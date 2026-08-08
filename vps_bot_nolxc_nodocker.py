import discord
from discord.ext import commands
import asyncio
import subprocess
import json
from datetime import datetime
import shlex
import logging
import shutil
import os
from typing import Optional, List, Dict, Any
import threading
import time
import sqlite3
import random
import requests
import re
import html
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
import secrets

# ─────────────────────────────────────────────────────────────────────────
# NO LXC, NO DOCKER DAEMON VERSION
# ─────────────────────────────────────────────────────────────────────────
# This backend assumes you have NEITHER LXD/LXC NOR a working Docker daemon
# (e.g. you're inside an unprivileged container/PaaS box like Railway that
# won't allow nested containerization, iptables NAT rules, or overlayfs
# mounts). The only thing that reliably still works there is plain Linux
# process/user isolation:
#
#   - Each "VPS" = one real Linux user account (`useradd`)
#   - An anchor process (`su - user -c "sleep infinity"`) keeps a live
#     session for that user so exec/tmate have something to attach to
#   - Resource limits are attempted via a delegated cgroup v2 path
#     (memory.max / cpu.max) - if that's not writable on your host, the
#     bot falls back to *tracking* the numbers only, with no hard
#     enforcement, and says so clearly in the VPS embed
#   - "SSH access" = tmate run as that user, same UX as before
#   - Port forwarding = a plain `socat` process forwarding
#     host_port -> 127.0.0.1:vps_port (no network namespace needed since
#     there's only one network stack now)
#   - Snapshot / clone / restore = tar / cp -a of the user's home directory
#
# IMPORTANT - THIS IS NOT A SECURE VPS PRODUCT:
#   All "VPS" users share one kernel, one process table, and one
#   filesystem root. A user can see (though usually not touch, thanks to
#   normal Unix permissions) that other users exist via `ps`/`w`/`who`.
#   There is no hard network isolation between VPS users either. Be
#   upfront with anyone you're hosting for that this is resource-limited
#   shell hosting, not an isolated VPS/container/VM.
# ─────────────────────────────────────────────────────────────────────────

DISCORD_TOKEN = os.getenv('DISCORD_TOKEN', '')
BOT_NAME = os.getenv('BOT_NAME', 'DevilClouds')
PREFIX = os.getenv('PREFIX', '!')
YOUR_SERVER_IP = os.getenv('YOUR_SERVER_IP', '127.0.0.1')
MAIN_ADMIN_ID = int(os.getenv('MAIN_ADMIN_ID', ''))
VPS_USER_ROLE_ID = int(os.getenv('VPS_USER_ROLE_ID', ''))
BOT_VERSION = os.getenv('BOT_VERSION', '2.0-PRO-MAX')
BOT_DEVELOPER = os.getenv('BOT_DEVELOPER', '')

VPS_HOME_ROOT = os.getenv('VPS_HOME_ROOT', '/home')
# Point this at your Railway Volume mount path (e.g. /data/vps.db) so VPS
# records survive redeploys. Left as 'vps.db' (cwd) it will be wiped along
# with everything else on every redeploy.
VPS_DB_PATH = os.getenv('VPS_DB_PATH', 'vps.db')
CGROUP_ROOT = os.getenv('CGROUP_ROOT', '/sys/fs/cgroup/vpsbot')
LOG_DIR = os.getenv('VPS_LOG_DIR', '/var/log/vpsbot')

# Web-terminal gateway (replaces tmate, which needs an outbound connection
# to a public relay server that platforms like Railway block). Instead,
# ttyd serves ONE web terminal on Railway's public port; a tiny gateway
# script prompts for a one-time code and drops the user into the right
# Linux user's shell if it matches. This only needs INBOUND traffic to
# Railway's public port, which Railway is built to support.
TTYD_PORT = int(os.getenv('PORT', os.getenv('TTYD_PORT', '8080')))
PUBLIC_URL = os.getenv('RAILWAY_PUBLIC_DOMAIN', '')  # auto-set by Railway when a public domain is attached
GATEWAY_SCRIPT_PATH = os.getenv('GATEWAY_SCRIPT_PATH', '/app/ssh_gateway.sh')
ACCESS_CODE_TTL_SECONDS = 600

# Admin web dashboard
DASHBOARD_PORT = int(os.getenv('DASHBOARD_PORT', '2026'))
DASHBOARD_USERNAME = os.getenv('DASHBOARD_USERNAME', 'admin')
DASHBOARD_PASSWORD = os.getenv('DASHBOARD_PASSWORD', '')
DASHBOARD_SECRET = os.getenv('DASHBOARD_SECRET', secrets.token_urlsafe(32))

# Whether cgroup-based resource limits actually work on this host. Detected
# once at startup in on_ready() / checked lazily; kept here so every part of
# the bot can report the same truth to users instead of guessing per-call.
CGROUPS_USABLE = {"value": False, "checked": False}

# "OS" selection no longer changes anything real (there's only one shared
# host OS/kernel) - kept purely as a label so the existing creation flow
# and DB schema don't need to change, and so it's visible in embeds that
# this is informational only.
OS_OPTIONS = [
    {"label": "Ubuntu 20.04 LTS (host OS - informational only)", "value": "ubuntu:20.04"},
    {"label": "Ubuntu 22.04 LTS (host OS - informational only)", "value": "ubuntu:22.04"},
    {"label": "Ubuntu 24.04 LTS (host OS - informational only)", "value": "ubuntu:24.04"},
    {"label": "Debian 10 (host OS - informational only)", "value": "debian:10"},
    {"label": "Debian 11 (host OS - informational only)", "value": "debian:11"},
    {"label": "Debian 12 (host OS - informational only)", "value": "debian:12"},
    {"label": "Debian 13 (host OS - informational only)", "value": "debian:13"},
]

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.FileHandler('bot.log'), logging.StreamHandler()]
)
logger = logging.getLogger(f'{BOT_NAME.lower()}_vps_bot')

# ─────────────────────────────────────────────────────────────────────────
# DATABASE
# ─────────────────────────────────────────────────────────────────────────
def get_db():
    conn = sqlite3.connect(VPS_DB_PATH)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    conn = get_db()
    cur = conn.cursor()
    cur.execute('''CREATE TABLE IF NOT EXISTS admins (user_id TEXT PRIMARY KEY)''')
    cur.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (str(MAIN_ADMIN_ID),))
    cur.execute('''CREATE TABLE IF NOT EXISTS nodes (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT UNIQUE NOT NULL, location TEXT, total_vps INTEGER, tags TEXT DEFAULT '[]',
        api_key TEXT, url TEXT, is_local INTEGER DEFAULT 0
    )''')
    cur.execute('SELECT COUNT(*) FROM nodes WHERE is_local = 1')
    if cur.fetchone()[0] == 0:
        cur.execute('INSERT INTO nodes (name, location, total_vps, tags, api_key, url, is_local) VALUES (?, ?, ?, ?, ?, ?, ?)',
                    ('Local Node', 'Local', 100, '[]', None, None, 1))
    cur.execute('''CREATE TABLE IF NOT EXISTS vps (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id TEXT NOT NULL, node_id INTEGER NOT NULL DEFAULT 1,
        container_name TEXT UNIQUE NOT NULL, ram TEXT NOT NULL, cpu TEXT NOT NULL, storage TEXT NOT NULL,
        config TEXT NOT NULL, os_version TEXT DEFAULT 'ubuntu:22.04', status TEXT DEFAULT 'stopped',
        suspended INTEGER DEFAULT 0, whitelisted INTEGER DEFAULT 0, created_at TEXT NOT NULL,
        shared_with TEXT DEFAULT '[]', suspension_history TEXT DEFAULT '[]', anchor_pid TEXT DEFAULT ''
    )''')
    cur.execute('PRAGMA table_info(vps)')
    columns = [col[1] for col in cur.fetchall()]
    if 'os_version' not in columns:
        cur.execute("ALTER TABLE vps ADD COLUMN os_version TEXT DEFAULT 'ubuntu:22.04'")
    if 'node_id' not in columns:
        cur.execute("ALTER TABLE vps ADD COLUMN node_id INTEGER DEFAULT 1")
    if 'anchor_pid' not in columns:
        cur.execute("ALTER TABLE vps ADD COLUMN anchor_pid TEXT DEFAULT ''")
    cur.execute('''CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL)''')
    for key, value in [('cpu_threshold', '90'), ('ram_threshold', '90')]:
        cur.execute('INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)', (key, value))
    cur.execute('''CREATE TABLE IF NOT EXISTS port_allocations (user_id TEXT PRIMARY KEY, allocated_ports INTEGER DEFAULT 0)''')
    cur.execute('''CREATE TABLE IF NOT EXISTS port_forwards (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id TEXT NOT NULL, vps_container TEXT NOT NULL,
        vps_port INTEGER NOT NULL, host_port INTEGER NOT NULL, created_at TEXT NOT NULL,
        tcp_pid TEXT DEFAULT '', udp_pid TEXT DEFAULT ''
    )''')
    cur.execute('PRAGMA table_info(port_forwards)')
    pf_columns = [col[1] for col in cur.fetchall()]
    if 'tcp_pid' not in pf_columns:
        cur.execute("ALTER TABLE port_forwards ADD COLUMN tcp_pid TEXT DEFAULT ''")
    if 'udp_pid' not in pf_columns:
        cur.execute("ALTER TABLE port_forwards ADD COLUMN udp_pid TEXT DEFAULT ''")
    cur.execute('''CREATE TABLE IF NOT EXISTS access_codes (
        code TEXT PRIMARY KEY, container_name TEXT NOT NULL, expires_at INTEGER NOT NULL
    )''')
    conn.commit()
    conn.close()

def get_setting(key: str, default: Any = None):
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT value FROM settings WHERE key = ?', (key,))
    row = cur.fetchone(); conn.close()
    return row[0] if row else default

def set_setting(key: str, value: str):
    conn = get_db(); cur = conn.cursor()
    cur.execute('INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)', (key, value))
    conn.commit(); conn.close()

def get_nodes() -> List[Dict]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT * FROM nodes'); rows = cur.fetchall(); conn.close()
    nodes = [dict(row) for row in rows]
    for node in nodes:
        node['tags'] = json.loads(node['tags'])
    return nodes

def get_node(node_id: int) -> Optional[Dict]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT * FROM nodes WHERE id = ?', (node_id,))
    row = cur.fetchone(); conn.close()
    if row:
        node = dict(row); node['tags'] = json.loads(node['tags']); return node
    return None

def get_current_vps_count(node_id: int) -> int:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT COUNT(*) FROM vps WHERE node_id = ?', (node_id,))
    count = cur.fetchone()[0]; conn.close()
    return count

def get_vps_data() -> Dict[str, List[Dict[str, Any]]]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT * FROM vps'); rows = cur.fetchall(); conn.close()
    data = {}
    for row in rows:
        user_id = row['user_id']
        if user_id not in data:
            data[user_id] = []
        vps = dict(row)
        vps['shared_with'] = json.loads(vps['shared_with'])
        vps['suspension_history'] = json.loads(vps['suspension_history'])
        vps['suspended'] = bool(vps['suspended'])
        vps['whitelisted'] = bool(vps['whitelisted'])
        vps['os_version'] = vps.get('os_version', 'ubuntu:22.04')
        data[user_id].append(vps)
    return data

def get_admins() -> List[str]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT user_id FROM admins'); rows = cur.fetchall(); conn.close()
    return [row['user_id'] for row in rows]

def save_vps_data():
    conn = get_db(); cur = conn.cursor()
    for user_id, vps_list in vps_data.items():
        for vps in vps_list:
            shared_json = json.dumps(vps['shared_with'])
            history_json = json.dumps(vps['suspension_history'])
            suspended_int = 1 if vps['suspended'] else 0
            whitelisted_int = 1 if vps.get('whitelisted', False) else 0
            os_ver = vps.get('os_version', 'ubuntu:22.04')
            created_at = vps.get('created_at', datetime.now().isoformat())
            node_id = vps.get('node_id', 1)
            anchor_pid = str(vps.get('anchor_pid', ''))
            if 'id' not in vps or vps['id'] is None:
                cur.execute('''INSERT INTO vps (user_id, node_id, container_name, ram, cpu, storage, config, os_version, status, suspended, whitelisted, created_at, shared_with, suspension_history, anchor_pid)
                               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                            (user_id, node_id, vps['container_name'], vps['ram'], vps['cpu'], vps['storage'], vps['config'],
                             os_ver, vps['status'], suspended_int, whitelisted_int, created_at, shared_json, history_json, anchor_pid))
                vps['id'] = cur.lastrowid
            else:
                cur.execute('''UPDATE vps SET user_id=?, node_id=?, container_name=?, ram=?, cpu=?, storage=?, config=?, os_version=?, status=?, suspended=?, whitelisted=?, shared_with=?, suspension_history=?, anchor_pid=?
                               WHERE id=?''',
                            (user_id, node_id, vps['container_name'], vps['ram'], vps['cpu'], vps['storage'], vps['config'],
                             os_ver, vps['status'], suspended_int, whitelisted_int, shared_json, history_json, anchor_pid, vps['id']))
    conn.commit(); conn.close()

def save_admin_data():
    conn = get_db(); cur = conn.cursor()
    cur.execute('DELETE FROM admins')
    for admin_id in admin_data['admins']:
        cur.execute('INSERT INTO admins (user_id) VALUES (?)', (admin_id,))
    conn.commit(); conn.close()

def get_user_allocation(user_id: str) -> int:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT allocated_ports FROM port_allocations WHERE user_id = ?', (user_id,))
    row = cur.fetchone(); conn.close()
    return row[0] if row else 0

def get_user_used_ports(user_id: str) -> int:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT COUNT(*) FROM port_forwards WHERE user_id = ?', (user_id,))
    row = cur.fetchone(); conn.close()
    return row[0]

def allocate_ports(user_id: str, amount: int):
    conn = get_db(); cur = conn.cursor()
    cur.execute('INSERT OR REPLACE INTO port_allocations (user_id, allocated_ports) VALUES (?, COALESCE((SELECT allocated_ports FROM port_allocations WHERE user_id = ?), 0) + ?)', (user_id, user_id, amount))
    conn.commit(); conn.close()

def deallocate_ports(user_id: str, amount: int):
    conn = get_db(); cur = conn.cursor()
    cur.execute('UPDATE port_allocations SET allocated_ports = MAX(0, allocated_ports - ?) WHERE user_id = ?', (amount, user_id))
    conn.commit(); conn.close()

def get_available_host_port(node_id: int) -> Optional[int]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT host_port FROM port_forwards WHERE vps_container IN (SELECT container_name FROM vps WHERE node_id = ?)', (node_id,))
    used_ports = set(row[0] for row in cur.fetchall())
    conn.close()
    for _ in range(100):
        port = random.randint(20000, 50000)
        if port not in used_ports:
            return port
    return None

def get_user_forwards(user_id: str) -> List[Dict]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT * FROM port_forwards WHERE user_id = ? ORDER BY created_at DESC', (user_id,))
    rows = cur.fetchall(); conn.close()
    return [dict(row) for row in rows]

def find_node_id_for_container(container_name: str) -> int:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT node_id FROM vps WHERE container_name = ?', (container_name,))
    row = cur.fetchone(); conn.close()
    return row[0] if row else 1

# ─────────────────────────────────────────────────────────────────────────
# HOST EXECUTION LAYER (replaces execute_lxc / execute_docker)
# ─────────────────────────────────────────────────────────────────────────
async def execute_host(container_name: str, shell_cmd: str, timeout=60, node_id: Optional[int] = None):
    """Runs an arbitrary shell command via `bash -c`, locally or against a
    remote node-agent. `container_name` is only used to resolve the node
    when node_id isn't given."""
    if node_id is None:
        node_id = find_node_id_for_container(container_name)
    node = get_node(node_id)
    if not node:
        raise Exception(f"Node {node_id} not found")

    if node['is_local']:
        try:
            proc = await asyncio.create_subprocess_exec(
                "bash", "-c", shell_cmd,
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            try:
                stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=timeout)
            except asyncio.TimeoutError:
                proc.kill(); await proc.wait()
                raise asyncio.TimeoutError(f"Command timed out after {timeout} seconds")
            if proc.returncode != 0:
                error = stderr.decode().strip() if stderr else "Command failed with no error output"
                raise Exception(f"Local command failed: {error}\nCommand: {shell_cmd}")
            return stdout.decode().strip() if stdout else True
        except asyncio.TimeoutError as te:
            logger.error(f"Command timed out: {shell_cmd} - {str(te)}")
            raise
        except Exception as e:
            logger.error(f"Host Error: {shell_cmd} - {str(e)}")
            raise
    else:
        # Remote node-agent must expose a shell-execution endpoint (not the
        # docker-flavoured one from earlier revisions of this bot).
        url = f"{node['url']}/api/execute_shell"
        data = {"shell": shell_cmd}
        params = {"api_key": node["api_key"]}
        try:
            response = requests.post(url, json=data, params=params, timeout=timeout)
            response.raise_for_status()
            res = response.json()
            if res.get("returncode", 1) != 0:
                raise Exception(f"Remote command failed on {node['name']}: {res.get('stderr', 'Command failed')}\nCommand: {shell_cmd}")
            return res.get("stdout", True)
        except requests.exceptions.RequestException as e:
            logger.error(f"Remote host error on node {node['name']} ({url}): {str(e)}")
            raise Exception(f"Remote execution failed on {node['name']}: {str(e)}")


async def detect_cgroups_usable(node_id: int = 1) -> bool:
    if CGROUPS_USABLE["checked"]:
        return CGROUPS_USABLE["value"]
    try:
        await execute_host("", f"mkdir -p {CGROUP_ROOT}/__probe__ && "
                               f"echo 10000000 > {CGROUP_ROOT}/__probe__/memory.max && "
                               f"rmdir {CGROUP_ROOT}/__probe__", node_id=node_id, timeout=15)
        CGROUPS_USABLE["value"] = True
    except Exception as e:
        logger.warning(f"cgroup delegation not usable on this host, falling back to no hard resource limits: {e}")
        CGROUPS_USABLE["value"] = False
    CGROUPS_USABLE["checked"] = True
    return CGROUPS_USABLE["value"]


def _home_dir(container_name: str) -> str:
    return f"{VPS_HOME_ROOT}/{container_name}"


async def ensure_prereqs(node_id: int):
    try:
        await execute_host("", f"mkdir -p {CGROUP_ROOT} {LOG_DIR}", node_id=node_id, timeout=15)
    except Exception as e:
        logger.error(f"Could not create bot dirs on node {node_id}: {e}")


_TTYD_STARTED = {"value": False}

async def ensure_ttyd_gateway_running(node_id: int = 1):
    """Start the shared ttyd web-terminal gateway once using a PID file."""
    if _TTYD_STARTED["value"]:
        return

    pidfile = "/tmp/execloud_ttyd_gateway.pid"
    logfile = f"{LOG_DIR}/ttyd_gateway.log"

    try:
        # Do not use pgrep -f here: the pgrep command can match its own
        # command line and falsely report that ttyd is already running.
        check_cmd = (
            f"if [ -f {pidfile} ] && kill -0 $(cat {pidfile}) 2>/dev/null; "
            f"then echo running; else echo stopped; fi"
        )
        status = await execute_host("", check_cmd, node_id=node_id, timeout=10)

        if str(status).strip() == "running":
            _TTYD_STARTED["value"] = True
            logger.info(f"ttyd gateway already running on port {TTYD_PORT}")
            return

        cmd = (
            f"mkdir -p {LOG_DIR} && "
            f"nohup ttyd -p {TTYD_PORT} -W bash {GATEWAY_SCRIPT_PATH} "
            f">{logfile} 2>&1 < /dev/null & "
            f"echo $! > {pidfile}"
        )
        await execute_host("", cmd, node_id=node_id, timeout=15)

        # Verify that the process actually survived startup.
        verify_cmd = (
            f"sleep 1; if [ -f {pidfile} ] && kill -0 $(cat {pidfile}) 2>/dev/null; "
            f"then echo running; else echo failed; fi"
        )
        verify = await execute_host("", verify_cmd, node_id=node_id, timeout=10)

        if str(verify).strip() != "running":
            logger.error(
                f"ttyd failed to start on port {TTYD_PORT}. "
                f"Check {logfile} on the node."
            )
            return

        pid = await execute_host("", f"cat {pidfile}", node_id=node_id, timeout=10)
        logger.info(
            f"Started ttyd web-terminal gateway on port {TTYD_PORT} "
            f"(pid {str(pid).strip()})"
        )
        _TTYD_STARTED["value"] = True

    except Exception as e:
        logger.error(f"Failed to start ttyd gateway: {e}")


def generate_access_code(container_name: str) -> str:
    code = ''.join(random.choices('abcdefghjkmnpqrstuvwxyz23456789', k=8))  # no ambiguous chars
    expires_at = int(time.time()) + ACCESS_CODE_TTL_SECONDS
    conn = get_db(); cur = conn.cursor()
    cur.execute('DELETE FROM access_codes WHERE container_name = ?', (container_name,))  # one active code per VPS
    cur.execute('INSERT INTO access_codes (code, container_name, expires_at) VALUES (?, ?, ?)', (code, container_name, expires_at))
    conn.commit(); conn.close()
    return code


def gateway_public_url() -> str:
    if PUBLIC_URL:
        return f"https://{PUBLIC_URL}"
    return f"http://<your-railway-public-domain>:{TTYD_PORT}  (set up a Public Domain for this service in Railway → Settings → Networking)"


async def create_vps_user(container_name: str, ram_mb: int, cpu_cores: int, node_id: int):
    home = _home_dir(container_name)
    await execute_host(container_name,
                        f"id -u {container_name} >/dev/null 2>&1 || useradd -m -d {home} -s /bin/bash {container_name}",
                        node_id=node_id)
    # Default password is "root" and the VPS user receives sudo privileges.
    try:
        password = os.getenv("VPS_DEFAULT_PASSWORD", "root")
        password_q = shlex.quote(container_name + ":" + password)
        await execute_host(
            container_name,
            f"printf '%s\n' {password_q} | chpasswd && usermod -aG sudo {shlex.quote(container_name)}",
            node_id=node_id
        )
    except Exception as e:
        logger.warning(f"Could not configure default password/sudo for {container_name}: {e}")
    if await detect_cgroups_usable(node_id):
        cg = f"{CGROUP_ROOT}/{container_name}"
        try:
            await execute_host(container_name, f"mkdir -p {cg}", node_id=node_id)
            await execute_host(container_name, f"echo {ram_mb * 1024 * 1024} > {cg}/memory.max", node_id=node_id)
            await execute_host(container_name, f"echo '{cpu_cores * 100000} 100000' > {cg}/cpu.max", node_id=node_id)
        except Exception as e:
            logger.warning(f"Could not apply cgroup limits for {container_name}: {e}")


async def start_anchor_process(container_name: str, node_id: int) -> str:
    cmd = f"setsid su - {container_name} -c 'exec sleep infinity' > {LOG_DIR}/{container_name}.log 2>&1 < /dev/null & echo $!"
    pid_out = await execute_host(container_name, cmd, node_id=node_id)
    pid = str(pid_out).strip().split()[-1]
    if await detect_cgroups_usable(node_id):
        cg = f"{CGROUP_ROOT}/{container_name}"
        try:
            await execute_host(container_name, f"echo {pid} > {cg}/cgroup.procs", node_id=node_id)
        except Exception as e:
            logger.warning(f"Could not attach {container_name} anchor pid to cgroup: {e}")
    return pid


async def is_vps_running(container_name: str, node_id: Optional[int] = None) -> bool:
    if node_id is None:
        node_id = find_node_id_for_container(container_name)
    try:
        out = await execute_host(container_name, f"pgrep -u {container_name} | head -1", node_id=node_id)
        return bool(str(out).strip())
    except Exception:
        return False


async def start_vps(container_name: str, node_id: int) -> str:
    if not await is_vps_running(container_name, node_id):
        return await start_anchor_process(container_name, node_id)
    return ""


async def stop_vps(container_name: str, node_id: int):
    await execute_host(container_name, f"pkill -9 -u {container_name} || true", node_id=node_id)


async def delete_vps_user(container_name: str, node_id: int):
    try:
        await execute_host(container_name, f"pkill -9 -u {container_name} || true", node_id=node_id)
    except Exception:
        pass
    try:
        await execute_host(container_name, f"userdel -r {container_name} 2>/dev/null || true", node_id=node_id)
    except Exception:
        pass
    try:
        await execute_host(container_name, f"rm -rf {CGROUP_ROOT}/{container_name} 2>/dev/null || true", node_id=node_id)
    except Exception:
        pass


async def exec_in_vps(container_name: str, cmd: str, node_id: Optional[int] = None, timeout=60):
    if node_id is None:
        node_id = find_node_id_for_container(container_name)
    escaped = cmd.replace('"', '\\"')
    return await execute_host(container_name, f'su - {container_name} -c "{escaped}"', node_id=node_id, timeout=timeout)


# ─────────────────────────────────────────────────────────────────────────
# PORT FORWARDING (plain socat, no network namespace needed)
# ─────────────────────────────────────────────────────────────────────────
async def create_port_forward(user_id: str, container: str, vps_port: int, node_id: int) -> Optional[int]:
    host_port = get_available_host_port(node_id)
    if not host_port:
        return None
    try:
        tcp_pid = str(await execute_host(container,
            f"nohup socat TCP4-LISTEN:{host_port},fork,reuseaddr TCP4:127.0.0.1:{vps_port} "
            f">{LOG_DIR}/proxy_tcp_{host_port}.log 2>&1 < /dev/null & echo $!", node_id=node_id)).strip()
        udp_pid = str(await execute_host(container,
            f"nohup socat UDP4-LISTEN:{host_port},fork,reuseaddr UDP4:127.0.0.1:{vps_port} "
            f">{LOG_DIR}/proxy_udp_{host_port}.log 2>&1 < /dev/null & echo $!", node_id=node_id)).strip()
        conn = get_db(); cur = conn.cursor()
        cur.execute('INSERT INTO port_forwards (user_id, vps_container, vps_port, host_port, created_at, tcp_pid, udp_pid) VALUES (?, ?, ?, ?, ?, ?, ?)',
                    (user_id, container, vps_port, host_port, datetime.now().isoformat(), tcp_pid, udp_pid))
        conn.commit(); conn.close()
        return host_port
    except Exception as e:
        logger.error(f"Failed to create port forward: {e}")
        return None

async def remove_port_forward(forward_id: int, is_admin: bool = False) -> tuple[bool, Optional[str]]:
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT user_id, vps_container, tcp_pid, udp_pid FROM port_forwards WHERE id = ?', (forward_id,))
    row = cur.fetchone()
    if not row:
        conn.close(); return False, None
    user_id, container, tcp_pid, udp_pid = row
    node_id = find_node_id_for_container(container)
    for pid in (tcp_pid, udp_pid):
        if pid:
            try:
                await execute_host(container, f"kill -9 {pid} 2>/dev/null || true", node_id=node_id)
            except Exception as e:
                logger.warning(f"Could not kill proxy pid {pid}: {e}")
    cur.execute('DELETE FROM port_forwards WHERE id = ?', (forward_id,))
    conn.commit(); conn.close()
    return True, user_id

async def recreate_port_forwards(container_name: str) -> int:
    """Restarts any proxy processes that aren't alive anymore."""
    node_id = find_node_id_for_container(container_name)
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT id, vps_port, host_port, tcp_pid, udp_pid FROM port_forwards WHERE vps_container = ?', (container_name,))
    rows = cur.fetchall()
    conn.close()
    fixed = 0
    for row in rows:
        fid, vps_port, host_port, tcp_pid, udp_pid = row
        need_tcp = True
        need_udp = True
        try:
            if tcp_pid:
                alive = await execute_host(container_name, f"kill -0 {tcp_pid} 2>/dev/null && echo alive || true", node_id=node_id)
                need_tcp = "alive" not in str(alive)
            if udp_pid:
                alive = await execute_host(container_name, f"kill -0 {udp_pid} 2>/dev/null && echo alive || true", node_id=node_id)
                need_udp = "alive" not in str(alive)
        except Exception:
            pass
        new_tcp_pid, new_udp_pid = tcp_pid, udp_pid
        try:
            if need_tcp:
                new_tcp_pid = str(await execute_host(container_name,
                    f"nohup socat TCP4-LISTEN:{host_port},fork,reuseaddr TCP4:127.0.0.1:{vps_port} "
                    f">{LOG_DIR}/proxy_tcp_{host_port}.log 2>&1 < /dev/null & echo $!", node_id=node_id)).strip()
            if need_udp:
                new_udp_pid = str(await execute_host(container_name,
                    f"nohup socat UDP4-LISTEN:{host_port},fork,reuseaddr UDP4:127.0.0.1:{vps_port} "
                    f">{LOG_DIR}/proxy_udp_{host_port}.log 2>&1 < /dev/null & echo $!", node_id=node_id)).strip()
            if need_tcp or need_udp:
                conn = get_db(); cur = conn.cursor()
                cur.execute('UPDATE port_forwards SET tcp_pid=?, udp_pid=? WHERE id=?', (new_tcp_pid, new_udp_pid, fid))
                conn.commit(); conn.close()
            fixed += 1
        except Exception as e:
            logger.error(f"Failed to ensure port forward host_port={host_port} for {container_name}: {e}")
    return fixed


# Initialize database
init_db()
vps_data = get_vps_data()
admin_data = {'admins': get_admins()}
CPU_THRESHOLD = int(get_setting('cpu_threshold', 90))
RAM_THRESHOLD = int(get_setting('ram_threshold', 90))

intents = discord.Intents.default()
intents.message_content = True
intents.members = True
bot = commands.Bot(command_prefix=PREFIX, intents=intents, help_command=None)
resource_monitor_active = True

def truncate_text(text, max_length=1024):
    if not text:
        return text
    if len(text) <= max_length:
        return text
    return text[:max_length-3] + "..."

def create_embed(title, description="", color=0x1a1a1a):
    embed = discord.Embed(title=truncate_text(f"🌟 {BOT_NAME} - {title}", 256),
                           description=truncate_text(description, 4096), color=color)
    embed.set_thumbnail(url="https://cdn.discordapp.com/attachments/1522275801297457203/1533016986068582460/5fe9ee50f1c0dd930c654ac7f5c3963e.webp?ex=6a782f53&is=6a76ddd3&hm=c92987356e84d2a2682fd1b89b2e87db74c0f95493f52df67534cd239574b050&")
    embed.set_footer(text=f"{BOT_NAME} VPS Manager v{BOT_VERSION} • {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                      icon_url="https://cdn.discordapp.com/attachments/1522275801297457203/1533016986068582460/5fe9ee50f1c0dd930c654ac7f5c3963e.webp?ex=6a782f53&is=6a76ddd3&hm=c92987356e84d2a2682fd1b89b2e87db74c0f95493f52df67534cd239574b050&")
    return embed

def add_field(embed, name, value, inline=False):
    embed.add_field(name=truncate_text(f"▸ {name}", 256), value=truncate_text(value, 1024), inline=inline)
    return embed

def create_success_embed(title, description=""): return create_embed(title, description, color=0x00ff88)
def create_error_embed(title, description=""): return create_embed(title, description, color=0xff3366)
def create_info_embed(title, description=""): return create_embed(title, description, color=0x00ccff)
def create_warning_embed(title, description=""): return create_embed(title, description, color=0xffaa00)

def is_admin():
    async def predicate(ctx):
        user_id = str(ctx.author.id)
        if user_id == str(MAIN_ADMIN_ID) or user_id in admin_data.get("admins", []):
            return True
        raise commands.CheckFailure("You need admin permissions to use this command. Contact support.")
    return commands.check(predicate)

def is_main_admin():
    async def predicate(ctx):
        if str(ctx.author.id) == str(MAIN_ADMIN_ID):
            return True
        raise commands.CheckFailure("Only the main admin can use this command.")
    return commands.check(predicate)

async def get_or_create_vps_role(guild):
    global VPS_USER_ROLE_ID
    me = guild.me
    if not me or not me.guild_permissions.manage_roles:
        return None
    role_name = f"{BOT_NAME} VPS User"
    if VPS_USER_ROLE_ID:
        role = guild.get_role(VPS_USER_ROLE_ID)
        if role and role < me.top_role:
            return role
        VPS_USER_ROLE_ID = None
    role = discord.utils.get(guild.roles, name=role_name)
    if role:
        if role >= me.top_role:
            try:
                await role.delete(reason="Role above bot, recreating")
            except discord.Forbidden:
                return None
            role = None
        else:
            VPS_USER_ROLE_ID = role.id
            return role
    try:
        role = await guild.create_role(name=role_name, color=discord.Color.dark_purple(),
                                        permissions=discord.Permissions.none(), reason=f"{BOT_NAME} VPS User role")
        await role.edit(position=me.top_role.position - 1)
        VPS_USER_ROLE_ID = role.id
        return role
    except Exception as e:
        logger.error(f"Failed to create VPS role: {e}")
        return None

def get_host_cpu_usage():
    try:
        if shutil.which("mpstat"):
            result = subprocess.run(['mpstat', '1', '1'], capture_output=True, text=True)
            for line in result.stdout.split('\n'):
                if 'all' in line and '%' in line:
                    return 100.0 - float(line.split()[-1])
        else:
            result = subprocess.run(['top', '-bn1'], capture_output=True, text=True)
            for line in result.stdout.split('\n'):
                if '%Cpu(s):' in line:
                    p = line.split()
                    return float(p[1]) + float(p[3]) + float(p[5]) + float(p[9]) + float(p[11]) + float(p[13]) + float(p[15])
        return 0.0
    except Exception as e:
        logger.error(f"Error getting CPU usage: {e}")
        return 0.0

def get_host_ram_usage():
    try:
        result = subprocess.run(['free', '-m'], capture_output=True, text=True)
        lines = result.stdout.splitlines()
        if len(lines) > 1:
            mem = lines[1].split()
            total = int(mem[1]); used = int(mem[2])
            return (used / total * 100) if total > 0 else 0.0
        return 0.0
    except Exception as e:
        logger.error(f"Error getting RAM usage: {e}")
        return 0.0

def get_host_disk_usage():
    try:
        result = subprocess.run(['df', '-h', '/'], capture_output=True, text=True)
        lines = result.stdout.splitlines()
        if len(lines) > 1:
            p = lines[1].split()
            return f"{p[2]}/{p[1]} ({p[4]})"
        return "Unknown"
    except Exception as e:
        logger.error(f"Error getting disk usage: {e}")
        return "Unknown"

async def get_host_stats(node_id: int) -> Dict:
    node = get_node(node_id)
    if node['is_local']:
        return {"cpu": get_host_cpu_usage(), "ram": get_host_ram_usage(), "disk": get_host_disk_usage()}
    url = f"{node['url']}/api/get_host_stats"
    try:
        response = requests.get(url, params={"api_key": node["api_key"]}, timeout=10)
        response.raise_for_status()
        stats = response.json(); stats['disk'] = stats.get('disk', 'Unknown')
        return stats
    except Exception as e:
        logger.error(f"Failed to get host stats from node {node['name']}: {e}")
        return {"cpu": 0.0, "ram": 0.0, "disk": "Unknown"}

def resource_monitor():
    global resource_monitor_active
    backup_interval = 3600
    last_backup = time.time()
    while resource_monitor_active:
        try:
            for node in get_nodes():
                stats = asyncio.run(get_host_stats(node['id']))
                logger.info(f"Node {node['name']}: CPU {stats['cpu']:.1f}%, RAM {stats['ram']:.1f}%")
                if stats['cpu'] > CPU_THRESHOLD or stats['ram'] > RAM_THRESHOLD:
                    logger.warning(f"Node {node['name']} exceeded thresholds. Manual intervention required.")
            if time.time() - last_backup > backup_interval:
                backup_name = f"vps_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
                try:
                    shutil.copy(VPS_DB_PATH, backup_name)
                    if os.path.exists(f'{VPS_DB_PATH}-wal'):
                        shutil.copy(f'{VPS_DB_PATH}-wal', f"{backup_name}-wal")
                    if os.path.exists(f'{VPS_DB_PATH}-shm'):
                        shutil.copy(f'{VPS_DB_PATH}-shm', f"{backup_name}-shm")
                    last_backup = time.time()
                except Exception as e:
                    logger.error(f"Failed to create DB backup: {e}")
            time.sleep(60)
        except Exception as e:
            logger.error(f"Error in resource monitor: {e}")
            time.sleep(60)

monitor_thread = threading.Thread(target=resource_monitor, daemon=True)
monitor_thread.start()

# ─────────────────────────────────────────────────────────────────────────
# PER-VPS STATS (ps/cgroup based instead of docker stats)
# ─────────────────────────────────────────────────────────────────────────
async def get_container_status_local(container_name: str):
    return "running" if await is_vps_running(container_name) else "stopped"

async def get_container_cpu_ram_local(container_name: str, ram_total_mb: int):
    try:
        out = await execute_host(container_name, f"ps -u {container_name} -o %cpu=,rss= --no-headers", node_id=find_node_id_for_container(container_name))
        cpu_total = 0.0; rss_total_kb = 0
        for line in str(out).splitlines():
            parts = line.split()
            if len(parts) >= 2:
                cpu_total += float(parts[0]); rss_total_kb += int(parts[1])
        used_mb = rss_total_kb / 1024
        pct = (used_mb / ram_total_mb * 100) if ram_total_mb > 0 else 0.0
        return cpu_total, {'used': int(used_mb), 'total': ram_total_mb, 'pct': pct}
    except Exception:
        return 0.0, {'used': 0, 'total': ram_total_mb, 'pct': 0.0}

async def get_container_disk_local(container_name: str):
    try:
        home = _home_dir(container_name)
        out = await execute_host(container_name, f"du -sh {home} 2>/dev/null | cut -f1", node_id=find_node_id_for_container(container_name))
        used = str(out).strip() or "Unknown"
        return f"{used} used (no hard quota enforced)"
    except Exception:
        return "Unknown"

async def get_container_uptime_local(container_name: str):
    try:
        out = await execute_host(container_name, f"ps -u {container_name} -o etimes= --no-headers | head -1", node_id=find_node_id_for_container(container_name))
        secs = int(str(out).strip() or 0)
        if secs <= 0:
            return "Not running"
        h, rem = divmod(secs, 3600); m, s = divmod(rem, 60)
        return f"{h}h {m}m {s}s"
    except Exception:
        return "Unknown"

async def get_container_stats(container_name: str, node_id: Optional[int] = None, ram_total_mb: int = 0) -> Dict:
    if node_id is None:
        node_id = find_node_id_for_container(container_name)
    node = get_node(node_id)
    if node['is_local']:
        status = await get_container_status_local(container_name)
        if status == "running":
            cpu, ram = await get_container_cpu_ram_local(container_name, ram_total_mb)
            disk = await get_container_disk_local(container_name)
            uptime = await get_container_uptime_local(container_name)
        else:
            cpu, ram, disk, uptime = 0.0, {'used': 0, 'total': ram_total_mb, 'pct': 0.0}, "Unknown", "Not running"
        return {"status": status, "cpu": cpu, "ram": ram, "disk": disk, "uptime": uptime}
    else:
        try:
            response = requests.post(f"{node['url']}/api/get_container_stats", json={"container": container_name},
                                      params={"api_key": node["api_key"]})
            response.raise_for_status()
            return response.json()
        except Exception as e:
            logger.error(f"Failed to get container stats from node {node['name']}: {e}")
            return {"status": "unknown", "cpu": 0.0, "ram": {"used": 0, "total": 0, "pct": 0.0}, "disk": "Unknown", "uptime": "Unknown"}

def get_uptime():
    try:
        return subprocess.run(['uptime'], capture_output=True, text=True).stdout.strip()
    except Exception:
        return "Unknown"

async def get_node_status(node_id: int) -> str:
    node = get_node(node_id)
    if not node:
        return "❓ Unknown"
    if node['is_local']:
        return "🟢 Online (Local)"
    try:
        response = requests.get(f"{node['url']}/api/ping", params={'api_key': node['api_key']}, timeout=5)
        return "🟢 Online" if response.status_code == 200 else "🔴 Offline"
    except Exception as e:
        logger.error(f"Failed to ping node {node['name']}: {e}")
        return "🔴 Offline"

async def recover_vps_after_redeploy():
    """On platforms like Railway, the container filesystem (and therefore
    /etc/passwd, running processes, and anything not on a mounted Volume)
    is wiped on every redeploy or restart. This re-creates the Linux user
    for every VPS still recorded in the DB, restarts its anchor process if
    it was supposed to be running, and re-establishes port forwards - so
    a redeploy degrades to "brief downtime + fresh home dirs" instead of
    "all VPS silently gone until an admin notices"."""
    recovered = 0
    failed = 0
    for user_id, vps_list in vps_data.items():
        for vps in vps_list:
            container_name = vps['container_name']
            node_id = vps.get('node_id', 1)
            try:
                exists = await execute_host(container_name, f"id -u {container_name} >/dev/null 2>&1 && echo yes || echo no", node_id=node_id)
                user_missing = "yes" not in str(exists)
                if user_missing:
                    ram_mb = int(vps['ram'].replace('GB', '')) * 1024
                    cpu = int(vps['cpu'])
                    await create_vps_user(container_name, ram_mb, cpu, node_id)
                    logger.warning(f"Recreated missing Linux user '{container_name}' after redeploy "
                                   f"(home directory contents are lost unless {VPS_HOME_ROOT} is on a persistent volume)")
                if vps.get('status') == 'running' and not vps.get('suspended', False):
                    pid = await start_anchor_process(container_name, node_id)
                    vps['anchor_pid'] = pid
                    await recreate_port_forwards(container_name)
                recovered += 1
            except Exception as e:
                failed += 1
                logger.error(f"Failed to recover VPS '{container_name}' after redeploy: {e}")
    save_vps_data()
    if recovered or failed:
        logger.info(f"Redeploy recovery: {recovered} VPS recovered, {failed} failed - check logs above for details")


# ─────────────────────────────────────────────────────────────────────────
# ADMIN WEB DASHBOARD (port 2026)
# ─────────────────────────────────────────────────────────────────────────
_DASHBOARD_SERVER = None
_DASHBOARD_SESSIONS = set()
_DASHBOARD_BANNED_IPS = set()


def _dashboard_cookie(token: str) -> str:
    return f"session={token}; Path=/; HttpOnly; SameSite=Strict"


def _dashboard_authenticated(handler) -> bool:
    if handler.client_address[0] in _DASHBOARD_BANNED_IPS:
        return False
    cookie = handler.headers.get("Cookie", "")
    return any(part.strip().startswith("session=") and part.strip().split("=", 1)[1] in _DASHBOARD_SESSIONS for part in cookie.split(";"))


def _dashboard_html(message=""):
    rows = []
    for owner_id, items in vps_data.items():
        for idx, vps in enumerate(items, 1):
            status = "SUSPENDED" if vps.get("suspended") else vps.get("status", "unknown").upper()
            name = html.escape(vps.get("container_name", "unknown"))
            rows.append(f"""
            <tr>
              <td>{html.escape(str(owner_id))}</td><td>{idx}</td><td><code>{name}</code></td>
              <td>{html.escape(status)}</td><td>{html.escape(vps.get('config','Custom'))}</td>
              <td>
                <form method='post' action='/action' style='display:inline'><input type='hidden' name='action' value='start'><input type='hidden' name='container' value='{html.escape(name)}'><button>Start</button></form>
                <form method='post' action='/action' style='display:inline'><input type='hidden' name='action' value='stop'><input type='hidden' name='container' value='{html.escape(name)}'><button>Stop</button></form>
                <form method='post' action='/action' style='display:inline'><input type='hidden' name='action' value='suspend'><input type='hidden' name='container' value='{html.escape(name)}'><button>Suspend</button></form>
                <form method='post' action='/action' style='display:inline'><input type='hidden' name='action' value='unsuspend'><input type='hidden' name='container' value='{html.escape(name)}'><button>Unsuspend</button></form>
                <form method='post' action='/action' style='display:inline' onsubmit="return confirm('Delete this VPS?')"><input type='hidden' name='action' value='delete'><input type='hidden' name='container' value='{html.escape(name)}'><button>Delete</button></form>
              </td>
            </tr>""")
    if not rows:
        rows.append("<tr><td colspan='6'>No VPS found.</td></tr>")
    return f"""<!doctype html><html><head><meta charset='utf-8'><title>{html.escape(BOT_NAME)} Dashboard</title>
    <style>body{{font-family:Arial;background:#111;color:#eee;margin:30px}}table{{width:100%;border-collapse:collapse}}td,th{{border:1px solid #444;padding:8px;text-align:left}}button{{margin:2px;padding:5px 8px}}a{{color:#8cf}}.msg{{padding:10px;background:#222;margin-bottom:15px}}</style></head>
    <body><h1>{html.escape(BOT_NAME)} Admin Dashboard</h1>{('<div class="msg">'+html.escape(message)+'</div>') if message else ''}
    <p>VPS: {sum(len(x) for x in vps_data.values())} | Users: {len(vps_data)} | <a href='/logout'>Logout</a></p>
    <table><tr><th>Owner ID</th><th>VPS</th><th>Account</th><th>Status</th><th>Resources</th><th>Actions</th></tr>{''.join(rows)}</table>
    </body></html>"""


class DashboardHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        logger.info("Dashboard %s - %s", self.address_string(), format % args)

    def _send(self, status, body, content_type='text/html; charset=utf-8', headers=None):
        data = body.encode('utf-8') if isinstance(body, str) else body
        self.send_response(status); self.send_header('Content-Type', content_type); self.send_header('Content-Length', str(len(data)))
        for k, v in (headers or {}).items(): self.send_header(k, v)
        self.end_headers(); self.wfile.write(data)

    def _redirect(self, path):
        self._send(303, '', headers={'Location': path})

    def _login_page(self, error=''):
        return f"""<!doctype html><html><head><meta charset='utf-8'><title>Admin Login</title></head><body style='font-family:Arial;background:#111;color:#eee;margin:40px'><h1>{html.escape(BOT_NAME)} Dashboard</h1><form method='post' action='/login'><input name='username' placeholder='Username' required><br><br><input type='password' name='password' placeholder='Password' required><br><br><button>Login</button></form><p>{html.escape(error)}</p></body></html>"""

    def do_GET(self):
        ip = self.client_address[0]
        if ip in _DASHBOARD_BANNED_IPS:
            return self._send(403, 'Forbidden')
        path = urlparse(self.path).path
        if path == '/login': return self._send(200, self._login_page())
        if path == '/logout':
            cookie = self.headers.get('Cookie', '')
            for part in cookie.split(';'):
                if part.strip().startswith('session='):
                    _DASHBOARD_SESSIONS.discard(part.strip().split('=', 1)[1])
            return self._redirect('/login')
        if not _dashboard_authenticated(self): return self._redirect('/login')
        if path == '/': return self._send(200, _dashboard_html())
        return self._send(404, 'Not found')

    def do_POST(self):
        ip = self.client_address[0]
        if ip in _DASHBOARD_BANNED_IPS: return self._send(403, 'Forbidden')
        length = int(self.headers.get('Content-Length', '0'))
        body = self.rfile.read(length).decode('utf-8', errors='replace')
        data = {k: v[0] for k, v in parse_qs(body).items()}
        path = urlparse(self.path).path
        if path == '/login':
            if secrets.compare_digest(data.get('username', ''), DASHBOARD_USERNAME) and DASHBOARD_PASSWORD and secrets.compare_digest(data.get('password', ''), DASHBOARD_PASSWORD):
                token = secrets.token_urlsafe(32); _DASHBOARD_SESSIONS.add(token)
                return self._send(303, '', headers={'Location': '/', 'Set-Cookie': _dashboard_cookie(token)})
            return self._send(401, self._login_page('Invalid credentials. Set DASHBOARD_PASSWORD in Railway Variables.'))
        if not _dashboard_authenticated(self): return self._redirect('/login')
        if path != '/action': return self._send(404, 'Not found')
        action, container = data.get('action', ''), data.get('container', '')
        if not container or not any(v.get('container_name') == container for items in vps_data.values() for v in items):
            return self._redirect('/')
        future = None
        if action == 'start': future = asyncio.run_coroutine_threadsafe(self._start(container), bot.loop)
        elif action == 'stop': future = asyncio.run_coroutine_threadsafe(self._stop(container), bot.loop)
        elif action == 'suspend': future = asyncio.run_coroutine_threadsafe(self._suspend(container), bot.loop)
        elif action == 'unsuspend': future = asyncio.run_coroutine_threadsafe(self._unsuspend(container), bot.loop)
        elif action == 'delete': future = asyncio.run_coroutine_threadsafe(self._delete(container), bot.loop)
        if future:
            try: future.result(timeout=60)
            except Exception as e: logger.error('Dashboard action failed: %s', e)
        return self._redirect('/')

    async def _find(self, container):
        for uid, items in vps_data.items():
            for vps in items:
                if vps.get('container_name') == container: return uid, vps
        return None, None

    async def _start(self, container):
        uid, vps = await self._find(container)
        if not vps: return
        pid = await start_vps(container, vps.get('node_id', 1)); vps['anchor_pid'] = pid or vps.get('anchor_pid', '')
        vps['status'] = 'running'; vps['suspended'] = False; save_vps_data()

    async def _stop(self, container):
        uid, vps = await self._find(container)
        if not vps: return
        await stop_vps(container, vps.get('node_id', 1)); vps['status'] = 'stopped'; save_vps_data()

    async def _suspend(self, container):
        uid, vps = await self._find(container)
        if not vps: return
        await stop_vps(container, vps.get('node_id', 1)); vps['status'] = 'stopped'; vps['suspended'] = True; save_vps_data()

    async def _unsuspend(self, container):
        uid, vps = await self._find(container)
        if not vps: return
        pid = await start_vps(container, vps.get('node_id', 1)); vps['anchor_pid'] = pid or vps.get('anchor_pid', '')
        vps['status'] = 'running'; vps['suspended'] = False; save_vps_data()

    async def _delete(self, container):
        uid, vps = await self._find(container)
        if not vps: return
        await delete_vps_user(container, vps.get('node_id', 1))
        conn = get_db(); cur = conn.cursor(); cur.execute('DELETE FROM vps WHERE container_name=?', (container,)); cur.execute('DELETE FROM port_forwards WHERE vps_container=?', (container,)); cur.execute('DELETE FROM access_codes WHERE container_name=?', (container,)); conn.commit(); conn.close()
        vps_data[uid] = [x for x in vps_data[uid] if x.get('container_name') != container]
        if not vps_data[uid]: del vps_data[uid]
        save_vps_data()


def start_dashboard_server():
    global _DASHBOARD_SERVER
    if _DASHBOARD_SERVER is not None: return
    if not DASHBOARD_PASSWORD:
        logger.warning('Dashboard disabled: DASHBOARD_PASSWORD is not set.')
        return
    try:
        _DASHBOARD_SERVER = ThreadingHTTPServer(('0.0.0.0', DASHBOARD_PORT), DashboardHandler)
        threading.Thread(target=_DASHBOARD_SERVER.serve_forever, name='dashboard-server', daemon=True).start()
        logger.info('Admin dashboard listening on port %s', DASHBOARD_PORT)
    except Exception as e:
        logger.error('Could not start admin dashboard on port %s: %s', DASHBOARD_PORT, e)

@bot.event
async def on_ready():
    logger.info(f'{bot.user} has connected to Discord!')
    start_dashboard_server()
    await bot.change_presence(activity=discord.Activity(type=discord.ActivityType.watching, name=f"{BOT_NAME} VPS Manager"))
    for node in get_nodes():
        try:
            await ensure_prereqs(node['id'])
            usable = await detect_cgroups_usable(node['id'])
            logger.info(f"Node {node['name']}: cgroup resource limits {'ENABLED' if usable else 'NOT AVAILABLE (tracking only)'}")
            if node['is_local']:
                await ensure_ttyd_gateway_running(node['id'])
        except Exception as e:
            logger.error(f"Prereq setup failed on node {node['id']}: {e}")
    try:
        await recover_vps_after_redeploy()
    except Exception as e:
        logger.error(f"Redeploy recovery pass failed: {e}")
    logger.info(f"{BOT_NAME} Bot is ready! (no-container / plain Linux-user backend)")

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    elif isinstance(error, commands.MissingRequiredArgument):
        await ctx.send(embed=create_error_embed("Missing Argument", "Please check command usage with `!help`."))
    elif isinstance(error, commands.BadArgument):
        await ctx.send(embed=create_error_embed("Invalid Argument", "Please check your input and try again."))
    elif isinstance(error, commands.CheckFailure):
        await ctx.send(embed=create_error_embed("Access Denied", str(error) or "You need admin permissions for this command."))
    elif isinstance(error, discord.NotFound):
        await ctx.send(embed=create_error_embed("Error", "The requested resource was not found. Please try again."))
    else:
        logger.error(f"Command error: {error}")
        await ctx.send(embed=create_error_embed("System Error", "An unexpected error occurred. Support has been notified."))

@bot.command(name='ping')
async def ping(ctx):
    await ctx.send(embed=create_success_embed("Pong!", f"{BOT_NAME} Bot latency: {round(bot.latency * 1000)}ms"))

@bot.command(name='uptime')
async def uptime(ctx):
    await ctx.send(embed=create_info_embed("Host Uptime", get_uptime()))

@bot.command(name='thresholds')
@is_admin()
async def thresholds(ctx):
    await ctx.send(embed=create_info_embed("Resource Thresholds", f"**CPU:** {CPU_THRESHOLD}%\n**RAM:** {RAM_THRESHOLD}%"))

@bot.command(name='set-threshold')
@is_admin()
async def set_threshold(ctx, cpu: int, ram: int):
    global CPU_THRESHOLD, RAM_THRESHOLD
    if cpu < 0 or ram < 0:
        await ctx.send(embed=create_error_embed("Invalid Thresholds", "Thresholds must be non-negative."))
        return
    CPU_THRESHOLD = cpu; RAM_THRESHOLD = ram
    set_setting('cpu_threshold', str(cpu)); set_setting('ram_threshold', str(ram))
    await ctx.send(embed=create_success_embed("Thresholds Updated", f"**CPU:** {cpu}%\n**RAM:** {ram}%"))

@bot.command(name='set-status')
@is_admin()
async def set_status(ctx, activity_type: str, *, name: str):
    types = {'playing': discord.ActivityType.playing, 'watching': discord.ActivityType.watching,
             'listening': discord.ActivityType.listening, 'streaming': discord.ActivityType.streaming}
    if activity_type.lower() not in types:
        await ctx.send(embed=create_error_embed("Invalid Type", "Valid types: playing, watching, listening, streaming"))
        return
    await bot.change_presence(activity=discord.Activity(type=types[activity_type.lower()], name=name))
    await ctx.send(embed=create_success_embed("Status Updated", f"Set to {activity_type}: {name}"))

@bot.command(name="myvps")
async def my_vps(ctx):
    user_id = str(ctx.author.id)
    vps_list = vps_data.get(user_id, [])
    if not vps_list:
        embed = create_error_embed("❌ No VPS Found", f"You don't have any **{BOT_NAME} VPS** yet.")
        embed.add_field(name="🚀 Quick Actions", value=f"• `{PREFIX}manage` – Manage VPS\n• Contact an admin to request a VPS", inline=False)
        await ctx.send(embed=embed)
        return
    embed = create_info_embed(title="🖥️ My VPS Dashboard", description="Your personal VPS overview (Linux-user backend - no hard isolation)")
    total_vps = len(vps_list); running = suspended = whitelisted = 0
    vps_cards = []
    for i, vps in enumerate(vps_list, start=1):
        node = get_node(vps.get("node_id"))
        node_name = node["name"] if node else "Unknown"
        config = vps.get("config", "Custom"); ram = vps.get("ram", "0GB"); cpu = vps.get("cpu", "0"); storage = vps.get("storage", "0GB")
        if vps.get("suspended"):
            status = "⛔ SUSPENDED"; suspended += 1
        elif vps.get("status") == "running":
            status = "🟢 RUNNING"; running += 1
        else:
            status = "🔴 STOPPED"
        if vps.get("whitelisted"):
            whitelisted += 1
        vps_cards.append(f"**{i}.** `{vps['container_name']}`\n{status} • `{config}`\n⚙️ `{ram}` RAM • `{cpu}` CPU • `{storage}` Disk\n📍 Node: `{node_name}`")
    embed.add_field(name="📊 Summary", value=f"🖥️ `{total_vps}` VPS\n🟢 `{running}` Running\n⛔ `{suspended}` Suspended\n✅ `{whitelisted}` Whitelisted", inline=True)
    embed.add_field(name="⚡ Quick Actions", value=f"`{PREFIX}manage`\n`{PREFIX}reinstall`\n`{PREFIX}status`", inline=True)
    embed.add_field(name="🧭 Tip", value="Use **manage** to control your VPS", inline=True)
    vps_text = "\n\n".join(vps_cards)
    for i in range(0, len(vps_text), 1024):
        embed.add_field(name="🖥️ Your VPS", value=vps_text[i:i + 1024], inline=False)
    embed.set_footer(text=f"{BOT_NAME} • Resource-limited shell hosting (not isolated VPS)")
    embed.timestamp = ctx.message.created_at
    await ctx.send(embed=embed)

class NodeSelectView(discord.ui.View):
    def __init__(self, ram: int, cpu: int, disk: int, user: discord.Member, ctx):
        super().__init__(timeout=300)
        self.ram = ram; self.cpu = cpu; self.disk = disk; self.user = user; self.ctx = ctx
        options = []
        for n in get_nodes():
            current_count = get_current_vps_count(n['id'])
            if current_count < n['total_vps']:
                options.append(discord.SelectOption(label=n['name'], value=str(n['id']),
                                                      description=f"{n['location']} - Available: {n['total_vps'] - current_count}"))
        if not options:
            self.add_item(discord.ui.Select(placeholder="No available nodes", disabled=True))
        else:
            self.select = discord.ui.Select(placeholder="Select a Node for the VPS", options=options)
            self.select.callback = self.select_node
            self.add_item(self.select)

    async def select_node(self, interaction: discord.Interaction):
        if str(interaction.user.id) != str(self.ctx.author.id):
            await interaction.response.send_message(embed=create_error_embed("Access Denied", "Only the command author can select."), ephemeral=True)
            return
        node_id = int(self.select.values[0])
        self.select.disabled = True
        await interaction.response.edit_message(view=self)
        os_view = OSSelectView(self.ram, self.cpu, self.disk, self.user, self.ctx, node_id)
        await interaction.followup.send(embed=create_info_embed("Select Label", "Choose a label for the VPS (informational only - see note)."), view=os_view)

class OSSelectView(discord.ui.View):
    def __init__(self, ram: int, cpu: int, disk: int, user: discord.Member, ctx, node_id: int):
        super().__init__(timeout=300)
        self.ram = ram; self.cpu = cpu; self.disk = disk; self.user = user; self.ctx = ctx; self.node_id = node_id
        self.select = discord.ui.Select(placeholder="Select a label for the VPS",
                                         options=[discord.SelectOption(label=o["label"], value=o["value"]) for o in OS_OPTIONS])
        self.select.callback = self.select_os
        self.add_item(self.select)

    async def select_os(self, interaction: discord.Interaction):
        if str(interaction.user.id) != str(self.ctx.author.id):
            await interaction.response.send_message(embed=create_error_embed("Access Denied", "Only the command author can select."), ephemeral=True)
            return
        os_version = self.select.values[0]
        self.select.disabled = True
        await interaction.response.edit_message(embed=create_info_embed("Creating VPS", f"Setting up VPS for {self.user.mention} on node {self.node_id}..."), view=self)
        user_id = str(self.user.id)
        if user_id not in vps_data:
            vps_data[user_id] = []
        vps_count = len(vps_data[user_id]) + 1
        container_name = f"{BOT_NAME.lower()}-vps-{user_id}-{vps_count}"
        ram_mb = self.ram * 1024
        try:
            await ensure_prereqs(self.node_id)
            await create_vps_user(container_name, ram_mb, self.cpu, self.node_id)
            pid = await start_anchor_process(container_name, self.node_id)
            await recreate_port_forwards(container_name)
            config_str = f"{self.ram}GB RAM / {self.cpu} CPU / {self.disk}GB Disk"
            vps_info = {
                "container_name": container_name, "node_id": self.node_id, "ram": f"{self.ram}GB", "cpu": str(self.cpu),
                "storage": f"{self.disk}GB", "config": config_str, "os_version": os_version, "status": "running",
                "suspended": False, "whitelisted": False, "suspension_history": [], "created_at": datetime.now().isoformat(),
                "shared_with": [], "id": None, "anchor_pid": pid
            }
            vps_data[user_id].append(vps_info)
            save_vps_data()
            if self.ctx.guild:
                vps_role = await get_or_create_vps_role(self.ctx.guild)
                if vps_role:
                    try:
                        await self.user.add_roles(vps_role, reason=f"{BOT_NAME} VPS ownership granted")
                    except discord.Forbidden:
                        logger.warning(f"Failed to assign VPS role to {self.user.name}")
            cgroup_note = "Enforced via cgroup v2" if CGROUPS_USABLE["value"] else "Tracked only - not enforced on this host"
            success_embed = create_success_embed("VPS Created Successfully")
            add_field(success_embed, "Owner", self.user.mention, True)
            add_field(success_embed, "VPS ID", f"#{vps_count}", True)
            add_field(success_embed, "Linux User", f"`{container_name}`", True)
            add_field(success_embed, "Node", get_node(self.node_id)['name'], True)
            add_field(success_embed, "Resources", f"**RAM:** {self.ram}GB\n**CPU:** {self.cpu} Cores\n**Storage:** {self.disk}GB\n**Limit enforcement:** {cgroup_note}", False)
            add_field(success_embed, "⚠️ Important", "This is a resource-limited shell account, not an isolated VPS/container. It shares the host kernel and filesystem with other VPS users.", False)
            await interaction.followup.send(embed=success_embed)
            dm_embed = create_success_embed("VPS Created!", "Your VPS shell account has been deployed by an admin!")
            add_field(dm_embed, "VPS Details", f"**VPS ID:** #{vps_count}\n**Account:** `{container_name}`\n**Configuration:** {config_str}\n**Status:** Running\n**Created:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", False)
            add_field(dm_embed, "Management", f"• Use `{PREFIX}manage` to start/stop your VPS\n• Use `{PREFIX}manage` → SSH for terminal access", False)
            try:
                await self.user.send(embed=dm_embed)
            except discord.Forbidden:
                await self.ctx.send(embed=create_info_embed("Notification Failed", f"Couldn't send DM to {self.user.mention}. Please ensure DMs are enabled."))
        except Exception as e:
            await interaction.followup.send(embed=create_error_embed("Creation Failed", f"Error: {str(e)}"))

@bot.command(name='changepwd')
async def change_password(ctx, vps_number: int, *, new_password: str):
    """Change the password of one of the caller's VPS users."""
    if len(new_password) < 4:
        await ctx.send(embed=create_error_embed("Password Too Short", "Password must be at least 4 characters long."))
        return

    user_vps = vps_data.get(str(ctx.author.id), [])
    if not user_vps:
        await ctx.send(embed=create_error_embed("No VPS Found", "You do not have any VPS accounts."))
        return
    if vps_number < 1 or vps_number > len(user_vps):
        await ctx.send(embed=create_error_embed("Invalid VPS", f"Choose a VPS number from 1 to {len(user_vps)}."))
        return

    vps = user_vps[vps_number - 1]
    username = vps['container_name']
    node_id = vps.get('node_id')
    try:
        # chpasswd receives the quoted username:password pair via stdin-like printf piping.
        pair = shlex.quote(username + ':' + new_password)
        await execute_host(
            username,
            f"printf '%s\n' {pair} | chpasswd && usermod -aG sudo {shlex.quote(username)}",
            node_id=node_id
        )
        await ctx.send(embed=create_success_embed(
            "Password Changed",
            f"Password changed for VPS #{vps_number}.\n\n`sudo su` is enabled for this VPS user."
        ))
    except Exception as e:
        logger.error(f"Password change failed for {username}: {e}")
        await ctx.send(embed=create_error_embed("Password Change Failed", str(e)[:500]))


@bot.command(name='create')
@is_admin()
async def create_vps(ctx, ram: int, cpu: int, disk: int, user: discord.Member):
    if ram <= 0 or cpu <= 0 or disk <= 0:
        await ctx.send(embed=create_error_embed("Invalid Specs", "RAM, CPU, and Disk must be positive integers."))
        return
    view = NodeSelectView(ram, cpu, disk, user, ctx)
    await ctx.send(embed=create_info_embed("VPS Creation", f"Creating VPS for {user.mention} with {ram}GB RAM, {cpu} CPU cores, {disk}GB Disk.\nSelect node below."), view=view)

class ManageView(discord.ui.View):
    def __init__(self, user_id, vps_list, is_shared=False, owner_id=None, is_admin=False, actual_index: Optional[int] = None):
        super().__init__(timeout=300)
        self.user_id = user_id; self.vps_list = vps_list[:]; self.selected_index = None
        self.is_shared = is_shared; self.owner_id = owner_id or user_id; self.is_admin = is_admin
        self.actual_index = actual_index; self.indices = list(range(len(vps_list)))
        if self.is_shared and self.actual_index is None:
            raise ValueError("actual_index required for shared views")
        if len(vps_list) > 1:
            options = [discord.SelectOption(label=f"VPS {i+1} ({v.get('config', 'Custom')})", description=f"Status: {v.get('status', 'unknown')}", value=str(i))
                       for i, v in enumerate(vps_list)]
            self.select = discord.ui.Select(placeholder="Select a VPS to manage", options=options)
            self.select.callback = self.select_vps
            self.add_item(self.select)
            self.initial_embed = create_embed("VPS Management", "Select a VPS from the dropdown menu below.", 0x1a1a1a)
            add_field(self.initial_embed, "Available VPS",
                      "\n".join([f"**VPS {i+1}:** `{v['container_name']}` - Status: `{v.get('status', 'unknown').upper()}`" for i, v in enumerate(vps_list)]), False)
        else:
            self.selected_index = 0; self.initial_embed = None; self.add_action_buttons()

    async def get_initial_embed(self):
        if self.initial_embed is not None:
            return self.initial_embed
        self.initial_embed = await self.create_vps_embed(self.selected_index)
        return self.initial_embed

    async def create_vps_embed(self, index):
        vps = self.vps_list[index]
        node = get_node(vps['node_id']); node_name = node['name'] if node else "Unknown"
        status = vps.get('status', 'unknown'); suspended = vps.get('suspended', False); whitelisted = vps.get('whitelisted', False)
        status_color = 0x00ff88 if status == 'running' and not suspended else 0xffaa00 if suspended else 0xff3366
        container_name = vps['container_name']
        ram_total_mb = int(vps['ram'].replace('GB', '')) * 1024
        stats = await get_container_stats(container_name, ram_total_mb=ram_total_mb)
        status_text = f"{stats['status'].upper()}"
        if suspended: status_text += " (SUSPENDED)"
        if whitelisted: status_text += " (WHITELISTED)"
        owner_text = ""
        if self.is_admin and self.owner_id != self.user_id:
            try:
                owner_user = await bot.fetch_user(int(self.owner_id))
                owner_text = f"\n**Owner:** {owner_user.mention}"
            except Exception:
                owner_text = f"\n**Owner ID:** {self.owner_id}"
        embed = create_embed(f"VPS Management - VPS {index + 1}", f"Managing account: `{container_name}` on node {node_name}{owner_text}", status_color)
        resource_info = (f"**Configuration:** {vps.get('config', 'Custom')}\n**Status:** `{status_text}`\n"
                          f"**RAM:** {vps['ram']}\n**CPU:** {vps['cpu']} Cores\n**Storage:** {vps['storage']}\n**Uptime:** {stats['uptime']}")
        add_field(embed, "📊 Allocated Resources", resource_info, False)
        if suspended:
            add_field(embed, "⚠️ Suspended", "This VPS is suspended. Contact an admin to unsuspend.", False)
        if whitelisted:
            add_field(embed, "✅ Whitelisted", "This VPS is exempt from auto-suspension.", False)
        add_field(embed, "📈 Live Usage", f"**CPU Usage:** {stats['cpu']:.1f}%\n**Memory:** {stats['ram']['used']}/{stats['ram']['total']} MB ({stats['ram']['pct']:.1f}%)\n**Disk:** {stats['disk']}", False)
        add_field(embed, "🎮 Controls", "Use the buttons below to manage your VPS", False)
        return embed

    def add_action_buttons(self):
        start_button = discord.ui.Button(label="▶ Start", style=discord.ButtonStyle.success)
        start_button.callback = lambda inter: self.action_callback(inter, 'start')
        stop_button = discord.ui.Button(label="⏸ Stop", style=discord.ButtonStyle.secondary)
        stop_button.callback = lambda inter: self.action_callback(inter, 'stop')
        ssh_button = discord.ui.Button(label="🔑 SSH", style=discord.ButtonStyle.primary)
        ssh_button.callback = lambda inter: self.action_callback(inter, 'tmate')
        stats_button = discord.ui.Button(label="📊 Stats", style=discord.ButtonStyle.secondary)
        stats_button.callback = lambda inter: self.action_callback(inter, 'stats')
        self.add_item(start_button); self.add_item(stop_button); self.add_item(ssh_button); self.add_item(stats_button)

    async def select_vps(self, interaction: discord.Interaction):
        if str(interaction.user.id) != self.user_id and not self.is_admin:
            await interaction.response.send_message(embed=create_error_embed("Access Denied", "This is not your VPS!"), ephemeral=True)
            return
        self.selected_index = int(self.select.values[0])
        await interaction.response.defer()
        new_embed = await self.create_vps_embed(self.selected_index)
        self.clear_items(); self.add_action_buttons()
        await interaction.edit_original_response(embed=new_embed, view=self)

    async def action_callback(self, interaction: discord.Interaction, action: str):
        if str(interaction.user.id) != self.user_id and not self.is_admin:
            await interaction.response.send_message(embed=create_error_embed("Access Denied", "This is not your VPS!"), ephemeral=True)
            return
        if self.selected_index is None:
            await interaction.response.send_message(embed=create_error_embed("No VPS Selected", "Please select a VPS first."), ephemeral=True)
            return
        actual_idx = self.actual_index if self.is_shared else self.indices[self.selected_index]
        target_vps = vps_data[self.owner_id][actual_idx]
        suspended = target_vps.get('suspended', False)
        if suspended and not self.is_admin and action != 'stats':
            await interaction.response.send_message(embed=create_error_embed("Access Denied", "This VPS is suspended. Contact an admin to unsuspend."), ephemeral=True)
            return
        container_name = target_vps["container_name"]; node_id = target_vps['node_id']
        ram_total_mb = int(target_vps['ram'].replace('GB', '')) * 1024

        if action == 'stats':
            stats = await get_container_stats(container_name, node_id, ram_total_mb)
            stats_embed = create_info_embed("📈 Live Statistics", f"Real-time stats for `{container_name}`")
            add_field(stats_embed, "Status", f"`{stats['status'].upper()}`", True)
            add_field(stats_embed, "CPU", f"{stats['cpu']:.1f}%", True)
            add_field(stats_embed, "Memory", f"{stats['ram']['used']}/{stats['ram']['total']} MB ({stats['ram']['pct']:.1f}%)", True)
            add_field(stats_embed, "Disk", stats['disk'], True)
            add_field(stats_embed, "Uptime", stats['uptime'], True)
            await interaction.response.send_message(embed=stats_embed, ephemeral=True)
            return

        await interaction.response.defer(ephemeral=True)
        if suspended:
            target_vps['suspended'] = False; save_vps_data()

        if action == 'start':
            try:
                pid = await start_vps(container_name, node_id)
                if pid:
                    target_vps['anchor_pid'] = pid
                target_vps["status"] = "running"; save_vps_data()
                fixed = await recreate_port_forwards(container_name)
                await interaction.followup.send(embed=create_success_embed("VPS Started", f"VPS `{container_name}` is now running! Verified {fixed} port forwards."), ephemeral=True)
            except Exception as e:
                await interaction.followup.send(embed=create_error_embed("Start Failed", str(e)), ephemeral=True)
        elif action == 'stop':
            try:
                await stop_vps(container_name, node_id)
                target_vps["status"] = "stopped"; save_vps_data()
                await interaction.followup.send(embed=create_success_embed("VPS Stopped", f"VPS `{container_name}` has been stopped!"), ephemeral=True)
            except Exception as e:
                await interaction.followup.send(embed=create_error_embed("Stop Failed", str(e)), ephemeral=True)
        elif action == 'tmate':
            if suspended:
                await interaction.followup.send(embed=create_error_embed("Access Denied", "Cannot access suspended VPS."), ephemeral=True)
                return
            try:
                await ensure_ttyd_gateway_running(node_id)
                code = generate_access_code(container_name)
                url = gateway_public_url()
                ssh_embed = create_embed("🔑 Web Terminal Access", "SSH doesn't work on this host (outbound connections are blocked), so this uses a browser-based terminal instead:", 0x00ff88)
                add_field(ssh_embed, "1. Open this URL", url, False)
                add_field(ssh_embed, "2. Enter this one-time code", f"```{code}```", False)
                add_field(ssh_embed, "⚠️ Security", f"This code expires in {ACCESS_CODE_TTL_SECONDS // 60} minutes and can only be used once. Do not share it.", False)
                try:
                    await interaction.user.send(embed=ssh_embed)
                    await interaction.followup.send(embed=create_success_embed("Access Code Sent", "Check your DMs for the web terminal link and code!"), ephemeral=True)
                except discord.Forbidden:
                    await interaction.followup.send(embed=ssh_embed, ephemeral=True)
            except Exception as e:
                await interaction.followup.send(embed=create_error_embed("Access Failed", str(e)), ephemeral=True)
        new_embed = await self.create_vps_embed(self.selected_index)
        await interaction.edit_original_response(embed=new_embed, view=self)

@bot.command(name='manage')
async def manage_vps(ctx, user: discord.Member = None):
    if user:
        if str(ctx.author.id) != str(MAIN_ADMIN_ID) and str(ctx.author.id) not in admin_data.get("admins", []):
            await ctx.send(embed=create_error_embed("Access Denied", "Only admins can manage other users' VPS."))
            return
        user_id = str(user.id); vps_list = vps_data.get(user_id, [])
        if not vps_list:
            await ctx.send(embed=create_error_embed("No VPS Found", f"{user.mention} doesn't have any {BOT_NAME} VPS."))
            return
        view = ManageView(str(ctx.author.id), vps_list, is_admin=True, owner_id=user_id)
        await ctx.send(embed=create_info_embed(f"Managing {user.name}'s VPS", f"Managing VPS for {user.mention}"), view=view)
    else:
        user_id = str(ctx.author.id); vps_list = vps_data.get(user_id, [])
        if not vps_list:
            embed = create_error_embed("No VPS Found", f"You don't have any {BOT_NAME} VPS. Contact an admin to create one.")
            add_field(embed, "Quick Actions", f"• `{PREFIX}manage` - Manage VPS\n• Contact admin for VPS creation", False)
            await ctx.send(embed=embed)
            return
        view = ManageView(user_id, vps_list)
        await ctx.send(embed=await view.get_initial_embed(), view=view)

@bot.command(name='manage-shared')
async def manage_shared_vps(ctx, owner: discord.Member, vps_number: int):
    owner_id = str(owner.id); user_id = str(ctx.author.id)
    if owner_id not in vps_data or vps_number < 1 or vps_number > len(vps_data[owner_id]):
        await ctx.send(embed=create_error_embed("Invalid VPS", "Invalid VPS number or owner doesn't have a VPS."))
        return
    vps = vps_data[owner_id][vps_number - 1]
    if user_id not in vps.get("shared_with", []):
        await ctx.send(embed=create_error_embed("Access Denied", "You do not have access to this VPS."))
        return
    view = ManageView(user_id, [vps], is_shared=True, owner_id=owner_id, actual_index=vps_number - 1)
    await ctx.send(embed=await view.get_initial_embed(), view=view)

@bot.command(name='share-user')
async def share_user(ctx, shared_user: discord.Member, vps_number: int):
    user_id = str(ctx.author.id); shared_user_id = str(shared_user.id)
    if user_id not in vps_data or vps_number < 1 or vps_number > len(vps_data[user_id]):
        await ctx.send(embed=create_error_embed("Invalid VPS", "Invalid VPS number or you don't have a VPS."))
        return
    vps = vps_data[user_id][vps_number - 1]
    vps.setdefault("shared_with", [])
    if shared_user_id in vps["shared_with"]:
        await ctx.send(embed=create_error_embed("Already Shared", f"{shared_user.mention} already has access to this VPS!"))
        return
    vps["shared_with"].append(shared_user_id); save_vps_data()
    await ctx.send(embed=create_success_embed("VPS Shared", f"VPS #{vps_number} shared with {shared_user.mention}!"))
    try:
        await shared_user.send(embed=create_embed("VPS Access Granted", f"You have access to VPS #{vps_number} from {ctx.author.mention}. Use `{PREFIX}manage-shared {ctx.author.mention} {vps_number}`", 0x00ff88))
    except discord.Forbidden:
        await ctx.send(embed=create_info_embed("Notification Failed", f"Could not DM {shared_user.mention}"))

@bot.command(name='share-ruser')
async def revoke_share(ctx, shared_user: discord.Member, vps_number: int):
    user_id = str(ctx.author.id); shared_user_id = str(shared_user.id)
    if user_id not in vps_data or vps_number < 1 or vps_number > len(vps_data[user_id]):
        await ctx.send(embed=create_error_embed("Invalid VPS", "Invalid VPS number or you don't have a VPS."))
        return
    vps = vps_data[user_id][vps_number - 1]
    vps.setdefault("shared_with", [])
    if shared_user_id not in vps["shared_with"]:
        await ctx.send(embed=create_error_embed("Not Shared", f"{shared_user.mention} doesn't have access to this VPS!"))
        return
    vps["shared_with"].remove(shared_user_id); save_vps_data()
    await ctx.send(embed=create_success_embed("Access Revoked", f"Access to VPS #{vps_number} revoked from {shared_user.mention}!"))
    try:
        await shared_user.send(embed=create_embed("VPS Access Revoked", f"Your access to VPS #{vps_number} by {ctx.author.mention} has been revoked.", 0xff3366))
    except discord.Forbidden:
        await ctx.send(embed=create_info_embed("Notification Failed", f"Could not DM {shared_user.mention}"))

@bot.command(name='ports-add-user')
@is_admin()
async def ports_add_user(ctx, amount: int, user: discord.Member):
    if amount <= 0:
        await ctx.send(embed=create_error_embed("Invalid Amount", "Amount must be a positive integer.")); return
    user_id = str(user.id); allocate_ports(user_id, amount)
    embed = create_success_embed("Ports Allocated", f"Allocated {amount} port slots to {user.mention}.")
    add_field(embed, "Quota", f"Total: {get_user_allocation(user_id)} slots", False)
    await ctx.send(embed=embed)
    try:
        await user.send(embed=create_info_embed("Port Slots Allocated", f"You have been granted {amount} additional port forwarding slots by an admin.\nUse `{PREFIX}ports list` to view your quota and active forwards."))
    except discord.Forbidden:
        await ctx.send(embed=create_info_embed("DM Failed", f"Could not notify {user.mention} via DM."))

@bot.command(name='ports-remove-user')
@is_admin()
async def ports_remove_user(ctx, amount: int, user: discord.Member):
    if amount <= 0:
        await ctx.send(embed=create_error_embed("Invalid Amount", "Amount must be a positive integer.")); return
    user_id = str(user.id); current = get_user_allocation(user_id)
    if amount > current: amount = current
    deallocate_ports(user_id, amount); remaining = get_user_allocation(user_id)
    embed = create_success_embed("Ports Deallocated", f"Removed {amount} port slots from {user.mention}.")
    add_field(embed, "Remaining Quota", f"{remaining} slots", False)
    await ctx.send(embed=embed)
    try:
        await user.send(embed=create_warning_embed("Port Slots Reduced", f"Your port forwarding quota has been reduced by {amount} slots by an admin.\nRemaining: {remaining} slots."))
    except discord.Forbidden:
        await ctx.send(embed=create_info_embed("DM Failed", f"Could not notify {user.mention} via DM."))

@bot.command(name='ports-revoke')
@is_admin()
async def ports_revoke(ctx, forward_id: int):
    success, user_id = await remove_port_forward(forward_id, is_admin=True)
    if success and user_id:
        try:
            user = await bot.fetch_user(int(user_id))
            await user.send(embed=create_warning_embed("Port Forward Revoked", f"One of your port forwards (ID: {forward_id}) has been revoked by an admin."))
        except Exception:
            pass
        await ctx.send(embed=create_success_embed("Revoked", f"Port forward ID {forward_id} revoked."))
    else:
        await ctx.send(embed=create_error_embed("Failed", "Port forward ID not found or removal failed."))

@bot.command(name='ports')
async def ports_command(ctx, subcmd: str = None, *args):
    user_id = str(ctx.author.id)
    allocated = get_user_allocation(user_id); used = get_user_used_ports(user_id); available = allocated - used
    if subcmd is None:
        embed = create_info_embed("Port Forwarding Help", f"**Your Quota:** Allocated: {allocated}, Used: {used}, Available: {available}")
        add_field(embed, "Commands", f"{PREFIX}ports add <vps_num> <port>\n{PREFIX}ports list\n{PREFIX}ports remove <id>", False)
        await ctx.send(embed=embed); return
    if subcmd == 'add':
        if len(args) < 2:
            await ctx.send(embed=create_error_embed("Usage", f"Usage: {PREFIX}ports add <vps_number> <vps_port>")); return
        try:
            vps_num = int(args[0]); vps_port = int(args[1])
            if vps_port < 1 or vps_port > 65535: raise ValueError
        except ValueError:
            await ctx.send(embed=create_error_embed("Invalid Input", "VPS number and port must be positive integers (port: 1-65535).")); return
        vps_list = vps_data.get(user_id, [])
        if vps_num < 1 or vps_num > len(vps_list):
            await ctx.send(embed=create_error_embed("Invalid VPS", f"Invalid VPS number (1-{len(vps_list)}). Use {PREFIX}myvps to list.")); return
        vps = vps_list[vps_num - 1]
        if used >= allocated:
            await ctx.send(embed=create_error_embed("Quota Exceeded", f"No available slots. Allocated: {allocated}, Used: {used}. Contact admin for more.")); return
        host_port = await create_port_forward(user_id, vps['container_name'], vps_port, vps['node_id'])
        if host_port:
            embed = create_success_embed("Port Forward Created", f"VPS #{vps_num} port {vps_port} (TCP/UDP) forwarded to host port {host_port}.")
            add_field(embed, "Access", f"External: {YOUR_SERVER_IP}:{host_port} → VPS:{vps_port} (TCP & UDP)", False)
            add_field(embed, "Quota Update", f"Used: {used + 1}/{allocated}", False)
            await ctx.send(embed=embed)
        else:
            await ctx.send(embed=create_error_embed("Failed", "Could not assign host port. Try again later."))
    elif subcmd == 'list':
        forwards = get_user_forwards(user_id)
        embed = create_info_embed("Your Port Forwards", f"**Quota:** Allocated: {allocated}, Used: {used}, Available: {available}")
        if not forwards:
            add_field(embed, "Forwards", "No active port forwards.", False)
        else:
            text = []
            for f in forwards:
                vps_num = next((i+1 for i, v in enumerate(vps_data.get(user_id, [])) if v['container_name'] == f['vps_container']), 'Unknown')
                created = datetime.fromisoformat(f['created_at']).strftime('%Y-%m-%d %H:%M')
                text.append(f"**ID {f['id']}** - VPS #{vps_num}: {f['vps_port']} (TCP/UDP) → {f['host_port']} (Created: {created})")
            add_field(embed, "Active Forwards", "\n".join(text[:10]), False)
            if len(forwards) > 10:
                add_field(embed, "Note", f"Showing 10 of {len(forwards)}. Remove unused with {PREFIX}ports remove <id>.")
        await ctx.send(embed=embed)
    elif subcmd == 'remove':
        if len(args) < 1:
            await ctx.send(embed=create_error_embed("Usage", f"Usage: {PREFIX}ports remove <forward_id>")); return
        try:
            fid = int(args[0])
        except ValueError:
            await ctx.send(embed=create_error_embed("Invalid ID", "Forward ID must be an integer.")); return
        success, _ = await remove_port_forward(fid)
        if success:
            embed = create_success_embed("Removed", f"Port forward {fid} removed (TCP & UDP).")
            add_field(embed, "Quota Update", f"Used: {used - 1}/{allocated}", False)
            await ctx.send(embed=embed)
        else:
            await ctx.send(embed=create_error_embed("Not Found", "Forward ID not found. Use !ports list."))
    else:
        await ctx.send(embed=create_error_embed("Invalid Subcommand", "Use: add <vps_num> <port>, list, remove <id>"))

@bot.command(name='delete-vps')
@is_admin()
async def delete_vps(ctx, user: discord.Member, vps_number: int, *, reason: str = "No reason"):
    user_id = str(user.id)
    if user_id not in vps_data or vps_number < 1 or vps_number > len(vps_data[user_id]):
        await ctx.send(embed=create_error_embed("Invalid VPS", "Invalid VPS number or user doesn't have that VPS.")); return
    vps = vps_data[user_id][vps_number - 1]
    container_name = vps["container_name"]; node_id = vps.get("node_id", 1)
    await ctx.send(embed=create_info_embed("Deleting VPS", f"Removing VPS #{vps_number} for {user.mention}..."))
    node_result = "Not checked"
    try:
        await delete_vps_user(container_name, node_id)
        node_result = "Linux user account removed successfully."
    except Exception as e:
        node_result = f"Removal failed: {e}"

    conn = get_db(); cur = conn.cursor()
    cur.execute("SELECT id, tcp_pid, udp_pid FROM port_forwards WHERE vps_container = ?", (container_name,))
    for fid, tcp_pid, udp_pid in cur.fetchall():
        for pid in (tcp_pid, udp_pid):
            if pid:
                try:
                    await execute_host(container_name, f"kill -9 {pid} 2>/dev/null || true", node_id=node_id)
                except Exception:
                    pass
    cur.execute("DELETE FROM vps WHERE container_name = ?", (container_name,))
    cur.execute("DELETE FROM port_forwards WHERE vps_container = ?", (container_name,))
    conn.commit(); conn.close()

    del vps_data[user_id][vps_number - 1]
    if not vps_data[user_id]:
        del vps_data[user_id]
        if ctx.guild:
            role = await get_or_create_vps_role(ctx.guild)
            if role and role in user.roles:
                try:
                    await user.remove_roles(role, reason="No VPS ownership")
                except discord.Forbidden:
                    logger.warning(f"Failed to remove VPS role from {user.name}")
    save_vps_data()

    embed = create_success_embed(f"🌟 {BOT_NAME} - VPS Deleted Successfully")
    add_field(embed, "Owner", user.mention, True)
    add_field(embed, "VPS Number", f"#{vps_number}", True)
    add_field(embed, "Account", container_name, False)
    add_field(embed, "Result", node_result, False)
    add_field(embed, "Reason", reason, False)
    await ctx.send(embed=embed)

@bot.command(name='add-resources')
@is_admin()
async def add_resources(ctx, vps_id: str, ram: int = None, cpu: int = None, disk: int = None):
    if ram is None and cpu is None and disk is None:
        await ctx.send(embed=create_error_embed("Missing Parameters", "Please specify at least one resource to add (ram, cpu, or disk)")); return
    found_vps = None; user_id = None; vps_index = None
    for uid, vps_list in vps_data.items():
        for i, vps in enumerate(vps_list):
            if vps['container_name'] == vps_id:
                found_vps = vps; user_id = uid; vps_index = i; break
        if found_vps: break
    if not found_vps:
        await ctx.send(embed=create_error_embed("VPS Not Found", f"No VPS found with ID: `{vps_id}`")); return
    node_id = found_vps['node_id']; changes = []
    try:
        new_ram_gb = int(found_vps['ram'].replace('GB', '')); new_cpu = int(found_vps['cpu']); new_disk_gb = int(found_vps['storage'].replace('GB', ''))
        if ram is not None and ram > 0:
            new_ram_gb += ram
            if await detect_cgroups_usable(node_id):
                try:
                    await execute_host(vps_id, f"echo {new_ram_gb * 1024 * 1024 * 1024} > {CGROUP_ROOT}/{vps_id}/memory.max", node_id=node_id)
                except Exception as e:
                    logger.warning(f"cgroup memory update failed: {e}")
            changes.append(f"RAM: +{ram}GB (New total: {new_ram_gb}GB)")
        if cpu is not None and cpu > 0:
            new_cpu += cpu
            if await detect_cgroups_usable(node_id):
                try:
                    await execute_host(vps_id, f"echo '{new_cpu * 100000} 100000' > {CGROUP_ROOT}/{vps_id}/cpu.max", node_id=node_id)
                except Exception as e:
                    logger.warning(f"cgroup cpu update failed: {e}")
            changes.append(f"CPU: +{cpu} cores (New total: {new_cpu} cores)")
        if disk is not None and disk > 0:
            new_disk_gb += disk
            changes.append(f"Disk: +{disk}GB (New total: {new_disk_gb}GB) [tracked only, no filesystem quota enforced]")
        found_vps['ram'] = f"{new_ram_gb}GB"; found_vps['cpu'] = str(new_cpu); found_vps['storage'] = f"{new_disk_gb}GB"
        found_vps['config'] = f"{new_ram_gb}GB RAM / {new_cpu} CPU / {new_disk_gb}GB Disk"
        vps_data[user_id][vps_index] = found_vps; save_vps_data()
        embed = create_success_embed("Resources Added", f"Successfully added resources to VPS `{vps_id}`")
        add_field(embed, "Changes Applied", "\n".join(changes), False)
        await ctx.send(embed=embed)
    except Exception as e:
        await ctx.send(embed=create_error_embed("Resource Addition Failed", f"Error: {str(e)}"))

@bot.command(name='restart-vps')
@is_admin()
async def restart_vps(ctx, container_name: str):
    node_id = find_node_id_for_container(container_name)
    await ctx.send(embed=create_info_embed("Restarting VPS", f"Restarting VPS `{container_name}`..."))
    try:
        await stop_vps(container_name, node_id)
        await asyncio.sleep(1)
        pid = await start_anchor_process(container_name, node_id)
        for user_id, vps_list in vps_data.items():
            for vps in vps_list:
                if vps['container_name'] == container_name:
                    vps['status'] = 'running'; vps['anchor_pid'] = pid; save_vps_data(); break
        await recreate_port_forwards(container_name)
        await ctx.send(embed=create_success_embed("VPS Restarted", f"VPS `{container_name}` has been restarted successfully!"))
    except Exception as e:
        await ctx.send(embed=create_error_embed("Restart Failed", f"Error: {str(e)}"))

@bot.command(name='exec')
@is_admin()
async def execute_command(ctx, container_name: str, *, command: str):
    node_id = find_node_id_for_container(container_name)
    await ctx.send(embed=create_info_embed("Executing Command", f"Running command in VPS `{container_name}`..."))
    try:
        output = await exec_in_vps(container_name, command, node_id)
        embed = create_embed(f"Command Output - {container_name}", f"Command: `{command}`", 0x1a1a1a)
        if output and str(output).strip():
            out = str(output)
            if len(out) > 1000: out = out[:1000] + "\n... (truncated)"
            add_field(embed, "📤 Output", f"```\n{out}\n```", False)
        await ctx.send(embed=embed)
    except Exception as e:
        await ctx.send(embed=create_error_embed("Execution Failed", f"Error: {str(e)}"))

@bot.command(name='suspend-vps')
@is_admin()
async def suspend_vps(ctx, container_name: str, *, reason: str = "Admin action"):
    node_id = find_node_id_for_container(container_name)
    found = False
    for uid, lst in vps_data.items():
        for vps in lst:
            if vps['container_name'] == container_name:
                if vps.get('status') != 'running':
                    await ctx.send(embed=create_error_embed("Cannot Suspend", "VPS must be running to suspend.")); return
                try:
                    await stop_vps(container_name, node_id)
                    vps['status'] = 'stopped'; vps['suspended'] = True
                    vps.setdefault('suspension_history', []).append({'time': datetime.now().isoformat(), 'reason': reason, 'by': f"{ctx.author.name} ({ctx.author.id})"})
                    save_vps_data()
                except Exception as e:
                    await ctx.send(embed=create_error_embed("Suspend Failed", str(e))); return
                try:
                    owner = await bot.fetch_user(int(uid))
                    await owner.send(embed=create_warning_embed("🚨 VPS Suspended", f"Your VPS `{container_name}` has been suspended by an admin.\n\n**Reason:** {reason}\n\nContact an admin to unsuspend."))
                except Exception as dm_e:
                    logger.error(f"Failed to DM owner {uid}: {dm_e}")
                await ctx.send(embed=create_success_embed("VPS Suspended", f"VPS `{container_name}` suspended. Reason: {reason}"))
                found = True; break
        if found: break
    if not found:
        await ctx.send(embed=create_error_embed("Not Found", f"VPS `{container_name}` not found."))

@bot.command(name='unsuspend-vps')
@is_admin()
async def unsuspend_vps(ctx, container_name: str):
    node_id = find_node_id_for_container(container_name)
    found = False
    for uid, lst in vps_data.items():
        for vps in lst:
            if vps['container_name'] == container_name:
                if not vps.get('suspended', False):
                    await ctx.send(embed=create_error_embed("Not Suspended", "VPS is not suspended.")); return
                try:
                    vps['suspended'] = False; vps['status'] = 'running'
                    pid = await start_anchor_process(container_name, node_id)
                    vps['anchor_pid'] = pid
                    await recreate_port_forwards(container_name)
                    save_vps_data()
                    await ctx.send(embed=create_success_embed("VPS Unsuspended", f"VPS `{container_name}` unsuspended and started."))
                    found = True
                except Exception as e:
                    await ctx.send(embed=create_error_embed("Start Failed", str(e)))
                try:
                    owner = await bot.fetch_user(int(uid))
                    await owner.send(embed=create_success_embed("🟢 VPS Unsuspended", f"Your VPS `{container_name}` has been unsuspended by an admin.\nYou can now manage it again."))
                except Exception as dm_e:
                    logger.error(f"Failed to DM owner {uid} about unsuspension: {dm_e}")
                break
        if found: break
    if not found:
        await ctx.send(embed=create_error_embed("Not Found", f"VPS `{container_name}` not found."))

@bot.command(name='whitelist-vps')
@is_admin()
async def whitelist_vps(ctx, container_name: str, action: str):
    if action.lower() not in ['add', 'remove']:
        await ctx.send(embed=create_error_embed("Invalid Action", f"Use: `{PREFIX}whitelist-vps <container> <add|remove>`")); return
    found = False
    for user_id, vps_list in vps_data.items():
        for vps in vps_list:
            if vps['container_name'] == container_name:
                vps['whitelisted'] = (action.lower() == 'add')
                save_vps_data()
                msg = "added to whitelist (exempt from auto-suspension)" if action.lower() == 'add' else "removed from whitelist"
                await ctx.send(embed=create_success_embed("Whitelist Updated", f"VPS `{container_name}` {msg}."))
                found = True; break
        if found: break
    if not found:
        await ctx.send(embed=create_error_embed("Not Found", f"VPS `{container_name}` not found."))

@bot.command(name='snapshot')
@is_admin()
async def snapshot_vps(ctx, container_name: str, snap_name: str = "snap0"):
    node_id = find_node_id_for_container(container_name)
    home = _home_dir(container_name)
    snap_dir = f"{VPS_HOME_ROOT}/.snapshots"
    snap_file = f"{snap_dir}/{container_name}__{snap_name}.tar.gz"
    await ctx.send(embed=create_info_embed("Creating Snapshot", f"Archiving home directory of `{container_name}` as '{snap_name}'..."))
    try:
        await execute_host(container_name, f"mkdir -p {snap_dir} && tar czf {snap_file} -C {home} .", node_id=node_id, timeout=300)
        await ctx.send(embed=create_success_embed("Snapshot Created", f"Snapshot '{snap_name}' saved to `{snap_file}`."))
    except Exception as e:
        await ctx.send(embed=create_error_embed("Snapshot Failed", f"Error: {str(e)}"))

@bot.command(name='list-snapshots')
@is_admin()
async def list_snapshots(ctx, container_name: str):
    node_id = find_node_id_for_container(container_name)
    snap_dir = f"{VPS_HOME_ROOT}/.snapshots"
    try:
        result = await execute_host(container_name, f"ls -1 {snap_dir} 2>/dev/null | grep '^{container_name}__' || true", node_id=node_id)
        text = str(result).strip() or "No snapshots found."
        await ctx.send(embed=create_info_embed(f"Snapshots for {container_name}", f"```{text}```"))
    except Exception as e:
        await ctx.send(embed=create_error_embed("List Failed", f"Error: {str(e)}"))

@bot.command(name='restore-snapshot')
@is_admin()
async def restore_snapshot(ctx, container_name: str, snap_name: str):
    node_id = find_node_id_for_container(container_name)
    home = _home_dir(container_name)
    snap_file = f"{VPS_HOME_ROOT}/.snapshots/{container_name}__{snap_name}.tar.gz"
    await ctx.send(embed=create_warning_embed("Restore Snapshot", f"Restoring snapshot '{snap_name}' for `{container_name}` will overwrite current home directory contents. Continue?"))

    class RestoreConfirm(discord.ui.View):
        def __init__(self):
            super().__init__(timeout=60)

        @discord.ui.button(label="Confirm Restore", style=discord.ButtonStyle.danger)
        async def confirm(self, inter: discord.Interaction, item: discord.ui.Button):
            await inter.response.defer()
            try:
                await stop_vps(container_name, node_id)
                await execute_host(container_name, f"find {home} -mindepth 1 -delete && tar xzf {snap_file} -C {home}", node_id=node_id, timeout=300)
                await execute_host(container_name, f"chown -R {container_name}:{container_name} {home}", node_id=node_id)
                pid = await start_anchor_process(container_name, node_id)
                await recreate_port_forwards(container_name)
                for uid, lst in vps_data.items():
                    for vps in lst:
                        if vps['container_name'] == container_name:
                            vps['status'] = 'running'; vps['suspended'] = False; vps['anchor_pid'] = pid; save_vps_data(); break
                await inter.followup.send(embed=create_success_embed("Snapshot Restored", f"Restored '{snap_name}' for VPS `{container_name}`."))
            except Exception as e:
                await inter.followup.send(embed=create_error_embed("Restore Failed", f"Error: {str(e)}"))

        @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
        async def cancel(self, inter: discord.Interaction, item: discord.ui.Button):
            await inter.response.edit_message(embed=create_info_embed("Cancelled", "Snapshot restore cancelled."))

    await ctx.send(view=RestoreConfirm())

@bot.command(name='clone-vps')
@is_admin()
async def clone_vps(ctx, container_name: str, new_name: str = None):
    if not new_name:
        new_name = f"{BOT_NAME.lower()}-{container_name}-clone-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
    node_id = find_node_id_for_container(container_name)
    await ctx.send(embed=create_info_embed("Cloning VPS", f"Cloning `{container_name}` to `{new_name}` (copying home directory)..."))
    try:
        found_vps = None; user_id = None
        for uid, vps_list in vps_data.items():
            for vps in vps_list:
                if vps['container_name'] == container_name:
                    found_vps = vps; user_id = uid; break
            if found_vps: break
        if not found_vps:
            await ctx.send(embed=create_error_embed("VPS Not Found", f"No VPS found with container name: `{container_name}`")); return

        ram_mb = int(found_vps['ram'].replace('GB', '')) * 1024
        cpu = int(found_vps['cpu'])
        await create_vps_user(new_name, ram_mb, cpu, node_id)
        old_home = _home_dir(container_name); new_home = _home_dir(new_name)
        await execute_host(new_name, f"rsync -a {old_home}/ {new_home}/ 2>/dev/null || cp -a {old_home}/. {new_home}/", node_id=node_id, timeout=300)
        await execute_host(new_name, f"chown -R {new_name}:{new_name} {new_home}", node_id=node_id)
        pid = await start_anchor_process(new_name, node_id)

        if user_id not in vps_data:
            vps_data[user_id] = []
        new_vps = found_vps.copy()
        new_vps.update({'container_name': new_name, 'status': 'running', 'suspended': False, 'whitelisted': False,
                         'suspension_history': [], 'created_at': datetime.now().isoformat(), 'shared_with': [], 'id': None, 'anchor_pid': pid})
        vps_data[user_id].append(new_vps)
        save_vps_data()
        embed = create_success_embed("VPS Cloned", f"Successfully cloned `{container_name}` to `{new_name}`")
        add_field(embed, "New VPS Details", f"**RAM:** {new_vps['ram']}\n**CPU:** {new_vps['cpu']} Cores\n**Storage:** {new_vps['storage']}", False)
        await ctx.send(embed=embed)
    except Exception as e:
        await ctx.send(embed=create_error_embed("Clone Failed", f"Error: {str(e)}"))

@bot.command(name='vps-stats')
@is_admin()
async def vps_stats(ctx, container_name: str):
    node_id = find_node_id_for_container(container_name)
    ram_total_mb = 0
    for lst in vps_data.values():
        for vps in lst:
            if vps['container_name'] == container_name:
                ram_total_mb = int(vps['ram'].replace('GB', '')) * 1024
    await ctx.send(embed=create_info_embed("Gathering Statistics", f"Collecting statistics for VPS `{container_name}`..."))
    try:
        stats = await get_container_stats(container_name, node_id, ram_total_mb)
        embed = create_embed(f"📊 VPS Statistics - {container_name}", "Resource usage statistics", 0x1a1a1a)
        add_field(embed, "📈 Status", f"**{stats['status'].upper()}**", False)
        add_field(embed, "💻 CPU Usage", f"**{stats['cpu']:.1f}%**", True)
        add_field(embed, "🧠 Memory Usage", f"**{stats['ram']['used']}/{stats['ram']['total']} MB ({stats['ram']['pct']:.1f}%)**", True)
        add_field(embed, "💾 Disk Usage", f"**{stats['disk']}**", True)
        add_field(embed, "⏱️ Uptime", f"**{stats['uptime']}**", True)
        await ctx.send(embed=embed)
    except Exception as e:
        await ctx.send(embed=create_error_embed("Statistics Failed", f"Error: {str(e)}"))

@bot.command(name='vps-processes')
@is_admin()
async def vps_processes(ctx, container_name: str):
    node_id = find_node_id_for_container(container_name)
    try:
        output = await execute_host(container_name, f"ps -u {container_name} -f", node_id=node_id)
        out = str(output)
        if len(out) > 1000: out = out[:1000] + "\n... (truncated)"
        embed = create_embed(f"⚙️ Processes - {container_name}", "Running processes for this VPS user", 0x1a1a1a)
        add_field(embed, "Process List", f"```\n{out}\n```", False)
        await ctx.send(embed=embed)
    except Exception as e:
        await ctx.send(embed=create_error_embed("Process Listing Failed", f"Error: {str(e)}"))

@bot.command(name='vps-uptime')
@is_admin()
async def vps_uptime(ctx, container_name: str):
    val = await get_container_uptime_local(container_name)
    await ctx.send(embed=create_info_embed("VPS Uptime", f"Uptime for `{container_name}`: {val}"))

@bot.command(name='vps-list')
@is_admin()
async def vps_list(ctx, node_id: int = 1):
    node = get_node(node_id)
    if not node:
        await ctx.send(embed=create_error_embed("Node Not Found", f"Node ID {node_id} not found.")); return
    status = await get_node_status(node_id); is_online = status.startswith("🟢")
    stats = await get_host_stats(node_id)
    if is_online:
        resources_text = (f"**CPU** {stats['cpu']:.0f}% {'█' * int(stats['cpu'] / 5) + '░' * (20 - int(stats['cpu'] / 5))}\n"
                           f"**RAM** {stats['ram']:.0f}% {'█' * int(stats['ram'] / 5) + '░' * (20 - int(stats['ram'] / 5))}\n"
                           f"**Disk** {stats['disk']}")
    else:
        resources_text = "⚠️ Resources unavailable (Offline)"
    current_vps = get_current_vps_count(node_id); total_capacity = node['total_vps']
    capacity_percent = (current_vps / total_capacity * 100) if total_capacity > 0 else 0
    conn = get_db(); cur = conn.cursor()
    cur.execute('SELECT * FROM vps WHERE node_id = ?', (node_id,)); rows = cur.fetchall(); conn.close()
    running = stopped = suspended = 0
    vps_info = []
    for i, row in enumerate(rows, 1):
        vps = dict(row)
        try:
            user = await bot.fetch_user(int(vps['user_id'])); username = user.name
        except Exception:
            username = f"Unknown ({vps['user_id']})"
        status_v = vps.get('status', 'unknown'); susp = vps.get('suspended', False)
        if susp: suspended += 1
        elif status_v == 'running': running += 1
        else: stopped += 1
        emoji = "🟢" if status_v == 'running' and not susp else "🟡" if susp else "🔴"
        vps_info.append(f"{emoji} **{i}.** {username} • `{vps['container_name']}`\n _{status_v.upper()}{' (SUSPENDED)' if susp else ''} | {vps.get('config', 'Custom')}_")
    embed = create_embed(title=f"🖥️ VPS Dashboard - {node['name']}",
                          description=f"**ID:** `{node_id}` | **Region:** {node['location']}\n*Updated: <t:{int(datetime.now().timestamp())}:R>*",
                          color=0x10b981 if is_online else 0xef4444)
    add_field(embed, "📡 **Status**", status, True)
    add_field(embed, "🗄️ **Capacity**", f"{current_vps}/{total_capacity} ({capacity_percent:.0f}%)", True)
    add_field(embed, "📊 **Resources**", resources_text, False)
    add_field(embed, "📈 **Summary**", f"**Total:** {len(rows)}\n**Running:** {running} 🟢\n**Stopped:** {stopped} ⏸️\n**Suspended:** {suspended} 🟡", True)
    if vps_info:
        add_field(embed, "📋 **Active VPS**", f"```{chr(10).join(vps_info[:10])}```", False)
    else:
        add_field(embed, "📋 **VPS List**", "No deployments yet. Launch one! 🚀", False)
    await ctx.send(embed=embed)

@bot.command(name='list-all')
@is_admin()
async def list_all_vps(ctx):
    total_vps = 0; total_users = len(vps_data)
    running_vps = stopped_vps = suspended_vps = whitelisted_vps = 0
    vps_info = []
    for user_id, vps_list in vps_data.items():
        try:
            user = await bot.fetch_user(int(user_id))
        except Exception:
            user = None
        for i, vps in enumerate(vps_list):
            total_vps += 1
            if vps.get('suspended', False): suspended_vps += 1
            elif vps.get('status') == 'running': running_vps += 1
            else: stopped_vps += 1
            if vps.get('whitelisted', False): whitelisted_vps += 1
            name = user.name if user else f"Unknown ({user_id})"
            emoji = "🟢" if vps.get('status') == 'running' and not vps.get('suspended', False) else "🟡" if vps.get('suspended', False) else "🔴"
            vps_info.append(f"{emoji} **{name}** - VPS {i+1}: `{vps['container_name']}` - {vps.get('config', 'Custom')}")
    embed = create_embed("All VPS Information", "Complete overview of all VPS deployments", 0x1a1a1a)
    add_field(embed, "System Overview", f"**Total Users:** {total_users}\n**Total VPS:** {total_vps}\n**Running:** {running_vps}\n**Stopped:** {stopped_vps}\n**Suspended:** {suspended_vps}\n**Whitelisted:** {whitelisted_vps}", False)
    await ctx.send(embed=embed)
    if vps_info:
        text = "\n".join(vps_info)
        for idx, chunk in enumerate([text[i:i+1024] for i in range(0, len(text), 1024)], 1):
            embed = create_embed(f"VPS Details (Part {idx})", "List of all VPS deployments", 0x1a1a1a)
            add_field(embed, "VPS List", chunk, False)
            await ctx.send(embed=embed)

@bot.command(name='userinfo')
@is_admin()
async def user_info(ctx, user: discord.Member):
    user_id = str(user.id); vps_list = vps_data.get(user_id, [])
    embed = create_embed(title="👤 User Dashboard", description=f"Statistics for {user.mention}", color=0x1A1A1A)
    embed.add_field(name="👤 User", value=f"**Name:** `{user.name}`\n**ID:** `{user.id}`", inline=True)
    embed.add_field(name="🖥️ VPS Count", value=f"`{len(vps_list)}` VPS", inline=True)
    if vps_list:
        lines = []
        for i, vps in enumerate(vps_list, start=1):
            lines.append(f"**{i}.** `{vps['container_name']}` - {vps.get('status', 'unknown').upper()} - {vps.get('config', 'Custom')}")
        embed.add_field(name="📋 VPS List", value="\n".join(lines)[:1024], inline=False)
    await ctx.send(embed=embed)

@bot.command(name='serverstats')
@is_admin()
async def server_stats(ctx):
    total_users = len(vps_data); total_vps = sum(len(v) for v in vps_data.values())
    embed = create_embed(title="📊 Server Statistics", description="**Live Infrastructure Dashboard**", color=0x1A1A1A)
    embed.add_field(name="👥 Users", value=f"`{total_users}` Users", inline=True)
    embed.add_field(name="🖥️ VPS", value=f"Total: `{total_vps}`", inline=True)
    embed.add_field(name="🔒 Isolation", value="Linux users only (no container/VM isolation)", inline=True)
    await ctx.send(embed=embed)

@bot.command(name='node-check')
@is_admin()
async def node_check(ctx, node_id: int):
    node = get_node(node_id)
    if not node:
        await ctx.send(embed=create_error_embed("Node Not Found", f"Node ID {node_id} not found.")); return
    embed = create_info_embed(f"Node Check - {node['name']}")
    status = await get_node_status(node_id)
    add_field(embed, "📡 Connection Status", status, False)
    if status.startswith("🟢"):
        usable = await detect_cgroups_usable(node_id)
        add_field(embed, "🧮 Resource Enforcement", "cgroup v2 delegation available ✅" if usable else "Not available - tracking only ⚠️", False)
        try:
            out = await execute_host("", "which useradd userdel su socat tmate", node_id=node_id)
            add_field(embed, "🛠️ Required Tools", f"```{out}```", False)
        except Exception as e:
            add_field(embed, "🛠️ Required Tools", f"Error checking: {str(e)[:200]}", False)
    await ctx.send(embed=embed)

@bot.command(name='backup-db')
@is_admin()
async def backup_db(ctx):
    backup_name = f"vps_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
    try:
        shutil.copy(VPS_DB_PATH, backup_name)
        if os.path.exists(f'{VPS_DB_PATH}-wal'): shutil.copy(f'{VPS_DB_PATH}-wal', f"{backup_name}-wal")
        if os.path.exists(f'{VPS_DB_PATH}-shm'): shutil.copy(f'{VPS_DB_PATH}-shm', f"{backup_name}-shm")
        await ctx.send(embed=create_success_embed("DB Backup Created", f"Backup saved as `{backup_name}`."))
    except Exception as e:
        await ctx.send(embed=create_error_embed("Backup Failed", f"Error: {str(e)}"))

@bot.command(name='repair-ports')
@is_admin()
async def repair_ports(ctx, container_name: str):
    await ctx.send(embed=create_info_embed("Repairing Ports", f"Checking/restarting port forward processes for `{container_name}`..."))
    try:
        fixed = await recreate_port_forwards(container_name)
        await ctx.send(embed=create_success_embed("Ports Repaired", f"Verified/restarted {fixed} port forwards for `{container_name}`."))
    except Exception as e:
        await ctx.send(embed=create_error_embed("Repair Failed", f"Error: {str(e)}"))

@bot.command(name='admin-add')
@is_main_admin()
async def admin_add(ctx, user: discord.Member):
    user_id = str(user.id)
    if user_id == str(MAIN_ADMIN_ID) or user_id in admin_data.get("admins", []):
        await ctx.send(embed=create_error_embed("Already Admin", "This user is already an admin!")); return
    admin_data["admins"].append(user_id); save_admin_data()
    await ctx.send(embed=create_success_embed("Admin Added", f"{user.mention} is now an admin!"))

@bot.command(name='admin-remove')
@is_main_admin()
async def admin_remove(ctx, user: discord.Member):
    user_id = str(user.id)
    if user_id == str(MAIN_ADMIN_ID):
        await ctx.send(embed=create_error_embed("Cannot Remove", "You cannot remove the main admin!")); return
    if user_id not in admin_data.get("admins", []):
        await ctx.send(embed=create_error_embed("Not Admin", f"{user.mention} is not an admin!")); return
    admin_data["admins"].remove(user_id); save_admin_data()
    await ctx.send(embed=create_success_embed("Admin Removed", f"{user.mention} is no longer an admin!"))

@bot.command(name='admin-list')
@is_main_admin()
async def admin_list(ctx):
    admins = admin_data.get("admins", [])
    main_admin = await bot.fetch_user(MAIN_ADMIN_ID)
    embed = create_embed("👑 Admin Team", "Current administrators:", 0x1a1a1a)
    add_field(embed, "🔰 Main Admin", f"{main_admin.mention} (ID: {MAIN_ADMIN_ID})", False)
    if admins:
        lines = []
        for aid in admins:
            try:
                u = await bot.fetch_user(int(aid)); lines.append(f"• {u.mention}")
            except Exception:
                lines.append(f"• Unknown ({aid})")
        add_field(embed, "🛡️ Admins", "\n".join(lines), False)
    await ctx.send(embed=embed)

@bot.command(name='about')
async def about(ctx):
    total_users = len(vps_data); total_vps = sum(len(v) for v in vps_data.values())
    main_admin = await bot.fetch_user(MAIN_ADMIN_ID)
    embed = create_info_embed(f"About {BOT_NAME}", "Bot information and statistics")
    add_field(embed, "Bot Name", BOT_NAME, True)
    add_field(embed, "Main Owner", main_admin.mention, True)
    add_field(embed, "Version", BOT_VERSION, True)
    add_field(embed, "Backend", "Plain Linux users (no LXC, no Docker)", False)
    add_field(embed, "Total VPS", str(total_vps), True)
    add_field(embed, "Total Users", str(total_users), True)
    await ctx.send(embed=embed)

@bot.command(name='help')
async def show_help(ctx):
    """Show every registered command automatically."""
    commands_list = sorted((c for c in bot.commands if c.name != 'help'), key=lambda c: c.qualified_name.lower())
    embed = create_info_embed("📚 Command Help", f"All registered {BOT_NAME} commands.")
    chunk = []
    fields = 0
    for command in commands_list:
        line = f"`{PREFIX}{command.qualified_name}`"
        if command.help:
            line += f" — {command.help.strip().splitlines()[0]}"
        if chunk and len('\n'.join(chunk + [line])) > 1000:
            add_field(embed, "📖 Commands" if fields == 0 else "📖 Commands (continued)", '\n'.join(chunk), False)
            fields += 1; chunk = []
        chunk.append(line)
    if chunk:
        add_field(embed, "📖 Commands" if fields == 0 else "📖 Commands (continued)", '\n'.join(chunk), False)
    add_field(embed, "⚠️ Reminder", "VPS here = a resource-limited Linux user account, not an isolated container/VM.", False)
    await ctx.send(embed=embed)

if __name__ == "__main__":
    if DISCORD_TOKEN:
        bot.run(DISCORD_TOKEN)
    else:
        logger.error("No Discord token found in DISCORD_TOKEN environment variable.")
