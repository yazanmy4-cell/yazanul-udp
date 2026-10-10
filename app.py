# -*- coding: utf-8 -*-
import sys
import os
os.environ['PYTHONUNBUFFERED'] = '1'
os.environ.setdefault('PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION', 'python')
try:
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
except Exception:
    pass
if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        if hasattr(sys.stderr, 'reconfigure'):
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

import asyncio
import httpx
import random
import json
import socket
import struct
import time
import uuid
import itertools
import math
import hmac
import hashlib
import codecs
import string as _string
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

try:
    from ReqAddBoT import send_friend_request_async
    _HAS_ADDFRIEND = True
except Exception:
    _HAS_ADDFRIEND = False
    send_friend_request_async = None

from dashboard import bot_state, start_web_dashboard

WEB_PORT = int(os.getenv("WEB_PORT", os.getenv("PORT", "8080")))

CS_START_INTERVAL = 0.5
CS_MATCH_REST = 60.0
CS_MAX_MATCH_DURATION = 700
CS_IDLE_TIMEOUT = 120.0
CS_NEW_MATCH_DELAY = 2.0
CS_MOVE_INTERVAL = 5.0
EXP_REFRESH_INTERVAL = 25.0
MODE_SWITCH_LEVEL = 2
REGION = "ME"
OB_VERSION = "OB55"

LW_START_INTERVAL = 3.0
LW_NEW_MATCH_DELAY = 3.0
LW_MAX_MATCH_DURATION = 700
LW_MATCH_IDLE_TIMEOUT = 15.0
LW_RECONNECT_DELAY = 1.0
LW_MAX_PARSE_FAILS = 5
LW_TOKEN_TTL = 1200

CLOUDFLARE_PRIMARY_DNS = "1.1.1.1"
CLOUDFLARE_SECONDARY_DNS = "1.0.0.1"
_DNS_CACHE: Dict[str, Tuple[str, float]] = {}
_DNS_CACHE_TTL = 300.0

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV = b'6oyZDr22E3ychjM%'

CRC7_TABLE = bytes([
    0, 9, 18, 27, 36, 45, 54, 63, 72, 65, 90, 83, 108, 101, 126, 119,
    25, 16, 11, 2, 61, 52, 47, 38, 81, 88, 67, 74, 117, 124, 103, 110,
    50, 59, 32, 41, 22, 31, 4, 13, 122, 115, 104, 97, 94, 87, 76, 69,
    43, 34, 57, 48, 15, 6, 29, 20, 99, 106, 113, 120, 71, 78, 85, 92,
    100, 109, 118, 127, 64, 73, 82, 91, 44, 37, 62, 55, 8, 1, 26, 19,
    125, 116, 111, 102, 89, 80, 75, 66, 53, 60, 39, 46, 17, 24, 3, 10,
    86, 95, 68, 77, 114, 123, 96, 105, 30, 23, 12, 5, 58, 51, 40, 33,
    79, 70, 93, 84, 107, 98, 121, 112, 7, 14, 21, 28, 35, 42, 49, 56,
    65, 72, 83, 90, 101, 108, 119, 126, 9, 0, 27, 18, 45, 36, 63, 54,
    88, 81, 74, 67, 124, 117, 110, 103, 16, 25, 2, 11, 52, 61, 38, 47,
    115, 122, 97, 104, 87, 94, 69, 76, 59, 50, 41, 32, 31, 22, 13, 4,
    106, 99, 120, 113, 78, 71, 92, 85, 34, 43, 48, 57, 6, 15, 20, 29,
    37, 44, 55, 62, 1, 8, 19, 26, 109, 100, 127, 118, 73, 64, 91, 82,
    60, 53, 46, 39, 24, 17, 10, 3, 116, 125, 102, 111, 80, 89, 66, 75,
    23, 30, 5, 12, 51, 58, 33, 40, 95, 86, 77, 68, 123, 114, 105, 96,
    14, 7, 28, 21, 42, 35, 56, 49, 70, 79, 84, 93, 98, 107, 112, 121,
])

_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0: 1, 1: 2, 2: 2, 3: 1, 4: 2}
_FIELD_NAMES = {0: "sendOption", 1: "cmd", 2: "orderId", 3: "flags", 4: "length"}

GEN_REGION_LANG = {
    "BD": "bn", "IND": "hi", "PK": "ur", "SG": "en", "ID": "id",
    "ME": "ar", "VN": "vi", "TW": "zh", "CIS": "ru", "TH": "th",
    "EU": "en", "US": "en", "SAC": "es", "LK": "en", "BR": "pt",
}

GEN_FIELD_TEMPLATE = bytes.fromhex(
    "474752450101010067020000a6a42db7bc5516876af3d1ba4adc337bac558af092eb3757d59d65c9323bba"
    "42c6593a48b74f33b2b5b3dc45cbd7ac02040db58f394045be4835213e12c35e5566445a5224f39d205f"
    "cf91c0e6bec797e7b3968ac00e90d7500b5865828a9d6f2091c3070f5319a130748e407ed57e66389746"
    "70ac045631b3d08c310cf1256cebcf1aed2d97d177534603d1c95d9c5d698340e797e72aa7ecc67a33122"
    "e48b0dfda050a1649586aca5e979be1fd9d99f48cd8cf59630e0ff60f67d4ed2ec4e5e7475970449a6c06"
    "329009ee0ce2567892587675781a31e4bb2774403b2f78e9811df2cb397fa602572266747704c625807791"
    "0902eb7420bcb4ab743d1610cddba9019e7867aaad3aa7ba9b04968064a409b66733f9f78c566a25ff478c"
    "ba37a2ffe23203d4b05bceef826f174b0be7912d19432cc759325251fa094d70693fb672d6f9e799284081"
    "b3adb541dd8f27ef80dcf1e7f0ff30f2fd976659457ce41e175a2d6301b777981ccc16b9a8247abaab8de"
    "0867836c27de0146fe4d0e1fd39b86ba51f0b58601cfcbd7f6f3451fe4184b26ed44ac2f6f7bb4ce5d9a8"
    "0f88c2cbfe7553e5ab97c8b028ae16b4f70f037753b8c229a6e5e9038fcbb9b4c2abb954894f8f2faf177"
    "bfdaab3b0ed537156633621d16b62d58ba4ebe518997c33e2304976ba6af9df7e7e34302c7910ae559c7e3d"
    "20a30d71c14f85c0e86f26291bbf18c2d9dfe9a908592eea4523e6c1e5d9bb5abfbebfccd5c4e136f9be77"
    "7723e932b06c029df5125191000c90fde62a8e5f8fceb28648f0c69ec3037d09302b2ade908a20dbd42761"
    "ca449b2743fc362649e16235769d9fbd7f87cd64972b58d69c0441abb5d22ddc6ed059f7ac1bdbfaef8c60"
    "e64631809c5e08c7cb4074c8ce6170d94b411604986be4ae163a"
)

client = httpx.AsyncClient(
    verify=False,
    timeout=15.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150)
)
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

headers = {
    'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)',
    'Connection': 'Keep-Alive',
    'Accept-Encoding': 'gzip',
    'Content-Type': 'application/x-www-form-urlencoded',
    'Expect': '100-continue',
    'X-Unity-Version': '2018.4.12f1',
    'X-GA-SV': '1789535859',
    'X-GA': 'v1 1',
    'ReleaseVersion': OB_VERSION,
}

_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()

_history_lock = asyncio.Lock()


def log(msg):
    print(msg, flush=True)
    try:
        bot_state.log(msg)
    except Exception:
        pass


def print_error(msg): log("[-] " + str(msg))
def print_success(msg): log("[+] " + str(msg))
def print_info(msg): log("[i] " + str(msg))
def print_warning(msg): log("[!] " + str(msg))


def get_proto_field(d, key, default=None):
    if not d or not isinstance(d, dict):
        return default
    if key in d:
        val = d[key].get('data')
        return val if val is not None else default
    if str(key) in d:
        val = d[str(key)].get('data')
        return val if val is not None else default
    return default


async def record_history(entry: Dict):
    async with _history_lock:
        try:
            bot_state.history.append(entry)
            bot_state.history = bot_state.history[-2000:]
        except Exception:
            pass


async def _inc_match(uid: str) -> int:
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]


async def _dec_match(uid: str) -> int:
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)


async def _get_match_count(uid: str) -> int:
    async with _match_counter_lock:
        return _match_counters.get(uid, 0)


async def aes_encrypt(payload, key, iv):
    cipher = AES.new(key, AES.MODE_CBC, iv)
    return cipher.encrypt(pad(payload, AES.block_size))


def optimize_tcp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        if hasattr(socket, "SIO_KEEPALIVE_VALS") and os.name == 'nt':
            try:
                sock.ioctl(socket.SIO_KEEPALIVE_VALS, (1, 10000, 2000))
            except Exception:
                pass
        elif hasattr(socket, "TCP_KEEPIDLE"):
            try:
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPIDLE, 10)
                if hasattr(socket, "TCP_KEEPINTVL"):
                    sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPINTVL, 2)
                if hasattr(socket, "TCP_KEEPCNT"):
                    sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_KEEPCNT, 5)
            except Exception:
                pass
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception:
        pass


async def safe_close_writer(writer):
    if not writer:
        return
    try:
        if not writer.is_closing():
            writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception:
        pass


def optimize_udp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
        if hasattr(socket, 'SIO_UDP_CONNRESET') and os.name == 'nt':
            try:
                sock.ioctl(socket.SIO_UDP_CONNRESET, False)
            except Exception:
                pass
    except Exception:
        pass


async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname:
        return hostname
    parts = hostname.split('.')
    if len(parts) == 4 and all(p.isdigit() and 0 <= int(p) <= 255 for p in parts):
        return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp:
            return ip

    def _query_cloudflare(server_ip):
        s = None
        try:
            tx_id = random.randint(1000, 65535)
            header = struct.pack(">HHHHHH", tx_id, 0x0100, 1, 0, 0, 0)
            qname = b"".join(bytes([len(part)]) + part.encode('ascii') for part in hostname.split('.')) + b"\x00"
            query_pkt = header + qname + struct.pack(">HH", 1, 1)
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.settimeout(1.2)
            s.sendto(query_pkt, (server_ip, 53))
            resp, _ = s.recvfrom(1024)
            if len(resp) >= 12:
                ancount = struct.unpack(">H", resp[6:8])[0]
                if ancount > 0:
                    offset = 12 + len(qname) + 4
                    for _ in range(ancount):
                        if offset >= len(resp):
                            break
                        if (resp[offset] & 0xC0) == 0xC0:
                            offset += 2
                        else:
                            while offset < len(resp) and resp[offset] != 0:
                                offset += 1 + resp[offset]
                            offset += 1
                        if offset + 10 > len(resp):
                            break
                        rtype, rclass, ttl, rdlen = struct.unpack(">HHIH", resp[offset:offset + 10])
                        offset += 10
                        if rtype == 1 and rdlen == 4 and offset + 4 <= len(resp):
                            return socket.inet_ntoa(resp[offset:offset + 4])
                        offset += rdlen
        except Exception:
            pass
        finally:
            if s:
                try:
                    s.close()
                except Exception:
                    pass
        return None

    loop = asyncio.get_running_loop()
    ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_PRIMARY_DNS)
    if not ip:
        ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_SECONDARY_DNS)
    if not ip:
        try:
            ip_info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
            if ip_info:
                ip = ip_info[0][4][0]
        except Exception:
            ip = hostname
    if ip:
        _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
    return ip or hostname


def _pb_varint(n):
    if n < 0:
        n = (1 << 64) + n
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


def _pb_tag(f, w):
    return _pb_varint((f << 3) | w)


def _pb_field(f, v):
    if isinstance(v, bool):
        v = int(v)
    if isinstance(v, int):
        return _pb_tag(f, 0) + _pb_varint(v)
    if isinstance(v, str):
        d = v.encode('utf-8')
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    if isinstance(v, (bytes, bytearray)):
        d = bytes(v)
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    return b""


def _pb_msg(f, inner):
    return _pb_tag(f, 2) + _pb_varint(len(inner)) + inner


def _gen_pb_field(f, v):
    if isinstance(v, bool):
        return _pb_tag(f, 0) + _pb_varint(1 if v else 0)
    if isinstance(v, int):
        return _pb_tag(f, 0) + _pb_varint(v)
    if isinstance(v, str):
        e = v.encode()
        return _pb_tag(f, 2) + _pb_varint(len(e)) + e
    if isinstance(v, (bytes, bytearray)):
        e = bytes(v)
        return _pb_tag(f, 2) + _pb_varint(len(e)) + e
    return b""


def _gen_build_proto(fields):
    return b"".join(_gen_pb_field(k, v) for k, v in fields.items())


def _gen_read_varint(b, o):
    v = 0
    s = 0
    while o < len(b):
        x = b[o]
        o += 1
        v |= (x & 0x7f) << s
        if not (x & 0x80):
            break
        s += 7
    return v, o


def _gen_parse(b):
    o = 0
    out = {}
    while o < len(b):
        t, o = _gen_read_varint(b, o)
        f, w = t >> 3, t & 7
        if w == 0:
            v, o = _gen_read_varint(b, o)
        elif w == 2:
            l, o = _gen_read_varint(b, o)
            v = b[o:o + l]
            o += l
        elif w == 5:
            v = b[o:o + 4]
            o += 4
        elif w == 1:
            v = b[o:o + 8]
            o += 8
        else:
            break
        out.setdefault(f, []).append(v)
    return out


def _gen_get(f, n):
    v = f.get(n)
    if v is None:
        return None
    if isinstance(v, list):
        v = v[0]
    return v


def _gen_enc_hex(hex_str):
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.backends import default_backend
    d = bytes.fromhex(hex_str)
    n = 16 - len(d) % 16
    d = d + bytes([n]) * n
    c = Cipher(
        algorithms.AES(AES_KEY),
        modes.CBC(AES_IV),
        backend=default_backend()
    ).encryptor()
    return (c.update(d) + c.finalize()).hex()


def _gen_pad(d):
    n = 16 - len(d) % 16
    return d + bytes([n]) * n


def _gen_hex_encrypt(hex_str):
    return _gen_enc_hex(hex_str)


def get_device_for_account(account_identifier: str) -> dict:
    device_list = [
        ("Samsung", "SM-G998B", "Adreno (TM) 660", "Android OS 12 / API-31"),
        ("Xiaomi", "2201122G", "Adreno (TM) 730", "Android OS 13 / API-33"),
        ("Realme", "RMX3700", "Mali-G710", "Android OS 14 / API-34"),
        ("OnePlus", "CPH2451", "Adreno (TM) 740", "Android OS 13 / API-33"),
        ("OPPO", "CPH2611", "Adreno (TM) 720", "Android OS 14 / API-34"),
        ("Vivo", "V2203", "Mali-G710", "Android OS 12 / API-31"),
        ("Poco", "M2102J20SG", "Adreno (TM) 660", "Android OS 13 / API-33"),
    ]
    brand, model, gpu, os_ver = random.choice(device_list)
    return {
        "unique_device_id": f"Google|{str(uuid.uuid4())}",
        "brand": brand,
        "model": model,
        "gpu_renderer": gpu,
        "system_software": os_ver,
        "screen_width": random.choice([1080, 1440, 720, 1280]),
        "screen_height": random.choice([2400, 3200, 1600, 2400]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
        "processor_details": f"ARM64 FP ASIMD AES VMH | {random.randint(2200, 3200)} | {random.randint(6, 12)}",
        "client_ip": f"{random.randint(103, 223)}.{random.randint(10, 250)}.{random.randint(10, 250)}.{random.randint(10, 250)}"
    }


async def get_playstore_version():
    loop = asyncio.get_event_loop()
    try:
        result = await loop.run_in_executor(
            None,
            lambda: play_scraper('com.dts.freefireth', lang='hi', country='id')
        )
        return result.get("version")
    except Exception:
        return "1.132.8"


async def version_config():
    app_version = await get_playstore_version()
    api_url = (
        "https://version.ggwhitehawk.com/live/ver.php"
        f"?version={app_version}"
        "&lang=hi&device=android&channel=android"
        f"&appstore=googleplay&region={REGION}"
        "&whitelist_version=1.3.0&whitelist_sp_version=1.0.0"
    )
    try:
        response = await client.get(api_url)
        response.raise_for_status()
        data = response.json()
        server_url = data.get("server_url")
        remote_version = data.get("remote_version")
        latest_release_version = data.get("latest_release_version")
        if not server_url or not remote_version or not latest_release_version:
            return None
        return latest_release_version, remote_version, server_url
    except Exception:
        return None


async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B Build/SP1A.210812.016)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "close"
    }
    data = {
        "uid": uid,
        "password": password,
        "response_type": "token",
        "client_type": "2",
        "client_secret": "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3",
        "client_id": "100067"
    }
    for attempt in range(5):
        try:
            response = await client.post(url, headers=hdrs, data=data)
            if response.status_code == 200:
                response_data = response.json()
                open_id = response_data.get("open_id")
                access_token = response_data.get("access_token")
                platform = response_data.get("platform", 4)
                if open_id and access_token:
                    return open_id, access_token, platform
            if response.status_code == 429:
                await asyncio.sleep(1)
                continue
        except Exception:
            pass
        await asyncio.sleep(0.5)
    return None


async def parse_results(parsed_results):
    result_dict = {}
    for result in parsed_results:
        field_data = {"wire_type": result.wire_type}
        if result.wire_type == "varint":
            field_data["data"] = result.data
        elif result.wire_type == "string":
            field_data["data"] = result.data
        elif result.wire_type == "bytes":
            field_data["data"] = result.data
        elif result.wire_type == "length_delimited":
            if hasattr(result.data, "results"):
                field_data["data"] = await parse_results(result.data.results)
            elif isinstance(result.data, list):
                field_data["data"] = await parse_results(result.data)
            else:
                field_data["data"] = str(result.data)
        result_dict[str(result.field)] = field_data
    return result_dict


async def decode_protobuf(data):
    parsed_results = Parser().parse(data)
    parsed_results_dict = await parse_results(parsed_results)
    return json.dumps(parsed_results_dict)


async def build_majorlogin_payload(open_id, access_token, platform, client_version, device_info):
    try:
        proto = thunderFF_pb2.MajorLoginReq()
        proto.event_time = str(datetime.now())[:-7]
        proto.game_name = "free fire"
        proto.platform_id = 1
        proto.client_version = str(client_version)
        proto.client_version_code = "2019121229"
        proto.system_software = "Android OS 15 / API-35 (AP3A.240905.015.A2/185014)"
        proto.system_hardware = "Handheld"
        proto.device_type = "Handheld"
        proto.screen_width = 1600
        proto.screen_height = 719
        proto.screen_dpi = "234"
        proto.processor_details = "ARM64 FP ASIMD AES | 1820 | 8"
        proto.memory = 2798
        proto.gpu_renderer = "Mali-G57"
        proto.gpu_version = "OpenGL ES 3.2 v1.r49p1-04eac0.2848c17a2fd4e9340e06555168eaa3c9"
        proto.unique_device_id = "Google|f744e396-5694-4e65-995d-97a958f2bd1f"
        proto.client_ip = "197.0.137.129"
        proto.language = "pt-br"
        proto.open_id = str(open_id)
        proto.open_id_type = "4"
        proto.login_open_id_type = 4
        proto.access_token = str(access_token)
        proto.login_by = 2
        proto.platform_sdk_id = 1
        proto.origin_platform_type = "4"
        proto.primary_platform_type = "4"
        proto.reg_avatar = 1
        proto.channel_type = 3
        proto.telecom_operator = "TUNTEL"
        proto.network_operator_a = "TUNTEL"
        proto.network_type = "WIFI"
        proto.network_type_a = "WIFI"
        proto.cpu_type = 2
        proto.cpu_architecture = "64"
        proto.graphics_api = "OpenGLES2"
        proto.supported_astc_bitset = 8191
        proto.client_using_version = "7428b253defc164018c604a1ebbfebdf"
        proto.loading_time = 15078
        proto.release_channel = "android"
        proto.extra_info = "KqsHTx3+QOmBRR1WKvaWewlcpqJBfjki+PPHQoQG8+0yV+Uos7gUFFjHMQ/e7u6han6Fl77r7c3vMN3p8UbKgN+nfycQCgwBmWgBzomx2gj84c+p"
        proto.android_engine_init_flag = 111207
        proto.if_push = 1
        proto.is_vpn = 0

        proto.memory_available.version = 55
        proto.memory_available.hidden_value = 81

        proto.external_storage_total = 49973
        proto.external_storage_available = 11338
        proto.internal_storage_total = 854
        proto.internal_storage_available = 11466
        proto.game_disk_storage_total = 49973
        proto.game_disk_storage_available = 11466
        proto.external_sdcard_total_storage = 49973
        proto.external_sdcard_avail_storage = 11466

        proto.library_path = "/data/app/~~lHFxTCCbupG2QVJmsURtZw==/com.dts.freefireth-N3aCHpHNXpdxjD80uIIbww==/lib/arm64"
        proto.library_token = "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~lHFxTCCbupG2QVJmsURtZw==/com.dts.freefireth-N3aCHpHNXpdxjD80uIIbww==/base.apk"

        base_payload = proto.SerializeToString()

        extra = b""
        extra += _pb_field(96, '{"cur_rate":[90,60,120],"support_etc2":false}')
        extra += _pb_field(97, 1)
        extra += _pb_field(99, "4")
        extra += _pb_field(100, "4")
        extra += _pb_field(102, b"\x17]ENWU\x0eR5")
        extra += _pb_field(104, 52882)
        extra += _pb_field(105, 1)
        extra += _pb_field(106, "https://dl.ak.freefiremobile.com/live/ABHotUpdates/|https://core-ak.freefiremobile.com/live/ABHotUpdates/|6b2078db9d22dd98f8e9386a39af8462")
        extra += _pb_field(107, "c8e41b7a93f02d56e1a94c7b8203f5d1")

        full_payload = base_payload + extra
        return await aes_encrypt(full_payload, AES_KEY, AES_IV)
    except Exception:
        return None


async def send_majorlogin(data, release_version, server_url):
    try:
        url = f"{server_url}MajorLogin" if server_url.endswith('/') else f"{server_url}/MajorLogin"
        req_headers = headers.copy()
        req_headers["ReleaseVersion"] = str(release_version)
        response = await client.post(url, headers=req_headers, data=data)
        if response.status_code != 200:
            return None
        response_content = response.content
        if len(response_content) < 40:
            return None

        res_proto = thunderFF_pb2.MajorLoginRes()
        try:
            res_proto.ParseFromString(response_content)
        except Exception:
            pass

        dict_res = {}
        try:
            parsed = Parser().parse(response_content.hex())
            dict_res = await parse_results(parsed)
        except Exception:
            pass

        key_val = get_proto_field(dict_res, 22)
        iv_val = get_proto_field(dict_res, 23)
        if not key_val:
            key_val = res_proto.aes_ak
        if not iv_val:
            iv_val = res_proto.iv_i
        if isinstance(key_val, str):
            try:
                key_val = bytes.fromhex(key_val)
            except Exception:
                pass
        if isinstance(iv_val, str):
            try:
                iv_val = bytes.fromhex(iv_val)
            except Exception:
                pass

        if not key_val or not iv_val:
            for offset in range(min(128, len(response_content))):
                try:
                    candidate = thunderFF_pb2.MajorLoginRes()
                    candidate.ParseFromString(response_content[offset:])
                    if candidate.region and candidate.token:
                        res_proto = candidate
                        break
                except Exception:
                    pass
            try:
                parsed = Parser().parse(response_content.hex())
                dict_res = await parse_results(parsed)
                kv = get_proto_field(dict_res, 22)
                ivv = get_proto_field(dict_res, 23)
                if isinstance(kv, str):
                    try:
                        kv = bytes.fromhex(kv)
                    except Exception:
                        pass
                if isinstance(ivv, str):
                    try:
                        ivv = bytes.fromhex(ivv)
                    except Exception:
                        pass
                if kv:
                    key_val = kv
                if ivv:
                    iv_val = ivv
            except Exception:
                pass

        if key_val:
            try:
                res_proto.aes_ak = key_val
            except Exception:
                pass
        if iv_val:
            try:
                res_proto.iv_i = iv_val
            except Exception:
                pass

        return res_proto
    except Exception as e:
        log(f"send_majorlogin error: {e}")
        return None


async def send_getlogin(data, base_url, token, release_version):
    try:
        url = f"{base_url.rstrip('/')}/GetLoginData"
        req_headers = headers.copy()
        req_headers["ReleaseVersion"] = release_version
        req_headers['Authorization'] = f"Bearer {token}"
        req_headers['Host'] = "clientbp.ppmainecoonghj.com"
        response = await client.post(url, headers=req_headers, data=data)
        if response.status_code != 200:
            return None
        response_content = response.content

        res_proto = thunderFF_pb2.GetLoginDataRes()
        try:
            res_proto.ParseFromString(response_content)
        except Exception:
            pass

        def _extract_addr(raw_bytes, field_no):
            try:
                pos = 0
                n = len(raw_bytes)
                def read_varint(buf, p):
                    res = 0
                    sh = 0
                    while p < len(buf):
                        b = buf[p]
                        p += 1
                        res |= (b & 0x7F) << sh
                        if not (b & 0x80):
                            break
                        sh += 7
                    return res, p
                fields = {}
                while pos < n:
                    try:
                        key, pos = read_varint(raw_bytes, pos)
                    except Exception:
                        break
                    fn = key >> 3
                    wt = key & 0x07
                    try:
                        if wt == 0:
                            val, pos = read_varint(raw_bytes, pos)
                        elif wt == 2:
                            ln, pos = read_varint(raw_bytes, pos)
                            val = raw_bytes[pos:pos + ln]
                            pos += ln
                        elif wt == 5:
                            val = raw_bytes[pos:pos + 4]
                            pos += 4
                        elif wt == 1:
                            val = raw_bytes[pos:pos + 8]
                            pos += 8
                        else:
                            break
                    except Exception:
                        break
                    fields.setdefault(fn, []).append(val)
                if field_no in fields:
                    v = fields[field_no][0]
                    if isinstance(v, bytes):
                        try:
                            return v.decode('utf-8', 'ignore')
                        except Exception:
                            return None
                    return str(v)
            except Exception:
                return None

        try:
            for offset in range(0, min(80, len(response_content))):
                fa = _extract_addr(response_content[offset:], 14)
                ia = _extract_addr(response_content[offset:], 32)
                if fa and ":" in fa and ia and ":" in ia:
                    res_proto.functional_addrs = fa
                    res_proto.informational_addrs = ia
                    break
        except Exception:
            pass

        dict_res = {}
        try:
            parsed = Parser().parse(response_content.hex())
            dict_res = await parse_results(parsed)
        except Exception:
            pass

        return res_proto, dict_res
    except Exception as e:
        log(f"send_getlogin error: {e}")
        return None


async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="ME", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    timestamp_hex = f"{int(server_time):08x}"
    encode_token = token.encode()
    encrypted_packet = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(encode_token, 16)).hex()
    encrypted_packet_length = f"{len(encrypted_packet) // 2:08x}"
    if typ == 'OnLine':
        return f"9015{uid_hex}{timestamp_hex}00000000{encrypted_packet_length}{encrypted_packet}"
    else:
        return f"9015{uid_hex}{timestamp_hex}{encrypted_packet_length}{encrypted_packet}"


async def send_keep_alive(region="ME"):
    try:
        reg = str(region).upper() if region else "ME"
        ka_hex = "0219" if reg == "ME" else ("0214" if reg == "IND" else "0215")
        return bytes.fromhex(ka_hex)
    except Exception:
        return bytes.fromhex("0219")


async def CS_Solo_Start_Matchmaking_Packet(key, iv, region="ME"):
    raw_proto_hex = (
        "080112960b0a0101100f3a0a0a04494443311a0242443a0a0a04494443321a0242443a0a0a0449444333"
        "1a02424440014a0901090a0b1219202729580162a70a0a80013038464241333342343332324443323230"
        "323033323030313232323130303031303038453030303330303841303032344235383634394234313330"
        "324437423434363736323531343030303130343037653061306438343830653734386333663661613034"
        "39643430303030303066663038306130353031636163666131366410c6011ab9037e585c541303054d51"
        "000b5c545102560057050309525a0852070853030057550101545600000b051204014f7d5c4045491a05"
        "1d04191009034c01567c77025a6842627e7a63494477675b79770e7708647b007c7c081302447b5d6351"
        "74567c4f7f677f76565074744c5a7b515c5a5b515063450812535f5d4c1e63791d754541044c646a6640"
        "014346504b594564134b7849470b6c7e7d5b466a1e46090d11040249085950785761007e7e45067e410f"
        "5e0066567e427f520502734b000c130a494502601c5362621e6a0b71426f5a405343795a49197b1a5a48"
        "40790c13034c197349517642174051597f5c6f4342435e5a030008644a05435c790e1b084c606973791e"
        "40646217505d687b484c7f707a185269057943400005081302004d0700640a007370405d714943584261"
        "057a6655016c70797c6a7f7c0c16034f701a015563610475431b015e0558670553401a5a037413771b66"
        "000f160549564a7f50477b697304606c0541696876046346561e464a047f74750c1300054d4477051350"
        "59437e5579435e65674a434500074a7b0240597c4f700d12054e5a4746597b5e5f5b704250405c1e6474"
        "5041537b61451a08616a440522047b5f5d5d300c3a1a1101404b4202020201041511647b7163746e7c5b"
        "57725d5550534207312e3133322e38480650015ab105036262535136334c707a475133416456324b796f"
        "566c6646484e4861775a57523441737574496d41506233706a4666667465554a722b7a58592b466f2f43"
        "2f58304b526636765a7631747943545a6e77314f7a307a7a554532636561556f61552b41483563492b42"
        "4a6d4234556d654b54776f4c34656569657a5345536c79332b6a627163486b4f4156456a4b2b634c4776"
        "3141652b68773749586f4e785137344d55716f544b4450557a4971564e584c4635337641775636706f68"
        "4c47345738387a5132627739466773496a564a4b6a48397538796e55354f51305746632f434b764c2b6b"
        "31617a2b6977576e34397044386c4b775253453846714b6d6c5061395963474e456b646d55562f55446d"
        "643045334d74516c353230567a332b4c55754765344b5136653148336f69466f5647615058417a4a7547"
        "4c6b62734a48412b537676504d4144416842676a502b364f6f49362b31445a594664644371736a675467"
        "62436c5674555a466156726a3130617377584b793674436550373535396757444b65586c617074536949"
        "5a73636d3376667051467165436252316c552f686639495163313634594d373553695a6765346979516c"
        "36514933434571556e754a4b426e635855523739303635654951624674377773546b6f6737384552786e"
        "6f4c484756392b59336662656d50316e4a3650385252394f673532587746706f3759646265556a685466"
        "6c4c4c6a415a782b4a696375694a2f685234652f676c7674553533585849374a37346254377067776137"
        "7054766a66514b696530516a79654b466f72794b6255354f46386771616a333464435961626933545470"
        "4339435838326f36653462742f704a4a4458643855796a6757393075692b695a56434c70394477526173"
        "7a6e7a567858654f37346174644138714956477943524239467145575a77384b755a536339593da20105"
        "080310e802a201050804108703a201050805109c01a20105081d10cc01a2010408161076a20105080e10"
        "8b01a201020815"
    )
    packet_bytes = bytes.fromhex(raw_proto_hex)
    encrypted_packet = (await aes_encrypt(packet_bytes, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = f"{packet_length:08x}"
    return bytes.fromhex('0315' + hex_length + encrypted_packet)


async def start_game_lone_wolf(region, client_version, writer, key, iv):
    packet = bytes.fromhex(
        "080112800a0a010b102b3a110a044944433110aa011a064555524f50453a100a044944433210311a06455552"
        "4f504540014a0801090a0b1219202758016291090a80013038384638324246303241393637363730323031"
        "30313030303030303030303030303030303031363030303130303135303030323232463937454545304630"
        "30303030303436373632353134303030303030303030303030303030303030303030303030303030303030"
        "3030303030303030303030303066663030303030303030636163666131366410241afb02735d5e57140002"
        "4a775d45414d1a041b1c001f11010449715f4243481a001e1d071c1703004b1a4066785c524570735c5148"
        "6775421b5c5a4c07504042685a63610816054e19025e75196001477c015165406370195f5547404e455064"
        "0103020f1304064863754268676c755f65576e40467e5f0a417a4701026d675d6e73670b1108495a4c6a0b"
        "78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b625f7d04055a47505c4e1d"
        "6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d615f795352567809"
        "11030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e5078487e7a"
        "7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b441b46"
        "0776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c"
        "57047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a1673050671"
        "62727516134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f56"
        "6c636f477776484f624e56526c4d727073504b4f4365417761684849417679555649727374375273714973"
        "4a7a786b3247525268377a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b5348"
        "6833447955726f39515152756c34545350626d6d624b7949565937545671577059455372323646572f5962"
        "4578507338514f706d317372785455736c30796a434144444d4f34616a654b615753366361496c554b4963"
        "797a494e396d52516f715277687939797257476d337a644345337a6a61436f492f5a585233656f65365a42"
        "647a64677654636b6b665733356e4d4c6a6a565072564b6433523172756174394e50514150724a554662"
        "7859696c4c5a3859707336654d5447666b6649793574666a526c314d4648706b51774c6373374439656378"
        "566c41636f374e664f6d2b30654756466c4434744478706771385533595973587645384842502f70666c76"
        "7a737138316a32524f4d7857437556445442492f684735625462773166456e4249725162762b6361447751"
        "47696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78704743334c304a53"
        "44532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f583932414c"
        "572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f5255513035"
        "78754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d74"
        "757077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803"
        "108703a201050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a2"
        "01020815"
    )
    proto = thunderFF_pb2.StartMatch()
    proto.ParseFromString(packet)
    if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
        proto.main.region_list[0].region = region
        if len(proto.main.region_list) > 1:
            proto.main.region_list[1].region = region
    if hasattr(proto.main, 'client_version'):
        proto.main.client_version.remote_version = client_version
    packet = proto.SerializeToString()
    encrypted_packet = (await aes_encrypt(packet, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = hex(packet_length)[2:]
    hex_length = hex_length if len(hex_length) > 1 else "0" + hex_length
    reg = str(region).upper() if region else "ME"
    reg_prefix = "031400" if reg == "ME" else ("031400" if reg == "IND" else "031500")
    final_packet = reg_prefix + "0" * (6 - len(hex_length)) + hex_length + encrypted_packet
    writer.write(bytes.fromhex(final_packet))
    await writer.drain()
    log(f"[LW] Match search sent ({packet_length} bytes) | Region: {reg}")


async def has_ssan_zig(n):
    z = (n << 1) & 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while z >= 0x80:
        out.append((z & 0x7F) | 0x80)
        z >>= 7
    out.append(z)
    return bytes(out)


async def uleb_encode(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^
                      ((v1 + s) & 0xFFFFFFFF) ^
                      (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v1 = (v1 + (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^
                      ((v0 + s) & 0xFFFFFFFF) ^
                      (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
    return v0, v1


async def tea_dec(v0, v1, k0, k1, k2, k3):
    s = (_DELTA * _ROUNDS) & 0xFFFFFFFF
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^
                      ((v0 + s) & 0xFFFFFFFF) ^
                      (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v0 = (v0 - (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^
                      ((v1 + s) & 0xFFFFFFFF) ^
                      (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1


async def tea_cbc_encrypt(padded, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(padded))
    prev_cipher = bytearray(8)
    prev_intermediate = bytearray(8)
    for i in range(0, len(padded), 8):
        xored = bytearray(8)
        for j in range(8):
            xored[j] = padded[i + j] ^ prev_cipher[j]
        e0, e1 = await tea_enc(
            struct.unpack_from("<I", xored, 0)[0],
            struct.unpack_from("<I", xored, 4)[0],
            k0, k1, k2, k3,
        )
        enc = bytearray(8)
        struct.pack_into("<I", enc, 0, e0)
        struct.pack_into("<I", enc, 4, e1)
        for j in range(8):
            out[i + j] = enc[j] ^ prev_intermediate[j]
        prev_cipher[:] = out[i:i + 8]
        prev_intermediate[:] = xored
    return bytes(out)


async def tea_cbc_decrypt(body, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(body))
    prev_intermediate = bytearray(8)
    prev_cipher = bytearray(8)
    xored = bytearray(8)
    dec = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8):
            xored[j] = body[i + j] ^ prev_intermediate[j]
        d0, d1 = await tea_dec(
            struct.unpack_from("<I", xored, 0)[0],
            struct.unpack_from("<I", xored, 4)[0],
            k0, k1, k2, k3
        )
        struct.pack_into("<I", dec, 0, d0)
        struct.pack_into("<I", dec, 4, d1)
        for j in range(8):
            out[i + j] = dec[j] ^ prev_cipher[j]
        prev_cipher[:] = body[i:i + 8]
        prev_intermediate[:] = dec
    return bytes(out)


async def build_padded(content):
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len, 0, 0]) + b"\x00" * pad_len + content + b"\x00" * 7


async def encode_header(layout, send_option, cmd, order_id, flags, length, k, v80):
    out = bytearray()
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: length}[code]
        if _FIELD_SIZES[code] == 1:
            out.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            out.append(v & 0xFF)
            out.append((v >> 8) & 0xFF)
    return bytes(out)


async def crc7_buff(crc, buf):
    c = crc & 0x7F
    for b in buf:
        c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F


async def sv_frame(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0]) + await encode_header(layout, send_option, cmd, order_id, flags, len(body), k, v80)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7F
    return bytes(packet)


async def build_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region=REGION, client_version="1.132.8",
                                      client_version_code="2019121229", access_token="",
                                      mode_id=43, map_id=11):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]

    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    encoded_thunder_jwt = thunder_jwt.encode() if isinstance(thunder_jwt, str) else thunder_jwt
    encoded_sharma_jwt = sharma_jwt.encode() if isinstance(sharma_jwt, str) else sharma_jwt

    garena420 = await has_ssan_zig(len(encoded_thunder_jwt)) + encoded_thunder_jwt
    reg = str(region).upper() if region else "ME"

    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200"
    )

    mid = bytes.fromhex('0000000001000102030101') + await has_ssan_zig(len(reg)) + reg.encode()
    mid += bytes.fromhex('0001030003000004')
    mid += await has_ssan_zig(len(client_version)) + client_version.encode()
    mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
    mid += csoversea_block

    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()

    clean_acc_tok = access_token.strip() if access_token else ""
    if clean_acc_tok:
        mid += await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode()

    mid += await has_ssan_zig(len(encoded_sharma_jwt)) + encoded_sharma_jwt

    tg_garena420 = (
        await uleb_encode(int(account_id)) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(1) +
        await uleb_encode(int(mode_id)) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(int(map_id)) +
        mid
    )

    process = await sv_frame(0x5E, match_code, 2, 447, 0, 1, garena420, udp_key)
    loading = await sv_frame(0x5A, match_code, 2, 448, 1, 1, tg_garena420, udp_key)
    return process.hex(), loading.hex()


async def produce_xor_key(secret_key):
    k = secret_key[0] if secret_key and len(secret_key) > 0 else 10
    return k, ((k << 8) | k) & 0xFFFF


async def parse_layout(layout):
    if isinstance(layout, str):
        return [int(ch) for ch in layout.strip()]
    return list(layout)


async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25:
        raise ValueError(f"Text is too long ({len(data)} bytes)")
    content = b"\x10\x00\x00\x00" + data + b"\x00" * (29 - 4 - len(data))
    k, v80 = await produce_xor_key(key)
    layout = await parse_layout(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    header_bytes = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    packet = bytearray([0x63, 0x00]) + header_bytes + enc_body
    packet[1] = await crc7_buff(0, packet[2:]) & 0x7F
    return bytes(packet).hex()


async def classify(frame):
    cmd = frame["cmd"]
    msg_name = MESSAGE_ID_TO_NAME.get(cmd, f"UNKNOWN_{cmd}")
    if msg_name == "UDP_HELLO":
        return "HELLO"
    if msg_name == "UDP_ACK":
        return "ACK"
    if msg_name == "UDP_PING":
        return "PING"
    if msg_name == "RUDP_JOIN_MATCH":
        return "JOIN_MATCH"
    if msg_name.startswith("RUDP_"):
        return msg_name
    if msg_name.startswith("UDP_"):
        return msg_name
    return "DATA"


async def build_packet(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: len(body)}[code]
        if _FIELD_SIZES[code] == 1:
            hdr.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF)
            hdr.append((v >> 8) & 0xFF)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7F
    return bytes(packet)


async def layouts_from_mask(mask):
    ru = [int(c) for c in str(mask).strip()]
    nr = [c for c in ru if c != 2]
    return ru, nr


async def reply_for(frame, key, mask, ack_key=0x68, ping_key=0x6D, hello_key=0x5B, ack_style="short"):
    ru, nr = await layouts_from_mask(mask)
    typ = await classify(frame)
    if typ == "HELLO":
        if ack_style == "echo":
            content = frame["content"] if frame["content"] else b"\x10\x00\x00\x00"
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ACK":
        content = frame["content"] if frame["content"] else b"\x01\x00"
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, content, key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None


async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_event_loop()
    i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<I", counter) + b"\x00\x00\x00", key_bytes, encrypted=False)
        try:
            await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception:
            pass
        i += 1
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=3.0)
        except asyncio.TimeoutError:
            pass


async def try_header(buf, layout, k, v80):
    off = 2
    out = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf):
            return None
        out[_FIELD_NAMES[code]] = (buf[off] ^ k) if size == 1 else ((buf[off] | (buf[off + 1] << 8)) ^ v80) & 0xFFFF
        off += size
    out["headerLen"] = off
    return out


async def oicq_unpad(padded):
    if not padded or len(padded) < 8:
        return None
    if not all(padded[-1 - i] == 0 for i in range(7)):
        return None
    pad_len = padded[0] & 0x07
    s = 3 + pad_len
    e = len(padded) - 7
    return padded[s:e] if s < e else b""


async def decode_packet(packet, key, mask=None):
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8:
        return None
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == await crc7_buff(0, data[2:])
    candidates = []
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0, 1, 2, 3, 4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0, 1, 3, 4])]
    for kind, layout in layouts:
        f = await try_header(data, layout, k, v80)
        if not f:
            continue
        if f["flags"] > 7 or f["sendOption"] > 7:
            continue
        if f["length"] != len(data) - f["headerLen"]:
            continue
        body = data[f["headerLen"]:f["headerLen"] + f["length"]]
        content = None
        padded = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0:
                continue
            padded = await tea_cbc_decrypt(body, key)
            content = await oicq_unpad(padded)
            if content is None:
                continue
        else:
            content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        candidates.append({
            "kind": kind, "layout": layout, "headerLen": f["headerLen"],
            "msgKey": data[0], "cmd": f["cmd"], "flags": f["flags"],
            "sendOption": f["sendOption"], "orderId": f.get("orderId"),
            "length": f["length"], "content": content, "crcOk": crc_ok,
            "padded": padded, "score": score, "total": len(data),
        })
    if not candidates:
        return None
    candidates.sort(key=lambda c: (c["kind"] in ("RUDP", "nonRUDP"), c["score"]), reverse=True)
    return candidates[0]


async def read_varints_full(b):
    out, i = [], 0
    while i < len(b):
        n, shift = 0, 0
        while i < len(b):
            byte = b[i]
            i += 1
            n |= (byte & 0x7F) << shift
            if not byte & 0x80:
                break
            shift += 7
        out.append(n)
    return out


def zigzag_encode(n):
    z = n << 1
    out = bytearray()
    while z >= 0x80:
        out.append((z & 0x7F) | 0x80)
        z >>= 7
    out.append(z)
    return bytes(out)


def crc7_bytes(data: bytes) -> int:
    c = 0
    for b in data:
        c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F


def build_movement_packet_2001(key_bytes, msg_key, player_state, x, y, z,
                                tick, counter, move_state, account_uid,
                                room_code, phase="game"):
    if phase == "arena":
        TAIL = (b"\x00" * 7 +
                b"\xbd\xb6\xe1\xf3\x03" +
                b"\x00" +
                b"\xc4\xb6\xe1\xfb\x0b" +
                b"\x00\x00")
    else:
        TAIL = (b"\x00" * 7 +
                b"\x93\xca\xd5\xf9\x0b" +
                b"\x8e\xfe\xfc\xf7\x0b" +
                b"\xf4\xe0\xfe\xf7\x03" +
                b"\x00\x00")

    body = bytearray()
    body += _pb_varint(account_uid)
    body += _pb_varint(player_state)
    body += zigzag_encode(x)
    body += zigzag_encode(y)
    body += zigzag_encode(z)
    body += b"\x00"
    body += _pb_varint(move_state)
    body += TAIL
    body += _pb_varint(tick)
    body += b"\x00\x00\x00"
    body += _pb_varint(counter)
    body = bytes(body)

    k = key_bytes[0]
    v80 = ((k << 8) | k) & 0xFFFF

    h = bytearray()
    h.append(msg_key)
    h.append(0x00)
    h.append(0 ^ k)
    h += ((2001 ^ v80) & 0xFFFF).to_bytes(2, "little")
    h += (len(body) ^ v80).to_bytes(2, "little")
    h.append(0 ^ k)
    h[1] = crc7_bytes(bytes(h[2:]) + body)
    return bytes(h) + body


class CSMovementState:
    def __init__(self, account_id):
        self.account_id = account_id
        self.player_id = None
        self.x = 100000
        self.y = 0
        self.z = 100000
        self.server_x = None
        self.server_y = None
        self.server_z = None
        self.pos_printed = False
        self.tick = 0
        self.counter = 0
        self.msg_key_idx = 0
        self.msg_keys = [0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F]
        self.player_state = 21073
        self.phase = "game"
        self.move_count = 0
        self.jump_toggle = 0


async def cs_send_movement(sock, ip, port, udp_key_bytes, match_code, mstate, move_state):
    loop = asyncio.get_event_loop()
    msg_key = mstate.msg_keys[mstate.msg_key_idx % len(mstate.msg_keys)]
    mstate.msg_key_idx += 1
    pid = mstate.player_id or mstate.account_id
    x = int(mstate.server_x) if mstate.server_x is not None else int(mstate.x)
    y = int(mstate.server_y) if mstate.server_y is not None else int(mstate.y)
    z = int(mstate.server_z) if mstate.server_z is not None else int(mstate.z)
    pkt = build_movement_packet_2001(
        udp_key_bytes,
        msg_key,
        mstate.player_state,
        x, y, z,
        mstate.tick,
        mstate.counter,
        move_state,
        pid,
        match_code,
        mstate.phase
    )
    try:
        await loop.sock_sendto(sock, pkt, (ip, port))
        mstate.move_count += 1
        mstate.tick += random.randint(1, 3)
        mstate.counter += random.randint(2, 8)
        return True
    except Exception:
        return False


async def cs_movement_loop(sock, ip, port, udp_key_bytes, match_code, mstate, stop_event):
    waited = 0.0
    while (mstate.server_x is None or mstate.server_z is None) and waited < 20.0 and not stop_event.is_set():
        await asyncio.sleep(0.5)
        waited += 0.5

    if mstate.server_x is None:
        print_warning(f"[CS MOVE] No server XYZ for {mstate.account_id}")
        mstate.x = 100000
        mstate.y = 295
        mstate.z = 100000
    elif not mstate.pos_printed:
        print_success(f"[CS MOVE] Real XYZ locked for {mstate.account_id}: ({int(mstate.server_x)}, {int(mstate.server_y)}, {int(mstate.server_z)})")
        mstate.pos_printed = True

    jump_cycle = [5, 5, 116, 5, 5, 5, 5, 104]
    idx = 0

    while not stop_event.is_set():
        move_state = jump_cycle[idx % len(jump_cycle)]
        idx += 1
        try:
            await cs_send_movement(sock, ip, port, udp_key_bytes, match_code, mstate, move_state)
        except Exception:
            pass
        for _ in range(int(CS_MOVE_INTERVAL * 10)):
            if stop_event.is_set():
                return
            await asyncio.sleep(0.1)


async def play_cs_game(server_ip_port, thunder, sharma, udp_key, match_code,
                       account_id, player_region, client_version, key, iv,
                       match_index: int, access_token=""):
    match_start_time = time.time()
    ping_task = None
    sock = None
    ping_stop = asyncio.Event()
    uid_str = str(account_id)
    completed_cleanly = False

    mstate = CSMovementState(account_id)
    movement_stop = asyncio.Event()
    movement_task = None

    try:
        ip, port = server_ip_port.split(":")
        port = int(port)
        resolved_ip = await resolve_host_cloudflare(ip)

        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.bind(('0.0.0.0', 0))
        except Exception:
            pass
        optimize_udp_socket(sock)
        sock.setblocking(False)

        udp_key_bytes = bytes.fromhex(udp_key)
        hello_packet = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_packet), (resolved_ip, port))

        log(f"[CS MATCH #{match_index}] Found UDP => {resolved_ip}:{port}")

        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        sharma_sent = False
        join_match_received = False
        local_closed = False
        send_lock = asyncio.Lock()

        ping_task = asyncio.create_task(
            keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code, ping_stop)
        )

        last_activity = time.time()

        async def send_thunder_sharma_inline():
            nonlocal ack_state, thunder_sent, sharma_sent, movement_task
            if thunder_sent:
                return
            async with send_lock:
                if thunder_sent:
                    return
                try:
                    await loop.sock_sendto(sock, bytes.fromhex(thunder), (resolved_ip, port))
                    thunder_sent = True
                    await asyncio.sleep(0.3)
                    prepare_ack = await build_packet(
                        0x68, (await layouts_from_mask(match_code))[1],
                        0, 2, None, 1, b"\x01\x00", udp_key_bytes
                    )
                    await loop.sock_sendto(sock, prepare_ack, (resolved_ip, port))
                    await asyncio.sleep(0.4)
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
                    sharma_sent = True
                    ack_state = "thunder_sharma_sent"
                    log(f"[CS MATCH #{match_index}] Startup delivered. Playing.")

                    if movement_task is None or movement_task.done():
                        movement_task = asyncio.create_task(
                            cs_movement_loop(
                                sock, resolved_ip, port,
                                udp_key_bytes, match_code,
                                mstate, movement_stop
                            )
                        )
                except Exception as e:
                    log(f"[CS MATCH #{match_index}] Startup send failed: {e}")

        while not local_closed:
            elapsed = time.time() - match_start_time
            if elapsed > CS_MAX_MATCH_DURATION:
                completed_cleanly = True
                break

            try:
                response, server_addr = await asyncio.wait_for(
                    loop.sock_recvfrom(sock, 65535), timeout=0.5
                )
                if response:
                    last_activity = time.time()
                    frame = await decode_packet(response, udp_key_bytes, match_code)
                    if frame:
                        cmd = frame.get('cmd')
                        order_id = frame.get('orderId')
                        flags = frame.get('flags', 0)
                        nr_layout = (await layouts_from_mask(match_code))[1]

                        if cmd in (103, 107):
                            log(f"[CS MATCH #{match_index}] Server ended match cmd={cmd}")
                            completed_cleanly = True
                            local_closed = True
                            continue

                        if cmd == 130:
                            try:
                                next_id = ((order_id or 0) + 1) & 0xFFFF
                                fin_ack = await build_packet(0x68, nr_layout, 0, 2, None, 1, next_id.to_bytes(2, "little"), udp_key_bytes)
                                await loop.sock_sendto(sock, fin_ack, server_addr)
                            except Exception:
                                pass
                            continue

                        if cmd == 101 and mstate.player_id is None:
                            try:
                                vs = await read_varints_full(frame.get('content') or b"")
                                if len(vs) >= 3:
                                    mstate.player_id = vs[2]
                            except Exception:
                                pass

                        if cmd == 2001:
                            try:
                                content = frame.get('content') or b""
                                vs = await read_varints_full(content)
                                if len(vs) >= 6:
                                    pid = vs[0]
                                    sx = vs[3]
                                    sy = vs[4]
                                    sz = vs[5]
                                    if pid and mstate.player_id is None:
                                        mstate.player_id = pid
                                    if pid != 0 and sx != 0 and sz != 0:
                                        mstate.server_x = sx
                                        mstate.server_y = sy
                                        mstate.server_z = sz
                                        if not mstate.pos_printed:
                                            print_success(f"[CS MOVE] Real XYZ locked for {mstate.account_id}: ({int(sx)}, {int(sy)}, {int(sz)})")
                                            mstate.pos_printed = True
                            except Exception:
                                pass

                        if (flags & 1) and order_id is not None:
                            try:
                                next_expected_id = (order_id + 1) & 0xFFFF
                                data_ack = await build_packet(0x68, nr_layout, 0, 2, None, 1, next_expected_id.to_bytes(2, "little"), udp_key_bytes)
                                await loop.sock_sendto(sock, data_ack, server_addr)
                            except Exception:
                                pass

                        if cmd == 101:
                            try:
                                ack_pkt = await build_packet(
                                    0x68, nr_layout,
                                    0, 2, None, 1, b"\x01\x00", udp_key_bytes
                                )
                                await loop.sock_sendto(sock, ack_pkt, server_addr)
                            except Exception:
                                pass

                        ptype = await classify(frame)
                        if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                            _, reply = await reply_for(frame, udp_key_bytes, match_code, ack_style="short")
                            if reply:
                                await loop.sock_sendto(sock, reply, server_addr)
                            ack_state = "ack_sent_waiting"
                        elif ptype == "ACK":
                            if ack_state in ("waiting_for_hello_reply", "ack_sent_waiting"):
                                ack_state = "ready_to_send_thunder"
                        elif ptype == "PING":
                            _, reply = await reply_for(frame, udp_key_bytes, match_code)
                            if reply:
                                await loop.sock_sendto(sock, reply, server_addr)
                        elif ptype == "JOIN_MATCH" and not join_match_received:
                            _, reply = await reply_for(frame, udp_key_bytes, match_code)
                            if reply:
                                await loop.sock_sendto(sock, reply, server_addr)
                                join_match_received = True

            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_thunder_sharma_inline()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > 7.0:
                        try:
                            pkt = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception:
                            pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        break
                elif ack_state == "thunder_sharma_sent":
                    idle = time.time() - last_activity
                    if idle > CS_IDLE_TIMEOUT:
                        log(f"[CS MATCH #{match_index}] Silent {int(idle)}s -> leaving")
                        completed_cleanly = True
                        break
                continue
            except BlockingIOError:
                await asyncio.sleep(0.05)
            except OSError:
                await asyncio.sleep(0.5)
                continue
            except Exception:
                await asyncio.sleep(0.5)
                continue

            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await send_thunder_sharma_inline()

        return f"cs match #{match_index} finished"

    except Exception as e:
        log(f"[CS MATCH #{match_index}] Session error: {e}")
        return f"cs match #{match_index} error"

    finally:
        movement_stop.set()
        if movement_task and not movement_task.done():
            movement_task.cancel()
            try:
                await movement_task
            except (asyncio.CancelledError, Exception):
                pass
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try:
                await ping_task
            except asyncio.CancelledError:
                pass
        if sock:
            try:
                sock.close()
            except Exception:
                pass
        remaining = await _dec_match(uid_str)
        try:
            bot_state.update_status(uid_str, "IN_MATCH" if remaining > 0 else "ONLINE", remaining)
        except Exception:
            pass


async def play_lw_game(server_ip_port, thunder, sharma, udp_key, match_code,
                       account_id, player_region, client_version, key, iv,
                       match_index: int):
    return await play_cs_game(
        server_ip_port, thunder, sharma, udp_key, match_code,
        account_id, player_region, client_version, key, iv,
        match_index=match_index
    )


async def refresh_account_profile(account_data: Dict):
    try:
        if not account_data:
            return
        url = account_data.get('server_url')
        token = account_data.get('token')
        release_version = account_data.get('release_version')
        payload = account_data.get('login_payload_data')
        if not (url and token and release_version and payload):
            return

        res = await send_getlogin(payload, url, token, release_version)
        if not res:
            return
        res_proto, dict_res = res

        level = 0
        exp = 0
        likes = 0
        try:
            if hasattr(res_proto, "level") and res_proto.level:
                level = int(res_proto.level)
        except Exception:
            pass
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 6, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 5, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            level = 1
        try:
            exp = int(get_proto_field(dict_res, 7, 0) or 0)
        except Exception:
            exp = 0
        try:
            likes = int(get_proto_field(dict_res, 8, 0) or 0)
        except Exception:
            likes = 0

        nickname = res_proto.nickname or get_proto_field(dict_res, 4, "")
        if exp < 0:
            exp = 0

        account_data['level'] = level
        account_data['exp'] = exp
        account_data['likes'] = likes
        if nickname:
            account_data['nickname'] = nickname

        try:
            uid_str = str(account_data.get('account_id'))
            bot_state.update_exp(uid_str, exp, level)
            if uid_str in bot_state.accounts:
                bot_state.accounts[uid_str]['likes'] = likes
                if nickname:
                    bot_state.accounts[uid_str]['nickname'] = nickname
        except Exception:
            pass
    except Exception:
        pass


async def process_account_uid_pass(uid: str, password: str) -> Optional[Dict]:
    log(f"[*] Logging in UID: {uid}")
    try:
        async with _LOGIN_SEMAPHORE:
            verconfig_res = await version_config()
            if verconfig_res is None:
                return None
            release_version, client_version, server_url = verconfig_res
            tokengrant_response = await get_access_token(uid, password)
            if tokengrant_response is None:
                log(f"[-] OAuth failed for UID {uid}")
                return None
            open_id, access_token, platform = tokengrant_response
            device_info = get_device_for_account(uid)
            login_payload_data = await build_majorlogin_payload(open_id, access_token, platform, client_version, device_info)
            if login_payload_data is None:
                return None
            majorlogin_response = await send_majorlogin(login_payload_data, release_version, server_url)
            if majorlogin_response is None:
                log(f"[-] MajorLogin failed for {uid}")
                return None
            getlogin_result = await send_getlogin(
                login_payload_data,
                majorlogin_response.url,
                majorlogin_response.token,
                release_version
            )
            if getlogin_result is None:
                log(f"[-] GetLoginData failed for {uid}")
                return None
            res_proto, dict_res = getlogin_result

        acc_id = str(majorlogin_response.account_id)
        level = 0
        exp = 0
        likes = 0
        try:
            if hasattr(res_proto, "level") and res_proto.level:
                level = int(res_proto.level)
        except Exception:
            pass
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 6, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 5, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            level = 1
        try:
            exp = int(get_proto_field(dict_res, 7, 0) or 0)
        except Exception:
            exp = 0
        try:
            likes = int(get_proto_field(dict_res, 8, 0) or 0)
        except Exception:
            likes = 0
        nickname = res_proto.nickname or get_proto_field(dict_res, 4, f"Player_{acc_id}")
        region = majorlogin_response.region or get_proto_field(dict_res, 3, REGION)
        if exp < 0:
            exp = 0

        func_addr = res_proto.functional_addrs
        info_addr = res_proto.informational_addrs
        if not isinstance(func_addr, str) or not func_addr or ":" not in func_addr:
            func_addr = None
        if not isinstance(info_addr, str) or not info_addr or ":" not in info_addr:
            info_addr = None

        key_val = majorlogin_response.aes_ak
        iv_val = majorlogin_response.iv_i
        if not isinstance(key_val, (bytes, bytearray)) or len(key_val) < 16:
            key_val = AES_KEY
        if not isinstance(iv_val, (bytes, bytearray)) or len(iv_val) < 16:
            iv_val = AES_IV

        account_data = {
            'account_id': majorlogin_response.account_id,
            'nickname': nickname,
            'region': region,
            'level': level,
            'exp': exp,
            'likes': likes,
            'open_id': open_id,
            'access_token': access_token,
            'platform': str(platform),
            'token': majorlogin_response.token,
            'server_time': majorlogin_response.server_time,
            'aes_ak': key_val,
            'iv_i': iv_val,
            'functional_addrs': func_addr,
            'informational_addrs': info_addr,
            'release_version': release_version,
            'client_version': client_version,
            'server_url': majorlogin_response.url,
            'login_payload_data': login_payload_data,
            'auth_type': 'guest',
            'auth_uid': uid,
            'auth_password': password
        }
        log(f"[+] Login OK | UID {acc_id} | {nickname} | Lvl {level}")
        return account_data
    except Exception as e:
        log(f"process_account_uid_pass error: {e}")
        return None


async def process_account_token(access_token: str) -> Optional[Dict]:
    log("[*] Logging in with access token")
    try:
        async with _LOGIN_SEMAPHORE:
            verconfig_res = await version_config()
            if verconfig_res is None:
                return None
            release_version, client_version, server_url = verconfig_res
            url = f"https://100067.connect.garena.com/oauth/token/inspect?token={access_token}"
            hdrs = {
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "close",
                "Content-Type": "application/x-www-form-urlencoded",
                "Host": "100067.connect.garena.com",
                "User-Agent": "GarenaMSDK/4.0.19P4(G011A ;Android 9;en;US;)"
            }
            resp = await client.get(url, headers=hdrs, timeout=10.0)
            if resp.status_code != 200:
                return None
            data = resp.json()
            if 'error' in data:
                return None
            open_id = data.get('open_id')
            platform = data.get('platform', 4)
            if not open_id:
                return None
            device_info = get_device_for_account(open_id)
            login_payload_data = await build_majorlogin_payload(open_id, access_token, str(platform), client_version, device_info)
            if not login_payload_data:
                return None
            majorlogin_response = await send_majorlogin(login_payload_data, release_version, server_url)
            if majorlogin_response is None:
                return None
            getlogin_result = await send_getlogin(
                login_payload_data,
                majorlogin_response.url,
                majorlogin_response.token,
                release_version
            )
            if getlogin_result is None:
                return None
            res_proto, dict_res = getlogin_result

        acc_id = str(majorlogin_response.account_id)
        level = 0
        exp = 0
        likes = 0
        try:
            if hasattr(res_proto, "level") and res_proto.level:
                level = int(res_proto.level)
        except Exception:
            pass
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 6, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            try:
                level = int(get_proto_field(dict_res, 5, 0) or 0)
            except Exception:
                level = 0
        if level <= 0:
            level = 1
        try:
            exp = int(get_proto_field(dict_res, 7, 0) or 0)
        except Exception:
            exp = 0
        try:
            likes = int(get_proto_field(dict_res, 8, 0) or 0)
        except Exception:
            likes = 0
        nickname = res_proto.nickname or get_proto_field(dict_res, 4, f"Player_{acc_id}")
        region = majorlogin_response.region or get_proto_field(dict_res, 3, REGION)
        if exp < 0:
            exp = 0

        account_data = {
            'account_id': majorlogin_response.account_id,
            'nickname': nickname,
            'region': region,
            'level': level,
            'exp': exp,
            'likes': likes,
            'open_id': open_id,
            'access_token': access_token,
            'platform': str(platform),
            'token': majorlogin_response.token,
            'server_time': majorlogin_response.server_time,
            'aes_ak': majorlogin_response.aes_ak,
            'iv_i': majorlogin_response.iv_i,
            'functional_addrs': res_proto.functional_addrs or get_proto_field(dict_res, 14),
            'informational_addrs': res_proto.informational_addrs or get_proto_field(dict_res, 32),
            'release_version': release_version,
            'client_version': client_version,
            'server_url': majorlogin_response.url,
            'login_payload_data': login_payload_data,
            'auth_type': 'token',
            'auth_token': access_token
        }
        log(f"[+] Login OK (token) | UID {acc_id} | {nickname} | Lvl {level}")
        return account_data
    except Exception as e:
        log(f"process_account_token error: {e}")
        return None


async def informational(addrs, starter_packet, key, iv, region=REGION, account_id="", max_reconnects=3):
    reconnects = 0
    ip, port = addrs.split(":")
    while True:
        writer = None
        ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))
            raw_sock = writer.get_extra_info('socket')
            if raw_sock:
                optimize_tcp_socket(raw_sock)
            writer.write(bytes.fromhex(starter_packet))
            await writer.drain()
            reconnects = 0

            try:
                init_ka = await send_keep_alive(region)
                if init_ka and writer and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def info_keepalive():
                ka_bytes = await send_keep_alive(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            ping_task = asyncio.create_task(info_keepalive())

            while True:
                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                except asyncio.TimeoutError:
                    continue
                if not data:
                    raise ConnectionError("Connection closed")
        except asyncio.CancelledError:
            if ping_task:
                ping_task.cancel()
            await safe_close_writer(writer)
            raise
        except Exception:
            if ping_task:
                ping_task.cancel()
            await safe_close_writer(writer)
            reconnects += 1
            if reconnects > max_reconnects:
                await asyncio.sleep(3)
                reconnects = 0
            else:
                await asyncio.sleep(1)


def choose_mode(level):
    try:
        lv = int(level)
    except Exception:
        lv = 1
    return "LW" if lv > MODE_SWITCH_LEVEL else "CS"


async def cs_fast_flow(addrs, starter_packet, account_region, client_version,
                        key, iv, account_id="", account_data=None, max_reconnects=10):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)
    last_match_end_time = 0.0

    current_token = starter_packet
    current_key = key
    current_iv = iv
    current_account_data = account_data

    try:
        if current_account_data:
            bot_state.register_account(
                uid_str,
                current_account_data.get("nickname", f"Player_{uid_str}"),
                current_account_data.get("region", REGION),
                current_account_data.get("level", 1),
                current_account_data.get("exp", 0),
                current_account_data.get("likes", 0),
            )
            bot_state.update_status(uid_str, "RUNNING")
            bot_state.account_start_ref[uid_str] = time.time()
            bot_state.start_exp_ref[uid_str] = int(current_account_data.get("exp", 0))
            bot_state.session_matches_ref[uid_str] = 0
            bot_state.exp_limit_reached_ref.discard(uid_str)
    except Exception:
        pass

    while True:
        writer = None
        gateway_ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))
            raw_sock = writer.get_extra_info('socket')
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(current_token))
            await writer.drain()

            try:
                init_ka = await send_keep_alive(account_region)
                if init_ka and writer and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def gateway_keepalive():
                ka_bytes = await send_keep_alive(account_region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            gateway_ping_task = asyncio.create_task(gateway_keepalive())

            log(f"[+] TCP gateway connected (CS) | UID: {uid_str}")
            reconnects = 0
            no_response_count = 0
            last_start_time = 0.0

            async def try_refresh_before_match():
                try:
                    if current_account_data:
                        await refresh_account_profile(current_account_data)
                except Exception:
                    pass
                try:
                    cur_lvl = int(current_account_data.get("level", 1) or 1) if current_account_data else 1
                except Exception:
                    cur_lvl = 1
                return cur_lvl

            async def send_start_match():
                nonlocal search_attempts, last_start_time
                search_attempts += 1
                lv = await try_refresh_before_match()
                if lv > MODE_SWITCH_LEVEL:
                    raise RuntimeError("mode_switch_to_lw")
                try:
                    await asyncio.sleep(random.uniform(0.2, 0.4))
                    log(f"[CS] UID {uid_str} | Lvl {lv} -> CS match #{search_attempts}")
                    st_pkt = await CS_Solo_Start_Matchmaking_Packet(current_key, current_iv, region=account_region)
                    writer.write(st_pkt)
                    await writer.drain()
                    try:
                        bot_state.update_status(uid_str, "SEARCHING", 0)
                    except Exception:
                        pass
                except Exception as e:
                    log(f"[!] StartMatch notice: {e}")
                last_start_time = asyncio.get_running_loop().time()

            try:
                await send_start_match()
            except RuntimeError as e:
                if "mode_switch_to_lw" in str(e):
                    log(f"[+] UID {uid_str} reached Lvl>{MODE_SWITCH_LEVEL} -> switching to LW")
                    if gateway_ping_task:
                        gateway_ping_task.cancel()
                    await safe_close_writer(writer)
                    writer = None
                    await lw_fast_flow(
                        addrs, current_token, account_region, client_version,
                        current_key, current_iv,
                        account_id=account_id,
                        account_data=current_account_data,
                        max_reconnects=max_reconnects
                    )
                    return

            while True:
                play_matches[:] = [m for m in play_matches if not m.done()]

                now = asyncio.get_running_loop().time()
                if len(play_matches) == 0 and (now - last_start_time >= CS_START_INTERVAL):
                    if last_match_end_time > 0:
                        rest_left = CS_MATCH_REST - (now - last_match_end_time)
                        if rest_left > 0:
                            await asyncio.sleep(min(rest_left, 1.0))
                            continue
                        last_match_end_time = 0.0
                    try:
                        await send_start_match()
                    except RuntimeError as e:
                        if "mode_switch_to_lw" in str(e):
                            log(f"[+] UID {uid_str} reached Lvl>{MODE_SWITCH_LEVEL} -> switching to LW")
                            if gateway_ping_task:
                                gateway_ping_task.cancel()
                            await safe_close_writer(writer)
                            writer = None
                            await lw_fast_flow(
                                addrs, current_token, account_region, client_version,
                                current_key, current_iv,
                                account_id=account_id,
                                account_data=current_account_data,
                                max_reconnects=max_reconnects
                            )
                            return

                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                except asyncio.TimeoutError:
                    no_response_count += 1
                    if no_response_count > 120:
                        no_response_count = 0
                    continue

                if not data:
                    raise ConnectionError("Connection closed by server")

                hex_data = data.hex()
                packet_length = len(data)
                no_response_count = 0

                if hex_data.startswith("0300") and 10 < packet_length < 30:
                    log(f"[*] Queue confirmed (CS) | UID: {uid_str}")
                    continue

                if hex_data.startswith("0300") and packet_length >= 300:
                    log(f"[+] Match found (CS) | UID: {uid_str}")

                    try:
                        res = json.loads(await decode_protobuf(hex_data[10:]))
                        token = None
                        udp_key = None
                        match_code = None
                        server_ip_port = None
                        match_account_id = None
                        block_val = None

                        if '42' in res and 'data' in res['42']:
                            match_code = res['42']['data']
                        if '5' in res and 'data' in res['5']:
                            res_field5 = res['5']['data']
                            server_ip_port = res_field5.get('2', {}).get('data')
                            udp_key = res_field5.get('3', {}).get('data')
                            token = res_field5.get('4', {}).get('data')
                            if '42' in res_field5:
                                match_code = res_field5['42']['data']
                        if '1' in res and 'data' in res['1']:
                            match_account_id = res['1']['data']
                        if '5' in res and 'data' in res['5']:
                            block_val = res['5']['data'].get('1', {}).get('data')

                        effective_acc_id = match_account_id or account_id or "ME_BOT"

                        if token and udp_key and match_code and server_ip_port:
                            acc_tok = current_account_data.get('access_token', '') if current_account_data else ""

                            mode_id, map_id = 43, 11

                            thunder, sharma = await build_match_startup_packets(
                                token, udp_key, match_code, effective_acc_id, block_val or 0,
                                server_ip=server_ip_port,
                                region=account_region,
                                client_version=client_version,
                                access_token=acc_tok,
                                mode_id=mode_id,
                                map_id=map_id
                            )

                            match_index = await _inc_match(uid_str)
                            log(f"[+] Match #{match_index} [CS] injected -> {server_ip_port}")

                            try:
                                bot_state.increment_match(uid_str)
                                bot_state.session_matches_ref[uid_str] = bot_state.session_matches_ref.get(uid_str, 0) + 1
                                bot_state.update_status(uid_str, "IN_MATCH")
                            except Exception:
                                pass

                            new_match = asyncio.create_task(
                                play_cs_game(
                                    server_ip_port,
                                    thunder,
                                    sharma,
                                    udp_key,
                                    match_code,
                                    effective_acc_id,
                                    account_region,
                                    client_version,
                                    current_key,
                                    current_iv,
                                    match_index=match_index,
                                    access_token=acc_tok
                                )
                            )
                            play_matches.append(new_match)

                            async def drain_gateway_reader():
                                while not new_match.done():
                                    try:
                                        data_gw = await asyncio.wait_for(reader.read(4096), timeout=1.0)
                                        if not data_gw:
                                            break
                                    except asyncio.TimeoutError:
                                        continue
                                    except Exception:
                                        break

                            drain_task = asyncio.create_task(drain_gateway_reader())

                            try:
                                await new_match
                            except Exception as e:
                                log(f"[CS MATCH #{match_index}] error: {e}")
                            finally:
                                drain_task.cancel()
                                try:
                                    await drain_task
                                except asyncio.CancelledError:
                                    pass

                            last_match_end_time = asyncio.get_running_loop().time()
                            play_matches[:] = [m for m in play_matches if not m.done()]

                            try:
                                await refresh_account_profile(current_account_data)
                            except Exception:
                                pass

                            try:
                                new_exp = int(current_account_data.get("exp", 0))
                                new_lvl = int(current_account_data.get("level", 1))
                                bot_state.update_exp(uid_str, new_exp, new_lvl)

                                target = int(bot_state.exp_targets_ref.get(uid_str, 0) or 0)
                                start_exp = int(bot_state.start_exp_ref.get(uid_str, new_exp))
                                if target > 0 and (new_exp - start_exp) >= target:
                                    bot_state.exp_limit_reached_ref.add(uid_str)
                                    bot_state.update_status(uid_str, "COMPLETED")
                                    log(f"[+] UID {uid_str} reached EXP target ({new_exp - start_exp}/{target})")
                            except Exception:
                                pass

                            if uid_str in bot_state.exp_limit_reached_ref:
                                log(f"[+] UID {uid_str} COMPLETED. Stopping CS worker.")
                                bot_state.update_status(uid_str, "COMPLETED")
                                if gateway_ping_task:
                                    gateway_ping_task.cancel()
                                await safe_close_writer(writer)
                                writer = None
                                return

                            if new_lvl > MODE_SWITCH_LEVEL:
                                log(f"[+] UID {uid_str} Lvl {new_lvl} > {MODE_SWITCH_LEVEL} -> switching to LW")
                                if gateway_ping_task:
                                    gateway_ping_task.cancel()
                                await safe_close_writer(writer)
                                writer = None
                                await lw_fast_flow(
                                    addrs, current_token, account_region, client_version,
                                    current_key, current_iv,
                                    account_id=account_id,
                                    account_data=current_account_data,
                                    max_reconnects=max_reconnects
                                )
                                return

                            await asyncio.sleep(CS_NEW_MATCH_DELAY)
                            continue

                    except Exception as e:
                        log(f"[!] Match packet notice: {e}")
                        continue

                if 30 <= packet_length <= 40:
                    continue

        except asyncio.CancelledError:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            raise
        except Exception as e:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            play_matches[:] = [m for m in play_matches if not m.done()]
            await safe_close_writer(writer)

            if "Cache expired" in str(e):
                break

            reconnects += 1
            if reconnects > max_reconnects:
                reconnects = 0
                await asyncio.sleep(3)
                continue

            await asyncio.sleep(min(reconnects, 2))
        finally:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            if writer:
                await safe_close_writer(writer)


async def lw_fast_flow(addrs, tcp_online_starter, account_region, client_version,
                        key, iv, account_id="", account_data=None, max_reconnects=10):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)
    parse_fail_count = 0

    current_token = tcp_online_starter
    current_key = key
    current_iv = iv
    current_account_data = account_data

    try:
        if current_account_data:
            bot_state.register_account(
                uid_str,
                current_account_data.get("nickname", f"Player_{uid_str}"),
                current_account_data.get("region", REGION),
                current_account_data.get("level", 1),
                current_account_data.get("exp", 0),
                current_account_data.get("likes", 0),
            )
            bot_state.update_status(uid_str, "RUNNING")
            if uid_str not in bot_state.account_start_ref:
                bot_state.account_start_ref[uid_str] = time.time()
                bot_state.start_exp_ref[uid_str] = int(current_account_data.get("exp", 0))
                bot_state.session_matches_ref[uid_str] = 0
                bot_state.exp_limit_reached_ref.discard(uid_str)
    except Exception:
        pass

    while True:
        writer = None
        gateway_ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))

            raw_sock = writer.get_extra_info('socket')
            if raw_sock:
                optimize_tcp_socket(raw_sock)

            writer.write(bytes.fromhex(current_token))
            await writer.drain()

            try:
                init_ka = await send_keep_alive(account_region)
                if init_ka and writer and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception:
                pass

            async def func_gateway_keepalive():
                ka_bytes = await send_keep_alive(account_region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka_bytes)
                            await writer.drain()
                    except Exception:
                        break

            gateway_ping_task = asyncio.create_task(func_gateway_keepalive())

            log(f"[+] TCP gateway connected (LW) | UID: {uid_str}")
            reconnects = 0
            no_response_count = 0
            last_start_time = 0.0
            parse_fail_count = 0

            async def send_start_match():
                nonlocal search_attempts, last_start_time
                search_attempts += 1
                try:
                    await asyncio.sleep(random.uniform(0.3, 0.6))
                    log(f"[LW] UID {uid_str} -> LW match #{search_attempts}")
                    await start_game_lone_wolf(
                        account_region, client_version, writer,
                        current_key, current_iv
                    )
                except Exception as e:
                    log(f"[!] StartMatch notice: {e}")
                last_start_time = asyncio.get_running_loop().time()

            await send_start_match()

            while True:
                play_matches[:] = [m for m in play_matches if not m.done()]

                now = asyncio.get_running_loop().time()
                if len(play_matches) == 0 and (now - last_start_time >= LW_START_INTERVAL):
                    await send_start_match()

                try:
                    data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                except asyncio.TimeoutError:
                    no_response_count += 1
                    if no_response_count > 80:
                        raise ConnectionError("idle")
                    continue

                if not data:
                    raise ConnectionError("Connection closed by server")

                hex_data = data.hex()
                packet_length = len(data)
                no_response_count = 0

                if hex_data.startswith("0300") and 10 < packet_length < 30:
                    log(f"[*] Queue confirmed (LW) | UID: {uid_str}")
                    continue

                if hex_data.startswith("0300") and packet_length >= 300:
                    log(f"[+] Match found (LW) | UID: {uid_str}")
                    try:
                        res = json.loads(await decode_protobuf(hex_data[10:]))
                        token = None
                        udp_key = None
                        match_code = None
                        server_ip_port = None
                        match_account_id = None
                        block_val = None

                        if '42' in res and 'data' in res['42']:
                            match_code = res['42']['data']
                        if '5' in res and 'data' in res['5']:
                            res_field5 = res['5']['data']
                            server_ip_port = res_field5.get('2', {}).get('data')
                            udp_key = res_field5.get('3', {}).get('data')
                            token = res_field5.get('4', {}).get('data')
                            if '42' in res_field5:
                                match_code = res_field5['42']['data']
                        if '1' in res and 'data' in res['1']:
                            match_account_id = res['1']['data']
                        if '5' in res and 'data' in res['5']:
                            block_val = res['5']['data'].get('1', {}).get('data')

                        effective_acc_id = match_account_id or account_id or "ME_BOT"

                        if token and udp_key and match_code and server_ip_port:
                            acc_tok = current_account_data.get('access_token', '') if current_account_data else ""
                            mode_id, map_id = 43, 11

                            thunder, sharma = await build_match_startup_packets(
                                token, udp_key, match_code, effective_acc_id, block_val or 0,
                                server_ip=server_ip_port,
                                region=account_region,
                                client_version=client_version,
                                access_token=acc_tok,
                                mode_id=mode_id,
                                map_id=map_id
                            )

                            match_index = await _inc_match(uid_str)
                            log(f"[+] Match #{match_index} [LW] injected -> {server_ip_port}")

                            try:
                                bot_state.increment_match(uid_str)
                                bot_state.session_matches_ref[uid_str] = bot_state.session_matches_ref.get(uid_str, 0) + 1
                                bot_state.update_status(uid_str, "IN_MATCH")
                            except Exception:
                                pass

                            if gateway_ping_task:
                                gateway_ping_task.cancel()
                            await safe_close_writer(writer)
                            writer = None

                            new_match = asyncio.create_task(
                                play_lw_game(
                                    server_ip_port,
                                    thunder,
                                    sharma,
                                    udp_key,
                                    match_code,
                                    effective_acc_id,
                                    account_region,
                                    client_version,
                                    current_key,
                                    current_iv,
                                    match_index=match_index
                                )
                            )
                            play_matches.append(new_match)

                            await asyncio.sleep(LW_NEW_MATCH_DELAY)

                            try:
                                await refresh_account_profile(current_account_data)
                            except Exception:
                                pass

                            try:
                                new_exp = int(current_account_data.get("exp", 0))
                                new_lvl = int(current_account_data.get("level", 1))
                                bot_state.update_exp(uid_str, new_exp, new_lvl)

                                target = int(bot_state.exp_targets_ref.get(uid_str, 0) or 0)
                                start_exp = int(bot_state.start_exp_ref.get(uid_str, new_exp))
                                if target > 0 and (new_exp - start_exp) >= target:
                                    bot_state.exp_limit_reached_ref.add(uid_str)
                                    bot_state.update_status(uid_str, "COMPLETED")
                                    log(f"[+] UID {uid_str} reached EXP target ({new_exp - start_exp}/{target})")
                            except Exception:
                                pass

                            if uid_str in bot_state.exp_limit_reached_ref:
                                log(f"[+] UID {uid_str} COMPLETED. Stopping LW worker.")
                                bot_state.update_status(uid_str, "COMPLETED")
                                return

                            break
                        else:
                            parse_fail_count += 1
                            if parse_fail_count >= LW_MAX_PARSE_FAILS:
                                parse_fail_count = 0
                            await asyncio.sleep(LW_RECONNECT_DELAY)
                            break
                    except Exception as e:
                        log(f"[!] Match packet notice: {e}")
                        parse_fail_count += 1
                        if parse_fail_count >= LW_MAX_PARSE_FAILS:
                            parse_fail_count = 0
                        await asyncio.sleep(LW_RECONNECT_DELAY)
                        break

                if 30 <= packet_length <= 40:
                    continue

        except asyncio.CancelledError:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            raise
        except Exception as e:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            play_matches[:] = [m for m in play_matches if not m.done()]
            await safe_close_writer(writer)

            if "Cache expired" in str(e):
                break

            reconnects += 1
            if reconnects > max_reconnects:
                reconnects = 0
                await asyncio.sleep(3)
                continue

            await asyncio.sleep(min(reconnects, 2))
        finally:
            if gateway_ping_task:
                gateway_ping_task.cancel()
            if writer:
                await safe_close_writer(writer)


async def functional_dispatcher(addrs, starter_packet, account_region, client_version,
                                 key, iv, account_id="", account_data=None, max_reconnects=10):
    cur_lvl = 1
    try:
        if account_data:
            v = account_data.get("level", 0)
            if v:
                cur_lvl = max(1, int(v))
    except Exception:
        cur_lvl = 1

    mode = choose_mode(cur_lvl)
    log(f"[*] Mode selected: {mode} | Lvl {cur_lvl}")

    if mode == "LW":
        await lw_fast_flow(
            addrs, starter_packet, account_region, client_version,
            key, iv, account_id=account_id, account_data=account_data,
            max_reconnects=max_reconnects
        )
    else:
        await cs_fast_flow(
            addrs, starter_packet, account_region, client_version,
            key, iv, account_id=account_id, account_data=account_data,
            max_reconnects=max_reconnects
        )


async def run_account_worker(account_data: Dict, label: str):
    acc_id = str(account_data['account_id'])
    informational_task = None
    exp_task = None
    functional_task = None
    try:
        reg = account_data.get('region', REGION)
        func_addr = account_data.get('functional_addrs')
        info_addr = account_data.get('informational_addrs')

        if not func_addr or not isinstance(func_addr, str) or ":" not in func_addr:
            log(f"[!] No functional_addrs for {acc_id} - worker idle")
            bot_state.update_status(acc_id, "ERROR")
            while True:
                await asyncio.sleep(60)
            return

        tcp_packet_online = await build_tcp_startup_packet(
            account_data['account_id'],
            account_data['token'],
            account_data['server_time'],
            account_data['aes_ak'],
            account_data['iv_i'],
            region=reg,
            typ='OnLine'
        )

        tcp_packet_chat = await build_tcp_startup_packet(
            account_data['account_id'],
            account_data['token'],
            account_data['server_time'],
            account_data['aes_ak'],
            account_data['iv_i'],
            region=reg,
            typ='ChaT'
        )

        if info_addr and isinstance(info_addr, str) and ":" in info_addr:
            informational_task = asyncio.create_task(
                informational(
                    info_addr,
                    tcp_packet_chat,
                    account_data['aes_ak'],
                    account_data['iv_i'],
                    region=reg
                )
            )

        await record_history({
            "uid": acc_id,
            "nickname": account_data.get("nickname", f"Player_{acc_id}"),
            "region": reg,
            "level": int(account_data.get("level", 1) or 1),
            "exp": int(account_data.get("exp", 0) or 0),
            "started_at": time.time(),
            "mode": choose_mode(int(account_data.get("level", 1) or 1)),
            "event": "worker_start"
        })

        async def exp_refresher():
            while True:
                await asyncio.sleep(EXP_REFRESH_INTERVAL)
                try:
                    await refresh_account_profile(account_data)
                except Exception:
                    pass

        exp_task = asyncio.create_task(exp_refresher())

        functional_task = asyncio.create_task(
            functional_dispatcher(
                func_addr,
                tcp_packet_online,
                account_data['region'],
                account_data['client_version'],
                account_data['aes_ak'],
                account_data['iv_i'],
                account_id=acc_id,
                account_data=account_data
            )
        )

        await functional_task

    except asyncio.CancelledError:
        raise
    except Exception as e:
        log(f"run_account_worker error for {label}: {e}")
    finally:
        for t in (informational_task, exp_task, functional_task):
            if t and not t.done():
                t.cancel()
        for t in (informational_task, exp_task, functional_task):
            if t:
                try:
                    await t
                except (asyncio.CancelledError, Exception):
                    pass
        try:
            bot_state.update_status(acc_id, "OFFLINE")
        except Exception:
            pass
        try:
            await record_history({
                "uid": acc_id,
                "nickname": account_data.get("nickname", f"Player_{acc_id}"),
                "region": account_data.get("region", REGION),
                "level": int(account_data.get("level", 1) or 1),
                "exp": int(account_data.get("exp", 0) or 0),
                "ended_at": time.time(),
                "event": "worker_stop"
            })
        except Exception:
            pass


async def generate_account_inline(region, prefix, password=None, lang=None, max_attempts=5):
    region = (region or REGION).upper()
    if not password:
        suffix = ''.join(random.choices(_string.ascii_letters + _string.digits, k=15))
        password = f"yazan-{suffix}"
    if not prefix:
        prefix = "bot"
    prefix = prefix[:7]
    name = f"{prefix}-{''.join(random.choices(_string.ascii_letters, k=6))}"
    lang = lang or GEN_REGION_LANG.get(region, "en")

    for attempt in range(max_attempts):
        try:
            pr = json.dumps({"app_id": 100067, "client_type": 2, "password": password, "source": 2}, separators=(",", ":"))
            sig = hmac.new(
                "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3".encode(),
                pr.encode(), hashlib.sha256
            ).hexdigest()
            hr = {
                "User-Agent": f"GarenaMSDK/4.0.44(ASUS ;Android 13;en;{region};app 1.132.1 2019121229;)",
                "Accept": "application/json",
                "Authorization": f"Signature {sig}",
                "Content-Type": "application/json; charset=utf-8",
                "Host": "100067.connect.garena.com"
            }
            rr = await client.post(
                "https://100067.connect.garena.com/api/v2/oauth/guest:register",
                headers=hr, data=pr, timeout=12
            )
            if rr.status_code != 200:
                if rr.status_code == 429:
                    await asyncio.sleep(2 ** attempt)
                continue
            rj = rr.json()
            if rj.get("code") != 0:
                continue
            uid = rj["data"]["uid"]

            pt = json.dumps({
                "client_id": 100067,
                "client_secret": "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3",
                "client_type": 2,
                "device_id": "02-%s" % hashlib.md5(str(uid).encode()).hexdigest()[:36],
                "password": password,
                "response_type": "token",
                "uid": uid
            }, separators=(",", ":"))
            ht = {
                "User-Agent": f"GarenaMSDK/4.0.44(ASUS ;Android 13;en;{region};app 1.132.1 2019121229;)",
                "Accept": "application/json",
                "Content-Type": "application/json; charset=utf-8",
                "Host": "100067.connect.garena.com"
            }
            rt = await client.post(
                "https://100067.connect.garena.com/api/v2/oauth/guest/token:grant",
                headers=ht, data=pt, timeout=12
            )
            if rt.status_code != 200:
                continue
            tj = rt.json()
            if tj.get("code") != 0:
                continue
            access_token = tj["data"]["access_token"]
            open_id = tj["data"]["open_id"]

            ks = [0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37, 0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37,
                  0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37, 0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30]
            fld = codecs.decode(
                "".join(chr(ord(open_id[i]) ^ ks[i % len(ks)]) for i in range(len(open_id)))
                .encode("unicode_escape").decode("utf-8"), "unicode_escape"
            ).encode("latin1")

            fields = {
                1: name, 2: access_token, 3: open_id, 5: 102000007, 6: 4, 7: 1,
                13: 1, 14: fld, 15: lang, 16: 1, 17: 1, 20: "1.132.6", 21: 1,
                22: GEN_FIELD_TEMPLATE
            }
            pd_hex = _gen_enc_hex(_gen_build_proto(fields).hex())
            ep = bytes.fromhex(pd_hex)
            await client.post(
                "https://loginbp.ppmainecoonghj.com/MajorRegister",
                headers=headers, data=ep, timeout=12
            )

            verconfig_res = await version_config()
            if not verconfig_res:
                continue
            release_version, client_version, server_url = verconfig_res

            device_info = get_device_for_account(str(uid))
            login_payload_data = await build_majorlogin_payload(open_id, access_token, 4, client_version, device_info)
            if not login_payload_data:
                continue
            majorlogin_response = await send_majorlogin(login_payload_data, release_version, server_url)
            if not majorlogin_response:
                continue
            getlogin_result = await send_getlogin(
                login_payload_data,
                majorlogin_response.url,
                majorlogin_response.token,
                release_version
            )
            if not getlogin_result:
                continue
            res_proto, dict_res = getlogin_result

            acc_id = str(majorlogin_response.account_id)
            level = int(get_proto_field(dict_res, 6, 1) or 1)
            exp = int(get_proto_field(dict_res, 7, 0) or 0)
            nickname = res_proto.nickname or name

            record = {
                "uid": str(uid),
                "account_id": acc_id,
                "name": name,
                "nickname": nickname,
                "password": password,
                "region": region,
                "level": level,
                "exp": exp,
                "access_token": access_token,
                "open_id": open_id,
                "date_created": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }
            try:
                bot_state.generated_accounts.append(record)
            except Exception:
                pass
            await record_history({
                "uid": acc_id,
                "nickname": nickname,
                "region": region,
                "level": level,
                "exp": exp,
                "created_at": time.time(),
                "event": "generated"
            })
            return record
        except Exception:
            pass
        await asyncio.sleep(0.5)
    return None


async def cb_login_only(payload: Dict):
    try:
        if payload.get("type") == "token":
            account_data = await process_account_token(payload["token"])
        else:
            account_data = await process_account_uid_pass(payload["uid"], payload["password"])
        if not account_data:
            raise RuntimeError("Login failed")
        uid = str(account_data["account_id"])
        bot_state.register_account(
            uid,
            account_data.get("nickname", f"Player_{uid}"),
            account_data.get("region", REGION),
            account_data.get("level", 1),
            account_data.get("exp", 0),
            account_data.get("likes", 0),
        )
        bot_state.account_credentials[uid] = account_data
        bot_state.accounts[uid]["status"] = "READY"
        log(f"[DASH] Registered UID {uid} - ready")
        return uid
    except Exception as e:
        log(f"[DASH] login_only error: {e}")
        raise


async def cb_set_target(uid: str, target: int):
    try:
        uid = str(uid)
        bot_state.exp_targets_ref[uid] = int(target)
        if uid in bot_state.accounts:
            bot_state.accounts[uid]["target"] = int(target)
        log(f"[DASH] Target set for {uid}: {target}")
    except Exception as e:
        log(f"[DASH] set_target error: {e}")
        raise


async def cb_start_account(uid: str):
    try:
        uid = str(uid)
        creds = bot_state.account_credentials.get(uid)
        if not creds:
            raise RuntimeError(f"No credentials for {uid}")
        if uid in bot_state.account_workers:
            t = bot_state.account_workers[uid]
            if t and not t.done():
                log(f"[DASH] {uid} already running")
                return
        bot_state.account_start_ref[uid] = time.time()
        bot_state.start_exp_ref[uid] = int(creds.get("exp", 0))
        bot_state.session_matches_ref[uid] = 0
        bot_state.exp_limit_reached_ref.discard(uid)
        task = asyncio.create_task(run_account_worker(creds, uid))
        bot_state.account_workers[uid] = task
        bot_state.update_status(uid, "RUNNING")
        log(f"[DASH] Started worker for {uid}")

        def _done(t, _uid=uid):
            try:
                bot_state.update_status(_uid, "OFFLINE")
                bot_state.account_workers.pop(_uid, None)
            except Exception:
                pass

        task.add_done_callback(_done)
    except Exception as e:
        log(f"[DASH] start_account error: {e}")
        raise


async def cb_stop_account(uid: str):
    try:
        uid = str(uid)
        t = bot_state.account_workers.get(uid)
        if t and not t.done():
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        bot_state.account_workers.pop(uid, None)
        bot_state.update_status(uid, "OFFLINE")
        log(f"[DASH] Stopped worker for {uid}")
    except Exception as e:
        log(f"[DASH] stop_account error: {e}")
        raise


async def cb_halt_account(uid: str):
    await cb_stop_account(uid)


async def cb_delete_account(uid: str):
    try:
        uid = str(uid)
        await cb_stop_account(uid)
        bot_state.accounts.pop(uid, None)
        bot_state.account_credentials.pop(uid, None)
        bot_state.exp_targets_ref.pop(uid, None)
        bot_state.start_exp_ref.pop(uid, None)
        bot_state.session_matches_ref.pop(uid, None)
        bot_state.account_start_ref.pop(uid, None)
        bot_state.exp_limit_reached_ref.discard(uid)
        log(f"[DASH] Deleted {uid}")
    except Exception as e:
        log(f"[DASH] delete_account error: {e}")
        raise


async def cb_add_friend(uid: str, target: str):
    try:
        uid = str(uid)
        target = str(target)
        if not _HAS_ADDFRIEND:
            return {"ok": False, "error": "ReqAddBoT not available"}
        creds = bot_state.account_credentials.get(uid)
        if not creds:
            return {"ok": False, "error": f"No credentials for {uid}"}
        if creds.get("auth_type") != "guest":
            return {"ok": False, "error": "Only UID+Password accounts supported"}
        auth_uid = str(creds.get("auth_uid", ""))
        auth_password = str(creds.get("auth_password", ""))
        if not auth_uid or not auth_password:
            return {"ok": False, "error": "Missing stored UID/password"}
        res = await send_friend_request_async(auth_uid, auth_password, target)
        return res if res else {"ok": False, "error": "No response"}
    except Exception as e:
        return {"ok": False, "error": str(e)}


async def cb_generate_accounts(name: str, region: str, count: int, threads: int, password: str = ""):
    generated = []
    try:
        count = max(1, min(50, int(count or 1)))
        prefix = (name or "bot")[:7]
        sem = asyncio.Semaphore(max(1, min(10, int(threads or 2))))
        results: List[Optional[Dict]] = [None] * count

        async def worker(i):
            async with sem:
                try:
                    acc = await generate_account_inline(region, prefix, password or None)
                    results[i] = acc
                except Exception:
                    results[i] = None

        await asyncio.gather(*(worker(i) for i in range(count)))
        for r in results:
            if r:
                generated.append(r)
        log(f"[GEN] Generated {len(generated)}/{count} accounts in {region}")
        return generated
    except Exception as e:
        log(f"[GEN] error: {e}")
        return generated


async def cb_gen_start(uid: str):
    uid = str(uid)
    try:
        found = None
        for a in (getattr(bot_state, "generated_accounts", []) or []):
            if str(a.get("uid")) == uid:
                found = a
                break
        if not found:
            raise RuntimeError(f"No generated account with UID {uid}")
        credentials = await process_account_uid_pass(str(found["uid"]), str(found["password"]))
        if not credentials:
            raise RuntimeError("Login failed")
        uid_real = str(credentials["account_id"])
        bot_state.register_account(
            uid_real,
            credentials.get("nickname", f"Player_{uid_real}"),
            credentials.get("region", REGION),
            credentials.get("level", 1),
            credentials.get("exp", 0),
            credentials.get("likes", 0),
        )
        bot_state.account_credentials[uid_real] = credentials
        bot_state.accounts[uid_real]["status"] = "READY"
        bot_state.account_start_ref[uid_real] = time.time()
        bot_state.start_exp_ref[uid_real] = int(credentials.get("exp", 0))
        bot_state.session_matches_ref[uid_real] = 0
        bot_state.exp_limit_reached_ref.discard(uid_real)

        task = asyncio.create_task(run_account_worker(credentials, uid_real))
        bot_state.account_workers[uid_real] = task
        bot_state.update_status(uid_real, "RUNNING")

        def _done(t, _uid=uid_real):
            try:
                bot_state.update_status(_uid, "OFFLINE")
                bot_state.account_workers.pop(_uid, None)
            except Exception:
                pass

        task.add_done_callback(_done)
        log(f"[GEN] Started {uid_real}")
    except Exception as e:
        log(f"[GEN] start error: {e}")
        raise


async def cb_gen_import(uid: str):
    uid = str(uid)
    try:
        found = None
        for a in (getattr(bot_state, "generated_accounts", []) or []):
            if str(a.get("uid")) == uid:
                found = a
                break
        if not found:
            raise RuntimeError(f"No generated account with UID {uid}")
        credentials = await process_account_uid_pass(str(found["uid"]), str(found["password"]))
        if not credentials:
            raise RuntimeError("Login failed")
        uid_real = str(credentials["account_id"])
        bot_state.register_account(
            uid_real,
            credentials.get("nickname", f"Player_{uid_real}"),
            credentials.get("region", REGION),
            credentials.get("level", 1),
            credentials.get("exp", 0),
            credentials.get("likes", 0),
        )
        bot_state.account_credentials[uid_real] = credentials
        bot_state.accounts[uid_real]["status"] = "READY"
        log(f"[GEN] Imported {uid_real}")
    except Exception as e:
        log(f"[GEN] import error: {e}")
        raise


async def cb_generated_download(uid: str = ""):
    accounts = getattr(bot_state, "generated_accounts", []) or []
    if uid:
        accounts = [a for a in accounts if str(a.get("uid")) == str(uid)]
    return accounts


async def cb_history():
    try:
        return list(getattr(bot_state, "history", []) or [])
    except Exception:
        return []


async def main():
    bot_state.bind_loop()

    if not hasattr(bot_state, "history"):
        bot_state.history = []

    bot_state.refresh_callbacks["on_account_login_only"] = cb_login_only
    bot_state.refresh_callbacks["on_set_target"] = cb_set_target
    bot_state.refresh_callbacks["on_start_account"] = cb_start_account
    bot_state.refresh_callbacks["on_stop_account"] = cb_stop_account
    bot_state.refresh_callbacks["on_halt_account"] = cb_halt_account
    bot_state.refresh_callbacks["on_delete_account"] = cb_delete_account
    bot_state.refresh_callbacks["on_add_friend"] = cb_add_friend
    bot_state.refresh_callbacks["on_generate_accounts"] = cb_generate_accounts
    bot_state.refresh_callbacks["on_gen_start"] = cb_gen_start
    bot_state.refresh_callbacks["on_gen_import"] = cb_gen_import
    bot_state.refresh_callbacks["on_gen_download"] = cb_generated_download
    bot_state.refresh_callbacks["on_history"] = cb_history

    runner = await start_web_dashboard(host="0.0.0.0", port=WEB_PORT)
    log(f"[WEB] YAZAN LEVEL dashboard ready on port {WEB_PORT}")

    try:
        while True:
            await asyncio.sleep(3600)
    except asyncio.CancelledError:
        pass
    finally:
        try:
            await runner.cleanup()
        except Exception:
            pass


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nStopped.")