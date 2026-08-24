const TelegramBot = require('node-telegram-bot-api');
const axios       = require('axios');
const crypto      = require('crypto');
const zlib        = require('zlib');
const puppeteer   = require('puppeteer');
const fs          = require('fs');
const path        = require('path');
const captchaModule = require('./captcha-solver-free');
const captchaLogin = captchaModule.captchaLogin || captchaModule;
if (typeof captchaLogin !== 'function') {
    throw new TypeError('captcha-solver-free.js must export captchaLogin');
}
// ============================================================
//  CONFIG
// ============================================================
// Keep secrets outside the source code.
const BOT_TOKEN    = process.env.BOT_TOKEN || "8868741436:AAHtR52bwP-C7o-gJSpoz8y9IH4y6F-Xui8";
const OWNER_ID     = 8869874751;
const OWNER_PASS   = process.env.OWNER_PASS || "2004";
const ADMIN_HANDLE = "@Sivakutty1";
const REG_LINK     = "https://bdgwinuu.com/#/register?invitationCode=7442815992780";
const WIN_STICKER  = "CAACAgUAAxkBAAFHUGNp4JX1-ohP4uBEWpfNptaz-HmwVgAC4hgAAhboKVbObuGuTcMs2zsE";
const LOSS_STICKER = "CAACAgUAAxkBAAFHUGVp4JX-BE2TRkhIKTwcjkwW-gzdPAACthoAAoG8YVYiydObSa0O8zsE";

const BET_URL     = "https://api.ar-lottery01.com/api/Lottery/WinGoBet";
const LOGIN_URL   = "https://13llottery.com/api/Home/Login";
const CAPTCHA_URL = "https://13llottery.com/api/Home/Captcha";
const DRAW_URL    = "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json?pageSize=20";
const SITE_URL    = "https://13lhack.vercel.app/";
const CHROME_ARGS = [
    '--no-sandbox', '--disable-setuid-sandbox', '--disable-gpu',
    '--disable-dev-shm-usage', '--disable-extensions', '--disable-background-networking',
    '--disable-component-update', '--disable-default-apps', '--no-first-run',
    '--no-zygote', '--single-process'
];

// Martingale multipliers — user can customize base bet
const MULT = [1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683]; // Standard 3x Martingale multipliers
const SIZE_WIN_MULTIPLIER = 1.85;   // Net profit multiplier for BIG/SMALL wins
const NUMBER_WIN_MULTIPLIER = 8.95; // Net profit multiplier for exact number wins

// ============================================================
//  RENDER KEEP-ALIVE
// ============================================================
const http = require('http');
const PORT = process.env.PORT || 5000;
http.createServer((req, res) => {
    res.writeHead(200);
    res.end('SIVA BOT OK');
}).listen(PORT, () => console.log(`✅ Keep-alive server on port ${PORT}`));

const RENDER_URL = process.env.RENDER_URL || "";
if (RENDER_URL) {
    setInterval(() => {
        axios.get(RENDER_URL).catch(() => {});
        console.log("[PING] Keep-alive ping sent");
    }, 14 * 60 * 1000).unref?.();
}

// ============================================================
//  STORAGE
// ============================================================
let ownerLoggedIn  = false;
let adminPasswords = {};
let adminLoggedIn  = {};
let usersAccess    = {};
let keyStore       = {};
let stats          = {};
let running        = {};
let sentPeriods    = {};
let ownerState     = null;
let adminState   = {};
let userAction   = {}; 
let userCreds       = {};
let credsSetupState = {};
let loginRetryTimers = {};
let autobetCfg      = {};
let autobetState   = {};
let profitTrack    = {};
let GLOBAL_TOKEN   = "";
const TOKEN_FILE = path.join(__dirname, 'user-tokens.json');

function normalizeToken(value) {
    if (value && typeof value === 'object') {
        value = value.token || value.accessToken || value.access_token ||
            value.jwt || value.data?.token || value.data?.accessToken ||
            value.data?.access_token || value.data?.jwt || '';
    }
    const token = String(value || '').replace(/^Bearer\s+/i, '').trim();
    return token.replace(/^['\"]|['\"]$/g, '').trim();
}

function loadUserTokens() {
    try {
        if (!fs.existsSync(TOKEN_FILE)) return {};
        const saved = JSON.parse(fs.readFileSync(TOKEN_FILE, 'utf8'));
        return saved && typeof saved === 'object' ? saved : {};
    } catch (error) {
        console.error('[TOKEN LOAD ERROR]', error.message);
        return {};
    }
}

function saveUserToken(userId, value) {
    const token = normalizeToken(value);
    if (!token || token.length < 20) return false;
    const key = String(userId);
    const next = { ...userTokens, [key]: token };
    const tmpFile = TOKEN_FILE + '.tmp';
    try {
        fs.mkdirSync(path.dirname(TOKEN_FILE), { recursive: true });
        fs.writeFileSync(tmpFile, JSON.stringify(next, null, 2) + '\n', { mode: 0o600 });
        fs.renameSync(tmpFile, TOKEN_FILE);
        userTokens = next;
        return true;
    } catch (error) {
        try { if (fs.existsSync(tmpFile)) fs.unlinkSync(tmpFile); } catch (_) {}
        console.error('[TOKEN SAVE ERROR]', error.message);
        return false;
    }
}

function clearUserToken(userId) {
    const key = String(userId);
    if (!Object.prototype.hasOwnProperty.call(userTokens, key)) return true;
    const next = { ...userTokens };
    delete next[key];
    const tmpFile = TOKEN_FILE + '.tmp';
    try {
        fs.writeFileSync(tmpFile, JSON.stringify(next, null, 2) + '\n', { mode: 0o600 });
        fs.renameSync(tmpFile, TOKEN_FILE);
        userTokens = next;
        return true;
    } catch (error) {
        try { if (fs.existsSync(tmpFile)) fs.unlinkSync(tmpFile); } catch (_) {}
        console.error('[TOKEN CLEAR ERROR]', error.message);
        return false;
    }
}

let userTokens = loadUserTokens();
let userLastSeen = {};
const nextRunTimers = new Map();
const resultCheckTimers = new Map();
const resultCheckInFlight = new Set();
const runInFlight = new Set();
const loginInFlight = new Map();
const MAX_SENT_PERIODS = 6;
const MAX_KEYS = 5000;
const USER_IDLE_TTL_MS = 60 * 60 * 1000;

function clearUserTimers(userId) {
    const key = String(userId);
    const nextTimer = nextRunTimers.get(key);
    if (nextTimer) clearTimeout(nextTimer);
    nextRunTimers.delete(key);

    const resultTimer = resultCheckTimers.get(key);
    if (resultTimer) clearTimeout(resultTimer);
    resultCheckTimers.delete(key);
    resultCheckInFlight.delete(key);
    runInFlight.delete(key);
}

function cleanupUserResources(userId, removeAccess = false) {
    const key = String(userId);
    clearUserTimers(key);
    resultCheckInFlight.delete(key);
    runInFlight.delete(key);
    delete adminState[key];
    delete userAction[key];
    delete userCreds[key];
    delete credsSetupState[key];
    delete loginRetryTimers[key];
    delete userTokens[key];
    delete userLastSeen[key];
    delete stats[key];
    delete userStates[key];
    delete autobetCfg[key];
    delete autobetState[key];
    delete profitTrack[key];
    delete sentPeriods[key];
    delete running[key];
    if (removeAccess) delete usersAccess[key];
}

function pruneExpiredUsers() {
    const now = Date.now();
    const tracked = new Set([
        ...Object.keys(usersAccess),
        ...Object.keys(userLastSeen),
        ...Object.keys(stats),
        ...Object.keys(userStates),
        ...Object.keys(autobetCfg),
        ...Object.keys(autobetState),
        ...Object.keys(profitTrack)
    ]);
    for (const key of tracked) {
        const expired = usersAccess[key] && Number(usersAccess[key]) <= now;
        const idle = !running[key] && !hasAccess(key) &&
            now - Number(userLastSeen[key] || 0) > USER_IDLE_TTL_MS;
        if (!running[key] && (expired || idle)) cleanupUserResources(key, true);
    }
}

// Prevent abandoned user objects and expired access records from accumulating.
const userPruneTimer = setInterval(pruneExpiredUsers, 10 * 60 * 1000);
userPruneTimer.unref?.();

function scheduleRun(userId, chatId, delayMs) {
    const key = String(userId);
    if (!running[userId]) return;
    const oldTimer = nextRunTimers.get(key);
    if (oldTimer) clearTimeout(oldTimer);
    const safeDelay = Math.max(1000, Number(delayMs) || 10000);
    const timer = setTimeout(() => {
        nextRunTimers.delete(key);
        if (running[userId]) {
            runPredict(userId, chatId).catch(error => {
                console.error("[RUN PREDICT ERROR]", error?.message || error);
                if (running[userId]) scheduleRun(userId, chatId, 10000);
            });
        }
    }, safeDelay);
    if (typeof timer.unref === "function") timer.unref();
    nextRunTimers.set(key, timer);
}
const MAX_LEVEL_HISTORY = 10;

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

async function fetchList() {
    try {
        // Draw history is the input for the local HTML-equivalent prediction engine and result settlement.
        const response = await axios.get(DRAW_URL, {
            headers: {
                "Accept": "application/json, text/plain, */*",
                "Origin": SITE_URL,
                "Referer": SITE_URL,
                "User-Agent": "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 Chrome/139.0.0.0 Safari/537.36"
            },
            timeout: 10000,
            validateStatus: status => status >= 200 && status < 300
        });
        if (!(response.data && response.data.data && Array.isArray(response.data.data.list))) {
            console.error("[FETCH LIST ERROR] WinGo response was not a list");
            return null;
        }
        return response.data.data.list;
    } catch (error) {
        console.error("[FETCH LIST ERROR]", error.message);
        return null;
    }
}
// Helper parser function
async function parseBalanceResponse(r) {
    if (r.data && r.data.code === 0 && r.data.data && typeof r.data.data.balance !== 'undefined') {
        return { success: true, balance: r.data.data.balance };
    }
    return {
        success: false,
        message: r.data && r.data.msg ? r.data.msg : "Token expired or invalid"
    };
}

async function getLiveBalance(userId, chatId = null) {
    let token = getToken(userId);
    
    // Optional: Auto login if token is missing
    if (!token && chatId) {
        const ok = await autoLogin(userId, chatId, true);
        if (ok) token = getToken(userId);
    }

    if (!token) return { success: false, message: "No token" };

    const url = "https://api.ar-lottery01.com/api/Lottery/GetBalance";
    const headers = {
        "Authorization": "Bearer " + token,
        "Ar-Origin": "https://13lwin19.com",
        "User-Agent": "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36"
    };

    try {
        const r = await axios.get(url, { headers, timeout: 5000 });
        return await parseBalanceResponse(r);
    } catch (e) {
        if (e.response && e.response.status === 405) {
            try {
                const r2 = await axios.post(url, {}, { headers, timeout: 5000 });
                return await parseBalanceResponse(r2);
            } catch (e2) {
                const errMsg = e2.response?.data?.msg || e2.message || "API Error";
                return { success: false, message: errMsg };
            }
        }
        const errMsg = e.response?.data?.msg || e.message || "API Error";
        return { success: false, message: errMsg };
    }
}

function initUser(id) {
    userLastSeen[id] = Date.now();
    if (!stats[id])        stats[id]        = { total:0,win:0,loss:0,lossStreak:0,winStreak:0,maxWinStreak:0,maxLossStreak:0,levelWins:{},sizeLevelWins:{},numberLevelWins:{} };
   if (!userStates[id])   userStates[id]   = { resultHistory:[], skipCount:0, currentMode:null, lastPrediction:null };
    if (!sentPeriods[id])  sentPeriods[id]  = new Set();
    if (!autobetCfg[id])   autobetCfg[id]   = { 
        watch:false, 
        watchLoss:2, 
        baseBet:1, 
        maxLvl:5, 
        enabled:false,
        mode:"SIZE", // SIZE, NUMBER, or COMBINED
        customBets:[1,3,9,27,81],
        customSizeBets:[1,2,4,8,16],
        customNumberBets:[1,9,81,729,6561],
        targetProfit: 1000,    // NEW: Profit target set panna
        restartDelay: 1        // NEW: Restart time (hours) set panna
    };
    if (autobetCfg[id].mode !== "SIZE" && autobetCfg[id].mode !== "NUMBER" && autobetCfg[id].mode !== "COMBINED") autobetCfg[id].mode = "SIZE";
    if (!Array.isArray(autobetCfg[id].customBets) || !autobetCfg[id].customBets.length) autobetCfg[id].customBets = [1,3,9,27,81];
    if (!Array.isArray(autobetCfg[id].customSizeBets) || !autobetCfg[id].customSizeBets.length) autobetCfg[id].customSizeBets = [1,2,4,8,16];
    if (!Array.isArray(autobetCfg[id].customNumberBets) || !autobetCfg[id].customNumberBets.length) autobetCfg[id].customNumberBets = [1,9,81,729,6561];
    if (!autobetState[id]) autobetState[id] = { 
        level:1,
        sizeLevel:1,
        numberLevel:1,
        consecutiveLoss:0,
        inMart:false,
        lastWinLevel:null,
        lastWinMode:null,
        isWaiting: false,
        nextStartTime: null,
        levelHistory: {},
        sizeLevelHistory: {},
        numberLevelHistory: {}
    };
    if (!autobetState[id].levelHistory || typeof autobetState[id].levelHistory !== "object") autobetState[id].levelHistory = {};
    if (!Number.isInteger(autobetState[id].sizeLevel) || autobetState[id].sizeLevel < 1) autobetState[id].sizeLevel = autobetState[id].level || 1;
    if (!Number.isInteger(autobetState[id].numberLevel) || autobetState[id].numberLevel < 1) autobetState[id].numberLevel = autobetState[id].level || 1;
    if (!autobetState[id].sizeLevelHistory || typeof autobetState[id].sizeLevelHistory !== "object") autobetState[id].sizeLevelHistory = {};
    if (!autobetState[id].numberLevelHistory || typeof autobetState[id].numberLevelHistory !== "object") autobetState[id].numberLevelHistory = {};
    if (!profitTrack[id])  profitTrack[id]  = { totalBets:0, wins:0, losses:0, pnl:0, winStreak:0, lossStreak:0, maxW:0, maxL:0, totalBetAmount: 0 };
}

function hasAccess(id) {
    if (Number(id) === Number(OWNER_ID)) return true;
    if (running[id] === true) return true;
    const expiry = usersAccess[id];
    return !!(expiry && Date.now() < expiry);
}
function daysLeft(id) {
    if (Number(id) === Number(OWNER_ID)) return "∞";
    if (running[id] === true) return "RUN";
    const expiry = usersAccess[id];
    if (!expiry) return "0";
    const left = (expiry - Date.now()) / 86400000;
    return left > 0 ? left.toFixed(1) : "0";
}
function isAdmin(id)    { return adminPasswords[id] !== undefined; }
function isAdminIn(id)  { return adminLoggedIn[id] === true; }
function getToken(id) {
    return normalizeToken(userTokens[String(id)]) || normalizeToken(GLOBAL_TOKEN) || "";
}

function generateKey(days, by) {
    const k = "EARN WITH ME-"+crypto.randomBytes(3).toString('hex').toUpperCase()+"-"+crypto.randomBytes(2).toString('hex').toUpperCase();
    keyStore[k] = { days, used:false, usedBy:null, by:by||OWNER_ID, createdAt: Date.now() };
    const keys = Object.keys(keyStore);
    if (keys.length > MAX_KEYS) {
        for (const key of keys) {
            if (keyStore[key]?.used) delete keyStore[key];
            if (Object.keys(keyStore).length <= MAX_KEYS) break;
        }
    }
    return k;
}
function activateKey(userId, code) {
    const k = code.toUpperCase().trim();
    if (!keyStore[k])     return { ok:false, msg:"❌ Invalid key!" };
    if (keyStore[k].used) return { ok:false, msg:"❌ Key already used!" };

    const days = Number(keyStore[k].days) || 1;
    const currentExpiry = usersAccess[userId];
    const base = (currentExpiry && currentExpiry > Date.now()) ? currentExpiry : Date.now();
    const newExpiry = base + days * 86400000;

    keyStore[k].used=true;
    keyStore[k].usedBy=userId;
    usersAccess[userId] = newExpiry;
    return { ok:true, days, expiry:new Date(newExpiry).toLocaleString() };
}
function activeUsersList() {
    const now=Date.now();
    const ids = new Set(Object.keys(usersAccess));
    Object.keys(running).forEach(id => { if (running[id]) ids.add(id); });

    const list = [...ids].filter(id => Number(id) === Number(OWNER_ID) || running[id] || Number(usersAccess[id]) > now);
    if (!list.length) return "No active users.";

    return list.map(id => {
        if (Number(id) === Number(OWNER_ID)) return "🟢 " + id + " | ♾️ Unlimited";
        if (running[id]) return "🟢 " + id + " | ⚡ Running";
        const expiry = Number(usersAccess[id]) || 0;
        return "🟢 " + id + " | " + ((expiry - now) / 86400000).toFixed(1) + "d";
    }).join("\n");
}
function adminList() {
    const ids=Object.keys(adminPasswords);
    return ids.length ? ids.map(id=>"👤 "+id+" | "+(adminLoggedIn[id]?"🟢 Online":"🔴 Offline")).join("\n") : "No admins.";
}
function allKeysList() {
    const keys=Object.entries(keyStore);
    return keys.length ? keys.map(([k,v])=>k+" → "+(v.used?"✅ Used":"🟢 "+v.days+"d")).join("\n") : "No keys.";
}

// ============================================================
//  DEVICE ID
// ============================================================
function getOrCreateDevice(userId) {
    if (!userCreds[userId]) userCreds[userId] = {};
    if (!userCreds[userId].deviceId) {
        userCreds[userId].deviceId = crypto.randomBytes(16).toString('hex');
    }
    return userCreds[userId].deviceId;
}

// ============================================================
//  SIGNATURES
// ============================================================
function makeLoginSign(params) {
    const p = {...params};
    delete p.signature; delete p.timestamp; delete p.track;
    const keys = Object.keys(p).filter(k => {
        const v = p[k];
        if (v === null || v === undefined || v === "") return false;
        if (typeof v === 'object') return false;
        return true;
    }).sort();
    const sorted = {};
    keys.forEach(k => { sorted[k] = p[k]; });
    const str = JSON.stringify(sorted);
    const sig = crypto.createHash('md5').update(str).digest('hex').toUpperCase().slice(0,32);
    return sig;
}

function makeBetSign(params) {
    const p = {...params};
    delete p.signature; delete p.timestamp;
    const keys = Object.keys(p).filter(k=>p[k]!==null&&p[k]!=="").sort();
    const sorted = {};
    keys.forEach(k=>{ sorted[k]=p[k]===0?0:p[k]; });
    return crypto.createHash('md5').update(JSON.stringify(sorted)).digest('hex').toUpperCase().slice(0,32);
}

// ============================================================
//  FETCH CAPTCHA
// ============================================================
async function fetchCaptcha() {
    try {
        const r = await axios.get(CAPTCHA_URL, {
            headers: {
                "Accept": "application/json, text/plain, */*",
                "Origin": "https://13lwin19.com",
                "Referer": "https://13lwin19.com",
                "Ar-Origin": "https://13lwin19.com",
                "User-Agent": "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Mobile Safari/537.36"
            },
            timeout: 10000
        });
        if (r.data?.code===0 && r.data?.data?.captchaId) {
            return r.data.data.captchaId;
        }
        return "";
    } catch(e) {
        console.error("[CAPTCHA ERR]", e.message);
        return "";
    }
}

// ============================================================
//  AUTO LOGIN (PUPPETEER VERSION)
// ============================================================
let loginLock = {};
async function autoLogin(userId, chatId, silent = false) {
    if (loginLock[userId]) {
        await logBoth(chatId, `[AUTO LOGIN] User ${userId} already in login process.`);
        return false;
    }
    loginLock[userId] = true;

    const creds = userCreds[userId] || {};
    const { phone, pass } = creds;

    if (!phone || !pass) {
        await logBoth(chatId, `[AUTO LOGIN] User ${userId} has no phone or password set.`);
        loginLock[userId] = false;
        return false;
    }

    try {
        const token = await captchaLogin(userId, chatId, phone, pass, bot, logBoth);
        if (token) {
            const cleanToken = normalizeToken(token);
            if (!cleanToken) {
                throw new Error('captchaLogin returned an empty token');
            }
            const saved = saveUserToken(userId, cleanToken);
            if (!saved || normalizeToken(userTokens[String(userId)]) !== cleanToken) {
                throw new Error('Token captured but could not be saved to userTokens');
            }
            console.log(`[TOKEN SAVED] User ${userId}; token length=${cleanToken.length}`);
            if (!silent) {
                await logBoth(chatId, `✅ [SUCCESS] Token captured for user ${userId}!`);
            }
            // Return the actual token so callers can use it immediately.
            return cleanToken;
        } else {
            if (!silent) {
                await logBoth(chatId, `❌ [FAILED] Login failed for user ${userId}`, true);
            }
            return false;
        }
    } catch (err) {
        await logBoth(chatId, `❌ Login Error for user ${userId}: ${err.message}`, true);
        return false;
    } finally {
        loginLock[userId] = false;
    }
}

async function robustLogin(userId, chatId, silent = false) {
    let success = await autoLogin(userId, chatId, silent);
    if (!success && !silent && chatId) {
        await logBoth(chatId, "❌ Login failed. Will retry automatically.");
    }
    return success;
}

async function startLoginWithRetry(userId, chatId) {
    if (loginRetryTimers[userId]) {
        clearTimeout(loginRetryTimers[userId]);
        delete loginRetryTimers[userId];
    }

    await send(chatId, "⏳ We are trying to login. Please hold on 3-5 minutes, we will be back to you.");

    let attempts = 0;

    async function attemptLogin() {
        if (!hasAccess(userId)) {
            delete loginRetryTimers[userId];
            return false;
        }
        attempts++;
        const ok = await autoLogin(userId, chatId, true);
        if (ok) {
            initUser(userId);
            autobetCfg[userId].enabled = true;
            if (loginRetryTimers[userId]) {
                clearTimeout(loginRetryTimers[userId]);
                delete loginRetryTimers[userId];
            }
            await send(chatId, "✅ Login Success!\n🤖 AutoBet is now turned ON automatically!", { reply_markup: userMenu(userId) });
            return true;
        }
        loginRetryTimers[userId] = setTimeout(attemptLogin, 60 * 1000);
        return false;
    }

    return attemptLogin();
}

// ============================================================
//  PLACE BET
// ============================================================
// PLACE BET (Modified to capture token from response if available)
// ============================================================
// ============================================================
//  IMPROVED PLACE BET FUNCTION (Silent Retries & Multi-Request Fix)
// ============================================================
// ============================================================
async function placeBet(userId, chatId, period, prediction, predType, level, amountOverride) {
    let token = getToken(userId);
    if (!token || token.length < 20) {
        console.log("[PLACE BET] Token missing or invalid, attempting autoLogin...");
        const freshToken = await autoLogin(userId, chatId, true);
        token = normalizeToken(freshToken) || getToken(userId);
        if (!token || token.length < 20) {
            await send(chatId, "❌ Token இல்லை! Auto-login தோல்வியடைந்தது.");
            return false;
        }
        console.log(`[PLACE BET] Fresh token loaded; length=${token.length}`);
    }

    // Always re-read the normalized per-user token immediately before the request.
    token = normalizeToken(token) || getToken(userId);
    if (!token || token.length < 20) {
        await send(chatId, '❌ Token missing before bet request.');
        return false;
    }

    const cfg       = autobetCfg[userId];
    const fallbackAmount = cfg.customBets[level-1] || (cfg.baseBet * MULT[level-1]);
    const betMult   = Number.isFinite(Number(amountOverride)) ? Number(amountOverride) : fallbackAmount;
    let bc = "";

    const maxRetries = 5; 
    const retryDelayMs = 2000; 

    if (predType === "SIZE") bc = prediction === "BIG" ? "BigSmall_Big" : "BigSmall_Small";
    if (predType === "NUMBER") bc = "Num_" + String(prediction);
    if (predType === "COLOR") bc = prediction === "RED" ? "Color_Red" : "Color_Green";

    console.log(`[BET] ${bc} ₹${betMult} L${level} for Period: ${period}`);

    for (let i = 0; i < maxRetries; i++) {
        try {
            // Dynamic generation inside the loop so random/timestamp/issueNumber are fresh on retry if needed
            const params = {
                amount:      1,
                betContent:  bc,
                betMultiple: betMult,
                gameCode:    "WinGo_1M", 
                issueNumber: String(period),
                language:    "en",
                random:      Math.floor(Math.random() * 1e12)
            };
            const signature = makeBetSign(params);
            const timestamp = Math.floor(Date.now() / 1000);
            const payload   = {...params, signature, timestamp};

            const r = await axios.post(BET_URL, payload, {
                headers: {
                    "authorization":    "Bearer " + token,
                    "content-type":     "application/json",
                    "Accept":           "application/json, text/plain, */*",
                    "Origin":           "https://13lwin19.com",
                    "Referer":          "https://13lwin19.com/",
                    "Ar-Origin":        "https://13lwin19.com",
                    "Sec-Ch-Ua":        '"Chromium";v="139"',
                    "Sec-Ch-Ua-Mobile": "?1",
                    "Sec-Fetch-Dest":   "empty",
                    "Sec-Fetch-Mode":   "cors",
                    "Sec-Fetch-Site":   "cross-site",
                    "User-Agent":       "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Mobile Safari/537.36"
                },
                timeout: 10000
            });

            const d = r.data;
            console.log(`[BET RESP] code:${d.code} msg:${d.msg}`);

            // Token check from response headers/body
            const newTokenFromResponseHeader = r.headers['authorization'] || r.headers['x-auth-token'];
            if (newTokenFromResponseHeader) {
                const cleanNewToken = newTokenFromResponseHeader.replace(/^Bearer\s+/i, "");
                if (cleanNewToken !== token) {
                                        saveUserToken(userId, cleanNewToken);
                    token = normalizeToken(cleanNewToken); // update local variable too
                    console.log("[TOKEN UPDATE] New token captured from bet response headers!");
                }
            }

            if (d.data && d.data.token && d.data.token !== token) {
                 saveUserToken(userId, d.data.token);
                 token = normalizeToken(d.data.token);
                 console.log("[TOKEN UPDATE] New token captured from bet response body!");
            }

            // Success case
            if (d.code === 0 || d.msg === "Succeed" || d.msgCode === 0) {
                return { ok: true, amt: betMult, bc };
            }

            // Token Expiry Handling -> AUTOMATIC RELOGIN (User கேட்காத வண்ணம்)
            if (d.code === 401 || d.code === 40100 || (d.msg && (d.msg.toLowerCase().includes("token") || d.msg.toLowerCase().includes("expired")))) {
                console.log("[AUTO RELOGIN] Token expired during bet. Clearing old token and trying autoLogin...");
                clearUserToken(userId);
                const freshToken = await autoLogin(userId, chatId, true);
                if (freshToken) {
                    token = normalizeToken(freshToken) || getToken(userId); // Get fresh token
                    console.log("[AUTO RELOGIN] Success! Retrying the bet with new token...");
                    continue; // Retry the loop with new token
                } else {
                    await send(chatId, "❌ Auto-login failed during token expiry.");
                    return false;
                }
            }

            // Retryable errors like Param is Invalid, issue number, etc.
            const retryableErrors = ["param is invalid", "the issue number does not exist", "period current settled"];
            const lowerMsg = (d.msg || "").toLowerCase();
            
            if (retryableErrors.some(errStr => lowerMsg.includes(errStr))) {
                console.log(`[BET RETRY] Retryable error: ${d.msg}. Retrying in ${retryDelayMs / 1000}s... (Attempt ${i + 1}/${maxRetries})`);
                await new Promise(resolve => setTimeout(resolve, retryDelayMs));
                continue; 
            }

            // Other unhandled API errors
            await send(chatId, "❌ Bet fail: " + (d.msg || JSON.stringify(d).substr(0, 60)));
            return false;

        } catch (err) {
            console.error("[BET ERR]", err.message);

            // Handle Axios 401 / Token errors inside catch block
            if (err.response && (err.response.status === 401 || (err.response.data && err.response.data.msg && (err.response.data.msg.toLowerCase().includes("token") || err.response.data.msg.toLowerCase().includes("expired"))))) {
                console.log("[AUTO RELOGIN] Token error caught via exception. Clearing old token and trying autoLogin...");
                clearUserToken(userId);
                const loginSuccess = await autoLogin(userId, chatId, true);
                if (loginSuccess) {
                    token = getToken(userId);
                    continue; // Retry after relogin
                } else {
                    await send(chatId, "❌ Auto-login failed during token error.");
                    return false;
                }
            }

            // For general network errors, retry if attempts left
            if (i < maxRetries - 1) {
                console.log(`[BET RETRY] Network error. Retrying in ${retryDelayMs / 1000}s... (Attempt ${i + 1}/${maxRetries})`);
                await new Promise(resolve => setTimeout(resolve, retryDelayMs));
                continue;
            }

            await send(chatId, "❌ Network error during bet: " + err.message);
            return false;
        }
    }

    console.log("[BET FAIL] All retries exhausted.");
    return false;
}
// ============================================================
// ============================================================
// COMPLETE BOT LOGIC WITH 4-PREDICTION PATTERN MODE EXTENSION & FIXES
// ============================================================
// ============================================================
// COMPLETE BOT LOGIC WITH STRICT 4-CONSECUTIVE LOSS REQUIREMENT (NO WINS ALLOWED)
// ============================================================
let userStates = {};

function getNextIssue(list) {
    const latest = (Array.isArray(list) ? list : [])
        .map(item => String(item?.issueNumber || ""))
        .find(issue => /^\d{8,}$/.test(issue));
    if (!latest) return null;
    try {
        const next = (BigInt(latest) + 1n).toString();
        return next.length === latest.length ? next : null;
    } catch {
        return null;
    }
}

function buildBSFromList(list, count = 15) {
    if (!Array.isArray(list)) return [];
    return list.slice(0, count).reverse().map(item => {
        const n = Number.parseInt(item?.number ?? item?.winNumber ?? -1, 10);
        return n >= 5 ? "BIG" : "SMALL";
    }).filter(Boolean);
}

function initState(userId) {
    if (!userStates[userId]) userStates[userId] = { lastSitePrediction: null, resultHistory: [] };
    if (!Array.isArray(userStates[userId].resultHistory)) userStates[userId].resultHistory = [];
}

function modeLabel(mode) {
    return mode === "NUMBER" ? "NUMBER" : mode === "COMBINED" ? "BIG/SMALL + NUMBER" : "BIG/SMALL";
}

function getSequenceAmount(userId, level, kind = "default") {
    const cfg = autobetCfg[userId] || {};
    const seq = cfg.mode === "COMBINED" ? (kind === "number" ? cfg.customNumberBets : cfg.customSizeBets) : cfg.customBets;
    return Number(seq?.[level - 1] ?? (cfg.baseBet * (MULT[level - 1] || 1)));
}

function getCombinedBetAmounts(userId, sizeLevel, numberLevel) {
    const cfg = autobetCfg[userId] || {};
    const base = Math.max(1, Number(cfg.baseBet) || 1);
    const sizeAmount = Number(cfg.customSizeBets?.[sizeLevel - 1] ?? base);
    const numberAmount = Number(cfg.customNumberBets?.[numberLevel - 1] ?? base);
    return {
        size: Number.isFinite(sizeAmount) && sizeAmount > 0 ? sizeAmount : base,
        number: Number.isFinite(numberAmount) && numberAmount > 0 ? numberAmount : base
    };
}

function combinedSettlement(bets, actualSize, actualNumber) {
    const sizeAmount = bets.filter(b => b.type === "SIZE").reduce((n, b) => n + Number(b.amt || 0), 0);
    const numberBets = bets.filter(b => b.type === "NUMBER");
    const numberAmount = numberBets.reduce((n, b) => n + Number(b.amt || 0), 0);
    const total = sizeAmount + numberAmount;
    const sizeWon = bets.some(b => b.type === "SIZE" && b.val === actualSize);
    const numberWon = numberBets.some(b => Number(b.val) === Number(actualNumber));
    if (sizeWon) return { won: true, pnl: sizeAmount * SIZE_WIN_MULTIPLIER - numberAmount, reason: "CATEGORY" };
    if (numberWon) {
        const winning = numberBets.filter(b => Number(b.val) === Number(actualNumber)).reduce((n, b) => n + Number(b.amt || 0), 0);
        return { won: true, pnl: winning * NUMBER_WIN_MULTIPLIER - (total - winning), reason: "NUMBER" };
    }
    return { won: false, pnl: -total, reason: "NONE" };
}

function updateCombinedAfterResult(userId, sizeWon, numberWon, betPlaced) {
    initUser(userId);
    const st = autobetState[userId];
    const cfg = autobetCfg[userId] || {};
    if (!betPlaced || cfg.mode !== "COMBINED") return;
    const sizeKey = "L" + st.sizeLevel;
    const numberKey = "L" + st.numberLevel;
    st.sizeLevelHistory[sizeKey] = (st.sizeLevelHistory[sizeKey] || 0) + 1;
    st.numberLevelHistory[numberKey] = (st.numberLevelHistory[numberKey] || 0) + 1;
    if (sizeWon || numberWon) {
        st.sizeLevel = 1; st.numberLevel = 1; st.level = 1;
    } else {
        st.sizeLevel = st.sizeLevel >= cfg.maxLvl ? 1 : st.sizeLevel + 1;
        st.numberLevel = st.numberLevel >= cfg.maxLvl ? 1 : st.numberLevel + 1;
        st.level = Math.max(st.sizeLevel, st.numberLevel);
    }
}

function formatPrediction(signal) {
    if (!signal || signal.skip === true) return "SKIP";
    if (signal.type === "NUMBER") return String(Number(signal.val));
    if (signal.type === "SIZE") return String(signal.val || "").toUpperCase();
    if (signal.type === "COMBINED") {
        const size = String(signal.val || "").toUpperCase();
        const number = signal.number ?? signal.bets?.find(b => b.type === "NUMBER")?.val;
        return number === undefined ? size : `${size} OR ${Number(number)}`;
    }
    return "SKIP";
}

// ============================================================
// SITE PREDICTION READER — one page, no refresh, no local predictor
// ============================================================
const siteReader = {
    browser: null,
    page: null,
    initPromise: null,
    readPromise: null,
    last: null,
    lastSignature: null,
    requestHandler: null,
    readCount: 0,
    recycleAfterReads: 20
};

async function ensureSitePage() {
    if (siteReader.page && !siteReader.page.isClosed()) return siteReader.page;
    if (siteReader.initPromise) return siteReader.initPromise;
    siteReader.initPromise = (async () => {
        siteReader.browser = await puppeteer.launch({
            headless: true,
            args: CHROME_ARGS
        });
        const page = await siteReader.browser.newPage();
        await page.setRequestInterception(true);
        siteReader.requestHandler = request => {
            const type = request.resourceType();
            if (type === 'image' || type === 'font' || type === 'media') {
                request.abort().catch(() => {});
            } else {
                request.continue().catch(() => {});
            }
        };
        page.on('request', siteReader.requestHandler);
        await page.setViewport({ width: 960, height: 640 });
        await page.setUserAgent('Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/139.0.0.0 Safari/537.36');
        await page.goto(SITE_URL, { waitUntil: 'domcontentloaded', timeout: 60000 });
        await page.waitForSelector('.current-card', { timeout: 30000 });
        siteReader.page = page;
        return page;
    })();
    try {
        return await siteReader.initPromise;
    } catch (error) {
        // If navigation/selector setup fails, close the partially-created browser
        // before the next retry; otherwise each retry can orphan a Chromium process.
        await closeSiteReader();
        throw error;
    } finally {
        siteReader.initPromise = null;
    }
}

async function closeSiteReader() {
    const page = siteReader.page;
    const browser = siteReader.browser;
    siteReader.page = null;
    siteReader.browser = null;
    siteReader.last = null;
    siteReader.lastSignature = null;
    siteReader.requestHandler = null;
    siteReader.readCount = 0;
    try { if (page && !page.isClosed()) await page.close(); } catch {}
    try { if (browser) await browser.close(); } catch {}
}

async function readSitePrediction(targetPeriod) {
    const period = String(targetPeriod);
    if (siteReader.last && siteReader.last.period === period) return siteReader.last;
    if (siteReader.readPromise) return siteReader.readPromise;

    siteReader.readPromise = (async () => {
        const page = await ensureSitePage();
        // 13lhack publishes the signal asynchronously; wait five seconds before reading.
        await sleep(5000);

        const data = await page.evaluate(() => {
            const card = document.querySelector('.current-card');
            if (!card) return null;

            const issueText = (card.querySelector('.label')?.textContent || '').trim();
            const predictionText = (card.querySelector('.prediction')?.textContent || '')
                .replace(/\s+/g, ' ').trim().toUpperCase();
            const issueMatch = issueText.match(/PREDICTION\s+FOR\s+ISSUE\s+(\d+)/i);
            const issue = issueMatch ? issueMatch[1] : '';

            if (!predictionText || predictionText === 'SKIP') {
                return { skip: true, issue, raw: predictionText, signature: `SKIP:${issue}` };
            }

            // Supports BIG3, BIG / 3, BIG-3, BIG OR 3, SMALL9, etc.
            const match = predictionText.match(
                /\b(BIG|SMALL)\s*(?:(?:\/|-|\bOR\b)\s*)?(10|[0-9])\b/
            );
            if (!match) {
                return { skip: true, issue, raw: predictionText, signature: `INVALID:${issue}:${predictionText}` };
            }

            return {
                skip: false,
                issue,
                side: match[1],
                number: Number(match[2]),
                raw: predictionText,
                signature: `${issue}:${match[1]}:${match[2]}`
            };
        });

        if (!data) throw new Error('13lhack prediction card is not ready');
        siteReader.lastSignature = data.signature;
        const result = { ...data, period, pattern: '13LHACK' };
        siteReader.last = result;
        siteReader.readCount++;

        // Keep one page alive, but recycle the browser periodically to prevent leaks.
        if (siteReader.readCount >= siteReader.recycleAfterReads) await closeSiteReader();
        return result;
    })();

    try { return await siteReader.readPromise; }
    finally { siteReader.readPromise = null; }
}

async function decidePrediction(_list, currentPeriod, userId) {
    const result = await readSitePrediction(currentPeriod);
    initState(userId);

    if (result.skip === true) {
        userStates[userId].lastPrediction = 'SKIP';
        userStates[userId].lastNumber = null;
        userStates[userId].lastReason = result.raw || '13lhack returned SKIP';
        return { skip: true, reason: result.raw || '13lhack returned SKIP' };
    }

    userStates[userId].lastPrediction = result.side;
    userStates[userId].lastNumber = result.number;
    userStates[userId].lastReason = result.pattern;

    // Pass the exact size and exact number from 13lhack unchanged.
    return {
        type: 'COMBINED',
        val: result.side,
        number: result.number,
        pat: result.pattern,
        bets: [
            { type: 'SIZE', val: result.side, kind: 'size' },
            { type: 'NUMBER', val: result.number, kind: 'number' }
        ]
    };
}
function updateAfterResult(userId, wasWin, actual, betPlaced) {
    initUser(userId);
    if (typeof autobetState !== 'undefined' && autobetState[userId]) {
        const st = autobetState[userId];
        const cfg = autobetCfg[userId] || {};
        if (betPlaced) {
            if (wasWin) { st.lastWinLevel = st.level; st.lastWinMode = cfg.mode || "SIZE"; st.level = 1; st.consecutiveLoss = 0; }
            else { st.consecutiveLoss++; st.level = st.level >= cfg.maxLvl ? 1 : st.level + 1; }
        } else if (cfg.watch) {
            st.consecutiveLoss = wasWin ? 0 : st.consecutiveLoss + 1;
        }
    }
}

function getStatus(userId) { initState(userId); return "SITE_ONLY"; }

function levelMapText(map) {
    const entries = Object.entries(map || {}).filter(([,v]) => Number(v) > 0).sort((a,b) => Number(a[0].slice(1)) - Number(b[0].slice(1)));
    return entries.length ? entries.map(([level,count]) => level + ":" + count).join(" | ") : "None";
}

function getStatus(userId) {
    initState(userId);
    const state = userStates[userId];
    return state.mode;
}

// ============================================================
// 2. handleWin - UI & Stats
// ============================================================
async function handleWin(userId, chatId, actual, num, betLevel, bets = [], settlement = null) {
    const pt = profitTrack[userId];
    const cfg = autobetCfg[userId];
    const amt = bets.length ? bets.reduce((sum, b) => sum + Number(b.amt || 0), 0) : getSequenceAmount(userId, betLevel);
    let profit;
    if (settlement) {
        profit = settlement.pnl;
    } else {
        const numberAmount = bets.filter(b => b.type === "NUMBER").reduce((sum, b) => sum + Number(b.amt || 0), 0);
        const sizeAmount = bets.filter(b => b.type === "SIZE").reduce((sum, b) => sum + Number(b.amt || 0), 0);
        profit = numberAmount > 0
            ? numberAmount * NUMBER_WIN_MULTIPLIER - (amt - numberAmount)
            : sizeAmount * SIZE_WIN_MULTIPLIER - (amt - sizeAmount);
    }
    
    pt.totalBets++; pt.wins++; pt.pnl += profit; 
    pt.totalBetAmount = (pt.totalBetAmount || 0) + amt;
    pt.winStreak++; pt.lossStreak = 0;
    if(pt.winStreak > pt.maxW) pt.maxW = pt.winStreak;

    await send(chatId,
"╔══════════════════════════╗\n"+
"║  ✅ WIN! 🎉              ║\n"+
"╠══════════════════════════╣\n"+
"║ Number : "+num+"\n"+
"║ Result : "+actual+"\n"+
"║ Profit : +₹"+profit.toFixed(2)+"\n"+
"║ P&L    : "+(pt.pnl>=0?"+":"")+pt.pnl.toFixed(2)+"\n"+
"║ Streak : "+pt.winStreak+" wins\n"+
"║ Total  : "+pt.wins+"W/"+pt.losses+"L\n"+
"║ Reset  : L1 | Watch 0/"+cfg.watchLoss+"\n"+
"╚══════════════════════════╝"
    );
    await sendSticker(chatId, WIN_STICKER);
}

// ============================================================
// 3. handleLoss - UI & Stats
// ============================================================
async function handleLoss(userId, chatId, actual, num, betLevel, bets = [], settlement = null) {
    const st = autobetState[userId];
    const pt = profitTrack[userId];
    const cfg = autobetCfg[userId];
    const amt = bets.length ? bets.reduce((sum, b) => sum + Number(b.amt || 0), 0) : getSequenceAmount(userId, betLevel);
    
    pt.totalBets++; pt.losses++; pt.pnl += settlement ? settlement.pnl : -amt; 
    pt.totalBetAmount = (pt.totalBetAmount || 0) + amt;
    pt.lossStreak++; pt.winStreak = 0;
    if(pt.lossStreak > pt.maxL) pt.maxL = pt.lossStreak;

    if(betLevel < cfg.maxLvl){
        const next = cfg.mode === "COMBINED" ? `Size ₹${getSequenceAmount(userId, st.sizeLevel, "size")} / Number ₹${getSequenceAmount(userId, st.numberLevel, "number")}` : (cfg.customBets[st.level-1] || (cfg.baseBet * MULT[st.level-1]));
        await send(chatId,
"╔══════════════════════════╗\n"+
"║  ❌ LOSS                 ║\n"+
"╠══════════════════════════╣\n"+
"║ Number : "+num+"\n"+
"║ Result : "+actual+"\n"+
"║ Loss   : -₹"+amt+"\n"+
"║ P&L    : "+(pt.pnl>=0?"+":"")+pt.pnl.toFixed(2)+"\n"+
"╠══════════════════════════╣\n"+
"║ Next L"+st.level+" : ₹"+next+"\n"+
"╚══════════════════════════╝"
        );
    } else {
        await send(chatId,
"╔══════════════════════════╗\n"+
"║  💀 MAX LEVEL LOSS       ║\n"+
"╠══════════════════════════╣\n"+
"║ Loss   : -₹"+amt+"\n"+
"║ P&L    : "+(pt.pnl>=0?"+":"")+pt.pnl.toFixed(2)+"\n"+
"║ Reset  : L1 | Watch 0/"+cfg.watchLoss+"\n"+
"╚══════════════════════════╝"
        );
    }
    await sendSticker(chatId, LOSS_STICKER);
}

// ============================================================
// PREDICT LOOP
// ============================================================
function parseItem(item) {
    const n = +(item.number || item.winNumber || 0);
    return {
        n,
        size: n >= 5 ? "BIG" : "SMALL",
        color:
            n === 0 ? "RED" :
            n === 5 ? "GREEN" :
            n % 2 === 0 ? "RED" : "GREEN"
    };
}

async function runPredict(userId, chatId) {
    const runKey = String(userId);
    if (runInFlight.has(runKey)) return;
    runInFlight.add(runKey);
    if(!running[userId]) { runInFlight.delete(runKey); return; }
    initUser(userId);
    const state = userStates[userId];
    const st = autobetState[userId];
    const cfg = autobetCfg[userId];

    if (st.isWaiting) {
        if (Date.now() >= st.nextStartTime) {
            st.isWaiting = false;
            profitTrack[userId].pnl = 0; 
            await send(chatId, "🔄 Timed Restart! Starting new section...");
        } else {
            scheduleRun(userId, chatId, 30000);
            runInFlight.delete(runKey);
            return;
        }
    }

    const list = await fetchList();
    if (!Array.isArray(list) || list.length === 0) {
        console.warn("[PREDICTION] Draw history unavailable; retrying without emitting a false prediction");
        scheduleRun(userId, chatId, 15000);
        runInFlight.delete(runKey);
        return;
    }

    // The draw API is the only external data input. Prediction is computed locally
    // from the supplied HTML algorithm; no website/browser navigation is used.
    const next = getNextIssue(list);
    if (!next) {
        await send(chatId, "SKIP");
        scheduleRun(userId, chatId, 10000);
        runInFlight.delete(runKey);
        return;
    }
    if (sentPeriods[userId].has(next)) { scheduleRun(userId, chatId, 3000); runInFlight.delete(runKey); return; }
    sentPeriods[userId].add(next);
    while (sentPeriods[userId].size > MAX_SENT_PERIODS) {
        sentPeriods[userId].delete(sentPeriods[userId].values().next().value);
    }

    initState(userId);
    const signal = await decidePrediction(list, next, userId);
    if(!signal) { scheduleRun(userId, chatId, 5000); runInFlight.delete(runKey); return; }
    if (signal.skip) {
        // This should only happen when the API returned no usable numbers.
        console.warn("[PREDICTION] Local engine skipped:", signal.reason);
        await send(chatId, "SKIP — history unavailable");
        scheduleRun(userId, chatId, 15000);
        runInFlight.delete(runKey);
        return;
    }

    let abLine = "🤖 AutoBet: OFF";
    let canBet = false;

    if (!cfg || !cfg.enabled) {
        abLine = "🤖 AutoBet: OFF";
        canBet = false;
    } else if (cfg.watch && st.consecutiveLoss < cfg.watchLoss) {
        abLine = `👀 WATCHING: ${st.consecutiveLoss}/${cfg.watchLoss}`;
        canBet = false;
    } else {
        canBet = true;
        const curBet = cfg.customBets[st.level-1] || (cfg.baseBet*MULT[st.level-1]);
        abLine = (st.level > 1 ? "📈 MART " : "💰 BET ") + "L" + st.level + ": ₹" + curBet;
    }

    const patternName = signal && signal.pat ? signal.pat : (state && state.mode ? state.mode : "NORMAL");
    const waitLine = (cfg && cfg.watch && st.consecutiveLoss < cfg.watchLoss) ? "\nWatch Loss: " + st.consecutiveLoss + "/" + cfg.watchLoss : "";

    await send(chatId,
"╔══════════════════════════╗\n"+
"║    👑 EARN WITH ME AI    ║\n"+
"╠══════════════════════════╣\n"+
"║ Period  : "+next.slice(-6)+"\n"+
"║ Mode    : BIG/SMALL + NUMBER\n"+
"║ Size    : "+signal.val+"\n"+
"║ Number  : "+(signal.number ?? signal.bets?.find(b=>b.type==="NUMBER")?.val ?? signal.bets?.find(b=>b.type==="SIZE")?.number ?? "-")+"\n"+
"║ Result  : "+formatPrediction(signal)+"\n"+
"║ Source  : Live Jade site\n"+
"╠══════════════════════════╣\n"+
"║ "+abLine+"\n"+
waitLine+"\n"+
"╚══════════════════════════╝",
        {reply_markup:{inline_keyboard:[[{text:"💰 CHECK NOW",url:REG_LINK}]]}}
    );

    let placedBets = [];
    if (canBet) {
        const rawSpecs = signal.bets || [{ type: signal.type, val: signal.val, kind: signal.type === "NUMBER" ? "number" : "size" }];
        // Always place exactly two bets: predicted size + exact in-range number.
        const specs = rawSpecs.filter(spec => spec.type === "SIZE" || spec.type === "NUMBER");
        const combinedAmounts = getCombinedBetAmounts(userId, st.sizeLevel, st.numberLevel);
        for (const spec of specs) {
            const amount = spec.kind === "number" ? combinedAmounts.number : combinedAmounts.size;
            const levelForBet = spec.kind === "number" ? st.numberLevel : st.sizeLevel;
            const result = await placeBet(userId, chatId, next, spec.val, spec.type, levelForBet, amount);
            if (result && result.ok) placedBets.push({ ...spec, amt: result.amt });
            else await send(chatId, "❌ Bet Failed (" + spec.type + "): " + (result?.msg || "Unknown error"));
        }
        if (placedBets.length) {
            await send(chatId, "✅ Bets Success: " + placedBets.length + " | L" + st.level + "\n" + placedBets.map(b => b.type + "=" + b.val + " ₹" + b.amt).join("\n") + "\n⏳ Checking result...");
        }
    }

    // Pass the signal bets separately so WATCH mode can evaluate predictions even when AutoBet is OFF.
    const rawPredictedBets = signal.bets || [{ type: signal.type, val: signal.val, kind: signal.type === "NUMBER" ? "number" : "size" }];
    const predictedBets = rawPredictedBets.filter(spec => spec.type === "SIZE" || spec.type === "NUMBER");
    checkResult(userId, chatId, next, signal.val, signal.type, placedBets, predictedBets);
    runInFlight.delete(runKey);
}

// ============================================================
// RESULT CHECKER
// ============================================================
async function checkResult(userId, chatId, target, predicted, predType, placedBets, predictedBets = []) {
    const timerKey = String(userId);
    if (resultCheckInFlight.has(timerKey)) return;
    resultCheckInFlight.add(timerKey);
    const previousTimer = resultCheckTimers.get(timerKey);
    if (previousTimer) clearTimeout(previousTimer);
    let tries = 0;
    let callbackBusy = false;
    const cfg = autobetCfg[userId];
    const st = autobetState[userId];
    const pt = profitTrack[userId];
    
    const releaseResultCheck = () => {
        if (iv) clearTimeout(iv);
        if (resultCheckTimers.get(timerKey) === iv) resultCheckTimers.delete(timerKey);
        resultCheckInFlight.delete(timerKey);
        callbackBusy = false;
    };
    let iv;
    const tick = async () => {
        if (callbackBusy) return;
        callbackBusy = true;
        try {
        if (!running[userId]) {
            releaseResultCheck();
            return;
        }
        if (++tries > 25) {
            releaseResultCheck();
            await logBoth(chatId, "⏱ Timeout — checking next period...");
            scheduleRun(userId, chatId, 15000);
            return;
        }
        const list = await fetchList();
        if (!list) {
            releaseResultCheck();
            scheduleRun(userId, chatId, 10000);
            return;
        }
        if (BigInt(list[0].issueNumber) < BigInt(target)) {
            callbackBusy = false;
            iv = setTimeout(tick, 10000);
            resultCheckTimers.set(timerKey, iv);
            return;
        }
        releaseResultCheck();

        const res = list.find(i => String(i.issueNumber) === String(target));
        if (!res) {
            scheduleRun(userId, chatId, 5000);
            return;
        }
        const num = parseInt(res.number || res.winNumber, 10);
        if (!Number.isFinite(num) || num < 0 || num > 9) {
            scheduleRun(userId, chatId, 5000);
            return;
        }
        const actualSize = num >= 5 ? "BIG" : "SMALL";

        const bets = Array.isArray(placedBets) ? placedBets : [];
        const betPlaced = bets.length > 0;
        // In WATCH mode, evaluate the original signal because no placed-bets array exists.
        // Colors are ignored; a category OR exact-number match is a WIN.
        const evaluationBets = betPlaced ? bets : (Array.isArray(predictedBets) ? predictedBets : []);
        const sizeMatched = evaluationBets.some(b => b.type === "SIZE" && b.val === actualSize);
        const numberMatched = evaluationBets.some(b => b.type === "NUMBER" && Number(b.val) === num);
        const isCombinedBet = evaluationBets.some(b => b.type === "SIZE") && evaluationBets.some(b => b.type === "NUMBER");
        const settlement = betPlaced && isCombinedBet ? combinedSettlement(bets, actualSize, num) : null;
        const win = settlement ? settlement.won : evaluationBets.some(b => b.type === "NUMBER"
            ? Number(b.val) === num
            : b.type === "SIZE" && b.val === actualSize);
        const betLevel = st.level;
        const sizeBetLevel = st.sizeLevel;
        const numberBetLevel = st.numberLevel;
        if (betPlaced) {
            const key = "L" + betLevel;
            st.levelHistory[key] = (st.levelHistory[key] || 0) + 1;
            const keys = Object.keys(st.levelHistory).sort((a, b) => Number(a.slice(1)) - Number(b.slice(1)));
            while (keys.length > MAX_LEVEL_HISTORY) delete st.levelHistory[keys.shift()];
        }

        if (isCombinedBet) updateCombinedAfterResult(userId, sizeMatched, numberMatched, betPlaced);
        else updateAfterResult(userId, win, actualSize, betPlaced);

        const s = stats[userId];
        if (betPlaced) {
            if (isCombinedBet) {
                if (sizeMatched) s.sizeLevelWins["L" + sizeBetLevel] = (s.sizeLevelWins["L" + sizeBetLevel] || 0) + 1;
                if (numberMatched) s.numberLevelWins["L" + numberBetLevel] = (s.numberLevelWins["L" + numberBetLevel] || 0) + 1;
            } else if (win) {
                s.levelWins["L" + betLevel] = (s.levelWins["L" + betLevel] || 0) + 1;
            }
        }
        s.total++;
        if (win) {
            s.win++; s.winStreak++; s.lossStreak = 0;
            if (s.winStreak > s.maxWinStreak) s.maxWinStreak = s.winStreak;
        } else {
            s.loss++; s.lossStreak++; s.winStreak = 0;
            if (s.lossStreak > s.maxLossStreak) s.maxLossStreak = s.lossStreak;
        }

        if (betPlaced) {
            if (win && settlement) {
                await handleWin(userId, chatId, actualSize, num, betLevel, bets, settlement);
            } else if (win) {
                await handleWin(userId, chatId, actualSize, num, betLevel, bets);
            } else if (settlement) {
                await handleLoss(userId, chatId, actualSize, num, betLevel, bets, settlement);
            } else {
                await handleLoss(userId, chatId, actualSize, num, betLevel, bets);
            }

            const targetProfit = Number(cfg.targetProfit) || 1000;
            if (pt.pnl >= targetProfit) {
                st.isWaiting = true;
                st.nextStartTime = Date.now() + (Number(cfg.restartDelay) || 1) * 60 * 1000;
                await send(chatId, "🎯 TARGET REACHED! Bot Paused.");
            }
        } else {
            if (win) {
                await send(chatId, 
                    "╔══════════════════════════╗\n"+
                    "║  👀 WATCH RESULT: WIN! ✅ ║\n"+
                    "╠══════════════════════════╣\n"+
                    "║ Number : "+num+"\n"+
                    "║ Result : "+actualSize+"\n"+
                    "║ Status : Correct Prediction\n"+
                    "╚══════════════════════════╝"
                );
                await sendSticker(chatId, WIN_STICKER);
            } else {
                await send(chatId, 
                    "╔══════════════════════════╗\n"+
                    "║  👀 WATCH RESULT: LOSS ❌ ║\n"+
                    "╠══════════════════════════╣\n"+
                    "║ Number : "+num+"\n"+
                    "║ Result : "+actualSize+"\n"+
                    "║ Status : Incorrect Prediction\n"+
                    "╚══════════════════════════╝"
                );
                await sendSticker(chatId, LOSS_STICKER);
            }
        }

        scheduleRun(userId, chatId, 8000);
        } catch (error) {
            releaseResultCheck();
            console.error("[RESULT CHECK ERROR]", error?.message || error);
            if (running[userId]) scheduleRun(userId, chatId, 10000);
        } finally {
            callbackBusy = false;
        }
    };
    iv = setTimeout(tick, 10000);
    resultCheckTimers.set(timerKey, iv);
}

module.exports = { decidePrediction, updateAfterResult, getStatus, initState, buildBSFromList, runPredict, checkResult };

function showStats(chatId,userId){
    const d=stats[userId],rate=d.total?((d.win/d.total)*100).toFixed(1):"0.0";
    const bar="🟦".repeat(d.total?Math.round(d.win/d.total*10):0)+"⬜".repeat(d.total?10-Math.round(d.win/d.total*10):10);
    send(chatId,"📊 STATS\n\nTotal: "+d.total+"\nWins: "+d.win+"\nLosses: "+d.loss+"\nAcc: "+rate+"%\n"+bar+"\n\nBest Win: "+d.maxWinStreak+" streak\nWorst Loss: "+d.maxLossStreak+" streak");
}
async function profitReport(chatId,userId){
    initUser(userId);
    const pt=profitTrack[userId],cfg=autobetCfg[userId];
    const rate=pt.totalBets?((pt.wins/pt.totalBets)*100).toFixed(1):"0.0";
    const amounts=cfg.customBets.slice(0,cfg.maxLvl);
    let balance = "❌ No token";
    const balResult = await getLiveBalance(userId);
    if(balResult.success){
        balance = "₹"+balResult.balance;
    } else if (balResult.message){
        balance = "⚠️ "+balResult.message;
    }
    send(chatId,
"💰 PROFIT REPORT\n\n"+
"Balance: "+balance+"\n"+
"Bets   : "+pt.totalBets+"\nWins   : "+pt.wins+"\nLoss   : "+pt.losses+"\nRate   : "+rate+"%\n"+
"P&L    : "+(pt.pnl>=0?"+":"")+pt.pnl.toFixed(2)+"\n"+
"Best W : "+pt.maxW+" | Worst L: "+pt.maxL+"\n\n"+
"Mart: ₹"+amounts.join("→₹")
    );
}
async function autobetStatus(chatId, userId) {
    initUser(userId);
    const cfg = autobetCfg[userId], st = autobetState[userId], pt = profitTrack[userId];
    const amounts = cfg.mode === "COMBINED" ? cfg.customSizeBets.slice(0, cfg.maxLvl) : cfg.customBets.slice(0, cfg.maxLvl);
    const creds = userCreds[userId] || {};

    let liveBal = "❌ No token";
    let token = getToken(userId);
    const hasToken = token && token.length > 20;
    if (hasToken) {
        const result = await getLiveBalance(userId);
        if (result.success) {
            liveBal = "₹" + result.balance;
        } else {
            liveBal = "⚠️ " + result.message;
        }
    } else if (creds.phone) {
        liveBal = "❌ Login Required";
    }

    let waitLine = "";
    if (st.isWaiting) {
        const diff = Math.round((st.nextStartTime - Date.now()) / 60000);
        waitLine = "\n⏳ Waiting: " + diff + " mins to restart";
    }

    send(chatId,
"🤖 AUTOBET STATUS\n\n"+
"💰 Live Balance: "+liveBal+"\n"+
"Enabled  : "+(cfg.enabled?"✅ ON":"❌ OFF")+"\n"+
"Token    : "+(token.length>20?"✅":"❌")+"\n"+
"AutoLogin: "+(creds.phone?"✅ "+creds.phone.slice(0,6)+"***":"❌")+"\n"+
"Mode     : "+modeLabel(cfg.mode)+"\n"+
    (cfg.mode === "COMBINED" ? "Size Bets: ₹"+cfg.customSizeBets.join(" → ₹")+"\nNum Bets : ₹"+cfg.customNumberBets.join(" → ₹")+"\nRule     : 1 site size + 1 site number\n" : "Bet Seq  : ₹"+cfg.customBets.join(" → ₹")+"\n")+
"Watch    : "+(cfg.watch?"ON":"OFF")+"\n"+
"WatchLoss: "+st.consecutiveLoss+"/"+cfg.watchLoss+"\n"+
"Base Bet : ₹"+cfg.baseBet+"\n"+
"Max Level: "+cfg.maxLvl+"\n"+
"Target Profit: ₹"+cfg.targetProfit+"\n"+
"Section Delay: "+cfg.restartDelay+" mins"+ // Hours-la irunthu Minutes-ku mathi irukken
waitLine+"\n"+
"In Mart  : "+(st.inMart?"YES":"NO")+"\n"+
(cfg.mode === "COMBINED" ? "Size L"+st.sizeLevel+" | Number L"+st.numberLevel+"\n" : "Current  : L"+st.level+"\n")+
"Last Win : "+(st.lastWinLevel?"L"+st.lastWinLevel+" ("+(st.lastWinMode||cfg.mode)+")":"None")+"\n"+
(cfg.mode === "COMBINED" ? "Size Hist: "+(Object.entries(st.sizeLevelHistory||{}).map(([level,count]) => level+":"+count).join(" | ") || "None")+"\nNumber Hist: "+(Object.entries(st.numberLevelHistory||{}).map(([level,count]) => level+":"+count).join(" | ") || "None")+"\n" : "History  : "+(Object.entries(st.levelHistory||{}).map(([level,count]) => level+":"+count).join(" | ") || "None")+"\n")+
"Wins Lvl : "+(cfg.mode === "COMBINED" ? "Size "+levelMapText(stats[userId].sizeLevelWins)+" | Number "+levelMapText(stats[userId].numberLevelWins) : levelMapText(stats[userId].levelWins))+"\n"+
"P&L      : "+(pt.pnl>=0?"+":"")+pt.pnl.toFixed(2)+"\n\n"+
"Mart: ₹"+amounts.join("→₹")
    );
}



// ============================================================
//  KEYBOARDS
// ============================================================
function userMenu(id){
    const rows=[["▶️ Start Prediction"],["⏹ Stop Prediction"],["📊 Stats","💰 Profit","📩 Contact"],["🤖 AutoBet Setup","🔑 My Token"]];
    if(isAdmin(id))rows.push(["👑 Admin Panel"]);
    return{keyboard:rows,resize_keyboard:true};
}
const ownerMenu={keyboard:[["👥 All Users","👮 All Admins"],["👤 Add Admin","🗑 Remove Admin"],["🔑 Generate Key","📋 All Keys"],["🟢 Add User","🔴 Remove User"],["🔐 Set Token","📊 All Status"],["🚪 Owner Logout"]],resize_keyboard:true};
const adminMenu={keyboard:[["👥 Active Users","🔑 Generate Key"],["🟢 Add User","🔴 Remove User"],["📋 All Keys","🚪 Admin Logout"]],resize_keyboard:true};
const autobetMenu={keyboard:[
    ["✅ Enable AutoBet","❌ Disable AutoBet"],
    ["👀 Watch Mode ON","👀 Watch Mode OFF"],
    ["💰 Set Base Bet","📈 Set Max Level"],
    ["🎯 Set Profit Target", "⏳ Set Section Delay"],
    ["🔢 Set Watch Losses","📊 AutoBet Status"],
    ["🎮 Mode: Big/Small","🔢 Mode: Number"],
    ["🔀 Mode: BigSmall+Number","🔀 Customize Bet"],
    ["🔙 Back"]
],resize_keyboard:true};

// ============================================================
//  BOT INIT
// ============================================================
let bot;
let handlersAttachedTo = null;
let pollingRecovery = false;
function recoverPolling(err) {
    if (pollingRecovery || !bot) return;
    pollingRecovery = true;
    console.warn("[POLL] Recovering from polling error:", err?.message || err);
    bot.stopPolling().catch(() => {});
    setTimeout(() => {
        try {
            bot.startPolling();
            console.log("[POLL] Polling restarted successfully.");
        } catch (e) {
            console.error("[POLL] Polling restart failed:", e?.message || e);
        } finally {
            pollingRecovery = false;
        }
    }, 5000);
}
function startBot(){
    if (!BOT_TOKEN) throw new Error("BOT_TOKEN environment variable is required");
    if(bot){try{bot.stopPolling();}catch(e){}}
    bot=new TelegramBot(BOT_TOKEN,{polling:{interval:1000,autoStart:true,params:{timeout:30}}});
    bot.on("polling_error",err=>{
        const msg = err?.message || String(err);
        if (msg.includes("409") || msg.toLowerCase().includes("terminated by other getupdates request")) {
            console.error("[POLL] 409 Conflict: another bot instance is using this token. Polling stopped; keep only one deployed instance running.");
            pollingRecovery = true;
            bot.stopPolling().catch(() => {});
            return;
        }
        if (msg.includes("ECONNRESET") || msg.includes("EFATAL") || msg.includes("socket hang up")) {
            recoverPolling(err);
            return;
        }
        console.error("Poll:", msg);
    });
    bot.on("error",err=>{
        const msg = err?.message || String(err);
        if (msg.includes("409") || msg.toLowerCase().includes("terminated by other getupdates request")) {
            console.error("[POLL] 409 Conflict: stop the duplicate bot instance, then redeploy this one.");
            bot.stopPolling().catch(() => {});
            return;
        }
        if (msg.includes("ECONNRESET") || msg.includes("EFATAL") || msg.includes("socket hang up")) {
            console.warn("Bot error recovered:", msg);
            return;
        }
        console.error("Bot:", msg);
    });
    addHandlers();
    console.log("✅ SIVA BOT running...");

}

async function send(chatId,text,opts={}){
    try{return await bot.sendMessage(chatId,text,opts);}
    catch(e){if(e.message&&e.message.includes("parse entities")){try{const o={...opts};delete o.parse_mode;return await bot.sendMessage(chatId,text,o);}catch(e2){}}console.error("send:",e.message?.substr(0,60));}
}

// Shared logger used by autoLogin() and captcha-solver-free.js.
// Signature: logBoth(chatId, message, isError)
async function logBoth(chatId, message, isError = false) {
    const text = String(message || "");
    if (isError) console.error(text);
    else console.log(text);
    if (chatId !== undefined && chatId !== null) {
        await send(chatId, text);
    }
}

async function sendSticker(chatId,sid){try{await bot.sendSticker(chatId,sid);}catch(e){}}

// ============================================================
//  AUTO LOGIN TASK
// ============================================================


// ============================================================
//  HANDLERS
// ============================================================
function addHandlers(){
    if (handlersAttachedTo === bot) return;
    handlersAttachedTo = bot;
    bot.onText(/\/start/,(msg)=>{
        const id=msg.from.id;initUser(id);
        const status=hasAccess(id)?"✅ ACTIVE — "+daysLeft(id)+"d left":"❌ NO ACCESS";
        send(msg.chat.id,
"╔══════════════════════════╗\n║  👑EARN WITH ME BOT    ║\n╠══════════════════════════╣\n"+
"║ Status : "+status+"\n║ ID     : "+id+"\n║ Admin  : "+ADMIN_HANDLE+"\n╠══════════════════════════╣\n"+
"║ /key CODE to activate    ║\n╚══════════════════════════╝",
        {reply_markup:userMenu(id)});
    });

    bot.onText(/\/key (.+)/,(msg,match)=>{
        const id=msg.from.id;initUser(id);
        const res=activateKey(id,match[1].trim());
        if(res.ok){send(msg.chat.id,"🎊 KEY ACTIVATED!\n⏳ "+res.days+" days\n📅 "+res.expiry,{reply_markup:userMenu(id)});send(OWNER_ID,"🔔 Key used!\nUser: "+id+"\nDays: "+res.days);}
        else send(msg.chat.id,res.msg);
    });

     bot.onText(/\/setcreds ?(.*)/,(msg,match)=>{
        const id=msg.from.id;
        if(!hasAccess(id))return send(id,"❌ No access.");
        const rest = (match[1] || "").trim();
        if (rest && rest.includes(" ")) {
            const parts = rest.split(/\s+/);
            const phone = parts[0];
            const pass = parts.slice(1).join(" ");
            credsSetupState[id] = { step: 3, phone, pass };
            const summary =
                "📋 Confirm your credentials:\n\n" +
                "📱 Mobile: " + phone + "\n" +
                "🔑 Password: " + "*".repeat(Math.min(pass.length, 8)) + "\n\n" +
                "Is this correct?";
            return send(id, summary, {
                reply_markup: {
                    inline_keyboard: [
                        [{ text: "✅ Yes", callback_data: "creds_confirm_yes" }, { text: "❌ No", callback_data: "creds_confirm_no" }]
                    ]
                }
            });
        }
        credsSetupState[id] = { step: 1 };
        send(id, "📱 Please enter your Mobile Number (e.g. 916381605525):");
    });


    bot.onText(/\/setmytoken (.+)/,(msg,match)=>{
        const id=msg.from.id;
        if(!hasAccess(id))return send(id,"❌ No access.");
        const tok=match[1].trim().replace(/^Bearer\s+/i,"");
        if(tok.length<20)return send(id,"❌ Token too short!");
        const cleanToken = normalizeToken(tok);
        if (cleanToken.length < 20) return send(id,"❌ Token too short!");
        saveUserToken(id, cleanToken);
        send(id,"✅ Token saved!\n..."+tok.slice(-12)+"\n\n🤖 AutoBet Setup → ✅ Enable");
    });

    bot.onText(/^\/login(?:@\w+)?$/, async (msg) => {
        const id = String(msg.from.id);
        const chatId = msg.chat.id;
        initUser(id);
        if (!hasAccess(id)) return send(chatId, "❌ No access.");

        const creds = userCreds[id] || {};
        if (!creds.phone || !creds.pass) {
            return send(chatId, "❌ First use /setcreds FULLPHONE PASSWORD");
        }

        await send(chatId, "🔄 Calling CAPTCHA login...");
        await autoLogin(id, chatId, false);
    });

    bot.onText(/\/owner/,(msg)=>{
        if(msg.from.id!==OWNER_ID)return;
        if(ownerLoggedIn)return send(OWNER_ID,"Already in!",{reply_markup:ownerMenu});
        ownerState={action:"login"};send(OWNER_ID,"� Owner password:");
    });

    bot.onText(/\/adminlogin (.+)/,(msg,match)=>{
        const id=msg.from.id,pass=match[1].trim();
        if(!isAdmin(id))return send(id,"Not admin.");
        if(pass===adminPasswords[id]){adminLoggedIn[id]=true;send(id,"✅ Admin Login!",{reply_markup:adminMenu});}
        else send(id,"❌ Wrong!");
    });

    bot.on("callback_query", async (cb) => {
        const id = cb.from.id;
        const data = cb.data || "";
        const chatId = cb.message && cb.message.chat ? cb.message.chat.id : id;
        try { await bot.answerCallbackQuery(cb.id); } catch (e) {}

        if (data === "creds_confirm_yes") {
            const s = credsSetupState[id];
            if (!s || !s.phone || !s.pass) {
                credsSetupState[id] = { step: 1 };
                return send(chatId, "⚠️ Session expired. Let's start over.\n\n📱 Please enter your Mobile Number (e.g. 916381605525):");
            }
            if (!userCreds[id]) userCreds[id] = {};
            userCreds[id].phone = s.phone;
            userCreds[id].pass = s.pass;
            delete credsSetupState[id];
            startLoginWithRetry(id, chatId);
        } else if (data === "creds_confirm_no") {
            credsSetupState[id] = { step: 1 };
            send(chatId, "🔁 Let's try again.\n\n📱 Please enter your Mobile Number (e.g. 916381605525):");
        }
    });
    bot.on("message",async msg=>{
        const id=msg.from.id,text=msg.text;
        if(!text||text.startsWith("/"))return;
                initUser(id);

        // Interactive credential setup started by the My Token button.
        if (hasAccess(id) && credsSetupState[id]) {
            const setup = credsSetupState[id];

            if (setup.step === 1) {
                const phone = text.trim();
                if (!/^\d{10,15}$/.test(phone)) {
                    return send(id, "❌ Invalid mobile number. Example: 916381605525");
                }
                credsSetupState[id] = { step: 2, phone };
                return send(id, "🔑 Please enter your password:");
            }

            if (setup.step === 2) {
                const pass = text.trim();
                if (!pass) return send(id, "❌ Password cannot be empty.");

                credsSetupState[id] = { step: 3, phone: setup.phone, pass };
                return send(id, "📋 Confirm your credentials:\n\n" +
                    "📱 Mobile: " + setup.phone + "\n" +
                    "🔑 Password: " + "*".repeat(Math.min(pass.length, 8)) + "\n\n" +
                    "Is this correct?", {
                    reply_markup: {
                        inline_keyboard: [[
                            { text: "✅ Yes", callback_data: "creds_confirm_yes" },
                            { text: "❌ No", callback_data: "creds_confirm_no" }
                        ]]
                    }
                });
            }
        }

        const OB=["👥 All Users","👮 All Admins","👤 Add Admin","🗑 Remove Admin","🔑 Generate Key","📋 All Keys","🟢 Add User","🔴 Remove User","🔐 Set Token","📊 All Status","🚪 Owner Logout"];
        const AB=["👥 Active Users","🔑 Generate Key","🟢 Add User","🔴 Remove User","📋 All Keys","🚪 Admin Logout"];

        if(id===OWNER_ID&&ownerState){
            const s=ownerState;
            if(s.action==="login"){if(text===OWNER_PASS){ownerLoggedIn=true;ownerState=null;return send(OWNER_ID,"👑 Welcome!",{reply_markup:ownerMenu});}else return send(OWNER_ID,"❌ Wrong!");}
            if(OB.includes(text)){ownerState=null;}
            else if(s.action==="addadmin"){if(!s.step2){const t=parseInt(text);if(isNaN(t))return send(OWNER_ID,"❌");ownerState={action:"addadmin",step2:true,tid:t};return send(OWNER_ID,"ID:"+t+"\nPassword:");}else{if(text.length<6)return send(OWNER_ID,"❌ Min 6");adminPasswords[s.tid]=text;adminLoggedIn[s.tid]=false;ownerState=null;send(OWNER_ID,"✅ Admin: "+s.tid,{reply_markup:ownerMenu});send(s.tid,"🎉 Admin!\n/adminlogin "+text);return;}}
            else if(s.action==="removeadmin"){const t=parseInt(text);if(isNaN(t))return;delete adminPasswords[t];delete adminLoggedIn[t];ownerState=null;send(OWNER_ID,"🚫 Removed",{reply_markup:ownerMenu});return;}
            else if(s.action==="genkey"){const d=parseInt(text);if(isNaN(d)||d<1)return send(OWNER_ID,"❌ Days?");const k=generateKey(d,OWNER_ID);ownerState=null;return send(OWNER_ID,"🔑 Key:\n\n"+k+"\n\n"+d+"d\n/key "+k,{reply_markup:ownerMenu});}
            else if(s.action==="adduser"){if(!s.step2){const t=parseInt(text);if(isNaN(t))return send(OWNER_ID,"❌");ownerState={action:"adduser",step2:true,tid:t};return send(OWNER_ID,"ID:"+t+"\nDays?");}else{const d=parseInt(text);if(isNaN(d)||d<1)return send(OWNER_ID,"❌");usersAccess[s.tid]=Date.now()+d*86400000;ownerState=null;send(OWNER_ID,"✅ "+s.tid+" "+d+"d",{reply_markup:ownerMenu});send(s.tid,"🎊 VIP! "+d+" days\n▶️ Start Prediction!");return;}}
            else if(s.action==="removeuser"){const t=parseInt(text);if(isNaN(t))return;if(Number(t)===Number(OWNER_ID))return send(OWNER_ID,"❌ Owner access cannot be removed.",{reply_markup:ownerMenu});const was=hasAccess(t);cleanupUserResources(t, true);ownerState=null;send(OWNER_ID,was?"🚫 Removed":"⚠️ Not active",{reply_markup:ownerMenu});if(was)send(t,"🔴 Access removed.");return;}
            else if(s.action==="settoken"){GLOBAL_TOKEN=text.trim().replace(/^Bearer\s+/i,"");ownerState=null;return send(OWNER_ID,"✅ Global Token set!",{reply_markup:ownerMenu});}
        }

        if(id===OWNER_ID&&ownerLoggedIn){
            if(text==="👥 All Users")    return send(OWNER_ID,"👥\n\n"+activeUsersList());
            if(text==="👮 All Admins")   return send(OWNER_ID,"👮\n\n"+adminList());
            if(text==="👤 Add Admin")    {ownerState={action:"addadmin"};return send(OWNER_ID,"User ID:");}
            if(text==="🗑 Remove Admin") {ownerState={action:"removeadmin"};return send(OWNER_ID,"Admin ID:");}
            if(text==="🔑 Generate Key") {ownerState={action:"genkey"};return send(OWNER_ID,"Days?");}
            if(text==="📋 All Keys")     return send(OWNER_ID,"📋\n\n"+allKeysList());
            if(text==="🟢 Add User")     {ownerState={action:"adduser"};return send(OWNER_ID,"User ID:");}
            if(text==="🔴 Remove User")  {ownerState={action:"removeuser"};return send(OWNER_ID,"User ID?");}
            if(text==="🔐 Set Token")    {ownerState={action:"settoken"};return send(OWNER_ID,"Token paste:");}
            if(text==="📊 All Status")    {
                const ids = Object.keys(usersAccess);
                if(ids.length === 0) return send(OWNER_ID, "No users found.");
                let report = "📊 TEAM MEMBERS ALL STATUS 📊\n\n";
                ids.forEach(uid => {
                    initUser(uid);
                    const pt = profitTrack[uid];
                    const st = autobetState[uid];
                    const pnlStr = (pt.pnl >= 0 ? "+" : "") + pt.pnl.toFixed(2);
                    report += `👤 ID: ${uid}\n`;
                    report += `💰 Total Bet: ₹${(pt.totalBetAmount || 0).toFixed(2)}\n`;
                    report += `📈 Profit: ₹${pnlStr}\n`;
                    report += `🎮 Level: L${st.level}\n`;
                    report += `🧾 History: ${Object.entries(st.levelHistory || {}).map(([level, count]) => level + ":" + count).join(" | ") || "None"}\n`;
                    report += `🏆 Wins by Level: ${st && autobetCfg[uid].mode === "COMBINED" ? "Size " + levelMapText(stats[uid].sizeLevelWins) + " | Number " + levelMapText(stats[uid].numberLevelWins) : levelMapText(stats[uid].levelWins)}\n`;
                    report += `📊 Win/Loss: ${pt.wins}W / ${pt.losses}L\n`;
                    report += `------------------------\n`;
                });
                return send(OWNER_ID, report);
            }
            if(text==="🚪 Owner Logout") {ownerLoggedIn=false;return send(OWNER_ID,"🔒 Out.",{reply_markup:userMenu(id)});}
        }

        if(isAdmin(id) && isAdminIn(id) && adminState[id]){
            const s = adminState[id];
            if(AB.includes(text)){ delete adminState[id]; }
            else if(s.action==="genkey"){const d=parseInt(text);if(isNaN(d)||d<1)return send(id,"❌ Days?");const k=generateKey(d,id);delete adminState[id];return send(id,"🔑 Key:\n\n"+k+"\n\n"+d+"d",{reply_markup:adminMenu});}
            else if(s.action==="adduser"){if(!s.step2){const t=parseInt(text);if(isNaN(t))return send(id,"❌");adminState[id]={action:"adduser",step2:true,tid:t};return send(id,"ID:"+t+"\nDays?");}else{const d=parseInt(text);if(isNaN(d)||d<1)return send(id,"❌");usersAccess[s.tid]=Date.now()+d*86400000;delete adminState[id];send(id,"✅ "+s.tid+" "+d+"d",{reply_markup:adminMenu});send(s.tid,"🎊 ACCESS! "+d+"d");return;}}
            else if(s.action==="removeuser"){const t=parseInt(text);if(isNaN(t))return;if(Number(t)===Number(OWNER_ID))return send(id,"❌ Owner access cannot be removed.",{reply_markup:adminMenu});const was=hasAccess(t);cleanupUserResources(t, true);delete adminState[id];send(id,was?"🚫 Removed":"⚠️ Not active",{reply_markup:adminMenu});if(was)send(t,"🔴 Removed.");return;}
        }

        if(hasAccess(id) && userAction[id]){
            const s = userAction[id];
            if(text === "🔙 Back") { delete userAction[id]; }
            else if(s.action === "setbase"){
                const v = parseInt(text);
                if(isNaN(v) || v < 1) return send(id, "❌ Invalid Amount! Min ₹1.");
                autobetCfg[id].baseBet = v;
                delete userAction[id];
                const a = MULT.slice(0, autobetCfg[id].maxLvl).map(m => v * m);
                return send(id, "✅ Base Bet Updated: ₹" + v + "\nMartingale: ₹" + a.join("→₹"), {reply_markup: autobetMenu});
            }
            else if(s.action === "setlvl"){
                const v = parseInt(text);
                if(isNaN(v) || v < 1 || v > 10) return send(id, "❌ Invalid Level! Enter 1-10.");
                autobetCfg[id].maxLvl = v;
                delete userAction[id];
                const a = MULT.slice(0, v).map(m => autobetCfg[id].baseBet * m);
                return send(id, "✅ Max Level Updated: L" + v + "\nMartingale: ₹" + a.join("→₹"), {reply_markup: autobetMenu});
            }
            else if(s.action === "setwloss"){
                const v = parseInt(text);
                if(isNaN(v) || v < 0) return send(id, "❌ Invalid Number!");
                autobetCfg[id].watchLoss = v;
                delete userAction[id];
                return send(id, "✅ Watch Loss Updated: " + v + "\n(Bot will wait for " + v + " losses before betting)", {reply_markup: autobetMenu});
            }
            else if(s.action === "setcustom"){
                const vals = text.split(/[, ]+/).map(v => parseInt(v.trim())).filter(v => !isNaN(v) && v > 0);
                if(vals.length === 0) return send(id, "❌ Invalid Format! Use: 1,4,7,9");
                autobetCfg[id].customBets = vals;
                autobetCfg[id].maxLvl = vals.length;
                delete userAction[id];
                return send(id, "✅ Custom Bets Updated!\nLevels: " + vals.length + "\nSequence: ₹" + vals.join(" → ₹"), {reply_markup: autobetMenu});
            }
        }

        if(isAdmin(id)&&isAdminIn(id)){
            if(text==="👥 Active Users") return send(id,"👥\n\n"+activeUsersList());
            if(text==="🔑 Generate Key") {adminState[id]={action:"genkey"};return send(id,"Days?");}
            if(text==="🟢 Add User")     {adminState[id]={action:"adduser"};return send(id,"User ID?");}
            if(text==="🔴 Remove User")  {adminState[id]={action:"removeuser"};return send(id,"User ID?");}
            if(text==="📋 All Keys")     return send(id,"📋\n\n"+allKeysList());
            if(text==="🚪 Admin Logout") {adminLoggedIn[id]=false;return send(id,"🔒 Out.",{reply_markup:userMenu(id)});}
        }

        if(text==="👑 Admin Panel"&&isAdmin(id)){
            if(!isAdminIn(id))return send(id,"Login:\n/adminlogin YOUR_PASS");
            return send(id,"👑 Admin",{reply_markup:adminMenu});
        }

        if(text==="🤖 AutoBet Setup"){
            if(!hasAccess(id))return send(id,"❌ No access.");
            const cfg=autobetCfg[id],creds=userCreds[id]||{};
            const amounts=cfg.customBets.slice(0,cfg.maxLvl);
            const targetProfit = Number(cfg.targetProfit) || 1000;
            return send(id,
"🤖 AUTOBET SETTINGS\n\n"+
"Status   : "+(cfg.enabled?"✅ ON":"❌ OFF")+"\n"+
"Token    : "+(getToken(id).length>20?"✅ SET":"❌ MISSING")+"\n"+
"AutoLogin: "+(creds.phone?"✅ "+creds.phone.slice(0,6)+"***":"❌ /setcreds")+"\n"+
"Mode     : "+modeLabel(cfg.mode)+"\n"+
    (cfg.mode === "COMBINED" ? "Size Seq : ₹"+cfg.customSizeBets.join(" → ₹")+"\nNum Seq  : ₹"+cfg.customNumberBets.join(" → ₹")+"\nRule     : 1 site size + 1 site number\n" : "Bet Seq  : ₹"+cfg.customBets.join(" → ₹")+"\n")+
"Watch    : "+(cfg.watch?"ON":"OFF")+"\n"+
"WatchLoss: "+cfg.watchLoss+" consecutive\n"+
"Base Bet : ₹"+cfg.baseBet+"\n"+
"Max Level: "+cfg.maxLvl+"\n"+
"Target   : ₹"+targetProfit+"\n\n"+
"Mart: ₹"+amounts.join("→₹")+"\n\n"+
"/setcreds 916381605525 PASSWORD\n"+
"/setmytoken TOKEN",
            {reply_markup:autobetMenu});
        }

        if(text==="✅ Enable AutoBet"){
            const creds=userCreds[id]||{};
            if(!getToken(id)&&!creds.phone)return send(id,"❌ /setcreds FULLPHONE PASSWORD\nor /setmytoken TOKEN");
            autobetCfg[id].enabled=true;
            if(!getToken(id)&&creds.phone){
                send(id,"🔄 Auto login...");
                const ok=await autoLogin(id,msg.chat.id,true);
                if(ok)send(id,"✅ AutoBet ON!\n₹"+autobetCfg[id].baseBet+" | Watch:"+(autobetCfg[id].watch?autobetCfg[id].watchLoss+"L":"OFF"),{reply_markup:userMenu(id)});
                else send(id,"⚠️ Login fail. /setcreds பண்ணு.",{reply_markup:autobetMenu});
            } else {
                send(id,"✅ AutoBet ON!\n₹"+autobetCfg[id].baseBet+" | Watch:"+(autobetCfg[id].watch?autobetCfg[id].watchLoss+"L":"OFF"),{reply_markup:userMenu(id)});
            }
            return;
        }
        if(text==="❌ Disable AutoBet"){autobetCfg[id].enabled=false;return send(id,"❌ AutoBet OFF",{reply_markup:userMenu(id)});}
        if(text==="👀 Watch Mode ON") {autobetCfg[id].watch=true;return send(id,"👀 Watch ON — "+autobetCfg[id].watchLoss+" losses → bet");}
        if(text==="👀 Watch Mode OFF"){autobetCfg[id].watch=false;return send(id,"👀 Watch OFF — Direct bet!");}
                        // --- CORRECTED SETTINGS HANDLERS ---
        if(text==="🎮 Mode: Big/Small"){
            delete userAction[id];
            autobetCfg[id].mode="SIZE";
            return send(id,"✅ Mode set: BIG/SMALL\nCategory bet enabled.",{reply_markup:autobetMenu});
        }
        if(text==="🔢 Mode: Number"){
            delete userAction[id];
            autobetCfg[id].mode="NUMBER";
            return send(id,"✅ Mode set: NUMBER\nExact Num_5 bet enabled.",{reply_markup:autobetMenu});
        }
        if(text==="🔀 Mode: BigSmall+Number"){
            delete userAction[id];
            autobetCfg[id].mode="COMBINED";
            return send(id,"✅ Mode set: BIG/SMALL + NUMBER\nOne site size bet + one site number bet.",{reply_markup:autobetMenu});
        }
        if(text==="💰 Set Base Bet"){userAction[id]={action:"setbase"};return send(id,"Enter base bet amount (e.g. 1):");}
        if(text==="📈 Set Max Level"){userAction[id]={action:"setlvl"};return send(id,"Enter max level (1-10):");}
                // --- SETTINGS TRIGGERS ---
        if(text==="🎯 Set Profit Target"){userAction[id]={action:"settarget"};return send(id,"Enter target profit (Min ₹10):");}
        if(text==="⏳ Set Section Delay"){userAction[id]={action:"setdelay"};return send(id,"Enter restart delay in MINUTES (e.g. 30):");}
        if(text==="🔀 Customize Bet"){
            if (autobetCfg[id].mode === "COMBINED") {
                userAction[id]={action:"setcombinedcustom",step:"size"};
                return send(id,"Enter BIG/SMALL level amounts (example: 1,2,4,8):");
            }
            userAction[id]={action:"setsinglecustom",mode:autobetCfg[id].mode};
            return send(id, autobetCfg[id].mode === "NUMBER" ? "Enter NUMBER bet level amounts (example: 1,9,81,729):" : "Enter BIG/SMALL bet level amounts (example: 1,2,4,8):");
        }
if(text==="🔢 Set Watch Losses"){
    userAction[id]={action:"setwloss"};
    return send(id,"Enter watch loss count (e.g. 3):");
}

        // --- INPUT SAVING LOGIC ---
        if(hasAccess(id) && userAction[id]){
            const s = userAction[id];
            if(text === "🔙 Back") { delete userAction[id]; }
            
            else if(s.action === "settarget"){
                const v = Number(text);
                if(!Number.isFinite(v) || v < 10) return send(id, "❌ Min ₹10 kudunga!");
                autobetCfg[id].targetProfit = v;
                delete userAction[id];
                return send(id, "✅ Profit target set to ₹"+v, {reply_markup: autobetMenu});
            }
            else if(s.action === "setdelay"){
                const v = parseInt(text);
                if(isNaN(v) || v < 1) return send(id, "❌ Invalid minutes!");
                autobetCfg[id].restartDelay = v;
                delete userAction[id];
                return send(id, "✅ Section delay set to "+v+" minutes", {reply_markup: autobetMenu});
            }
            else if(s.action === "setsinglecustom"){
                const vals = text.split(/[, ]+/).map(v => parseInt(v.trim())).filter(v => Number.isInteger(v) && v > 0);
                if(vals.length === 0) return send(id, "❌ Format error! Use: 1,2,4,8");
                autobetCfg[id].customBets = vals;
                if (s.mode === "NUMBER") autobetCfg[id].customNumberBets = [...vals];
                else autobetCfg[id].customSizeBets = [...vals];
                autobetCfg[id].maxLvl = vals.length;
                delete userAction[id];
                return send(id, "✅ "+(s.mode === "NUMBER" ? "NUMBER" : "BIG/SMALL")+" custom bets updated!\nSequence: ₹"+vals.join(" → ₹"), {reply_markup: autobetMenu});
            }
            else if(s.action === "setcombinedcustom"){
                const vals = text.split(/[, ]+/).map(v => parseInt(v.trim())).filter(v => Number.isInteger(v) && v > 0);
                if(vals.length === 0) return send(id, "❌ Format error! Use: 1,2,4,8");
                if(s.step === "size"){
                    autobetCfg[id].customSizeBets = vals;
                    userAction[id] = {action:"setcombinedcustom", step:"number", sizeVals:vals};
                    return send(id, "✅ Size levels saved. Now enter NUMBER level amounts (example: 1,9,81,729):");
                }
                autobetCfg[id].customNumberBets = vals;
                autobetCfg[id].maxLvl = Math.max((userAction[id].sizeVals || []).length, vals.length);
                delete userAction[id];
                return send(id, "✅ Combined custom bets updated!\nSize: ₹"+autobetCfg[id].customSizeBets.join(" → ₹")+"\nNumber: ₹"+vals.join(" → ₹")+"\nAny win resets both to L1.", {reply_markup: autobetMenu});
            }
            // ... matha setbase, setlvl code-um ithu kulla thaan varum
        }

        // --- IMPORTANT: AWAIT ADDED ---
        if(text==="📊 AutoBet Status") return await autobetStatus(msg.chat.id,id);

        if(text==="🔙 Back")return await send(id,"Main Menu",{reply_markup:userMenu(id)});

        if (text === "🔑 My Token") {
            if (!hasAccess(id)) return send(id, "❌ No access.");

            const tok = getToken(id);
            const creds = userCreds[id] || {};
            const tokenSaved = tok && tok.length > 20;
            const tokenPreview = tokenSaved ? "..." + tok.slice(-12) : "❌ Not saved";
            const loginStatus = creds.phone ? "✅ " + creds.phone.slice(0, 6) + "***" : "❌ Not configured";

            if (!tokenSaved) {
                return send(
                    id,
                    "🔑 MY TOKEN\n\n" +
                    "Token: ❌ Not saved\n" +
                    "Login: " + loginStatus + "\n\n" +
                    "Save your token using:\n" +
                    "/setmytoken YOUR_TOKEN",
                    { reply_markup: userMenu(id) }
                );
            }

            return send(
                id,
                "🔑 MY TOKEN\n\n" +
                "Token: ✅ Saved\n" +
                "Preview: " + tokenPreview + "\n" +
                "Login: " + loginStatus + "\n\n" +
                "To replace it, use:\n" +
                "/setmytoken NEW_TOKEN",
                { reply_markup: userMenu(id) }
            );
        }

        if(text==="⏹ Stop Prediction"){
            if(!running[id]) return send(msg.chat.id,"⚠️ Bot is not running.",{reply_markup:userMenu(id)});
            running[id]=false;
            clearUserTimers(id);
            await closeSiteReader();
            return send(msg.chat.id,"⏹ Prediction stopped. Browser memory released; no new bets or result checks will be scheduled.",{reply_markup:userMenu(id)});
        }

      if(text==="▶️ Start Prediction"){
            if(!hasAccess(id))return send(msg.chat.id,"❌ No access!\n📩 "+ADMIN_HANDLE+"\nID: "+id);
            if(running[id])return send(msg.chat.id,"⚠️ Already running!");

            clearUserTimers(id);
            running[id]=true;sentPeriods[id]=new Set();
            autobetState[id]={...(autobetState[id]||{}),level:1,sizeLevel:1,numberLevel:1,consecutiveLoss:0,inMart:false,lastWinLevel:null,lastWinMode:null};

            // Load previous B/S history from API
            const prevList = await fetchList();
            initState(id);

            if (prevList && prevList.length >= 4) {
                // Build B/S history
                userStates[id].resultHistory = buildBSFromList(prevList, 15);
                await send(msg.chat.id, "📋 Loaded history: " + (userStates[id].resultHistory || []).join(''));


            }

            const cfg=autobetCfg[id];
            await send(msg.chat.id,
"🚀 ENGINE ON!\n\nAutoBet: "+(cfg.enabled?"✅ ON":"❌ OFF")+"\nMode   : "+modeLabel(cfg.mode)+"\nWatch  : "+(cfg.watch?"ON ("+cfg.watchLoss+"L)":"OFF")+"\nBase   : ₹"+cfg.baseBet+" | MaxLvl: "+cfg.maxLvl
            );
            runPredict(id,msg.chat.id);
        }
        if(text==="📊 Stats")  showStats(msg.chat.id,id);
        if(text==="💰 Profit") profitReport(msg.chat.id,id);
        if(text==="📩 Contact") send(msg.chat.id,"📩 "+ADMIN_HANDLE+"\nID: "+id);
    });
}
const shutdown = async (signal) => {
    console.log(`[SHUTDOWN] ${signal}`);
    for (const id of Object.keys(running)) { running[id] = false; clearUserTimers(id); }
    await closeSiteReader();
    try { if (bot) await bot.stopPolling(); } catch {}
    process.exit(0);
};
process.once('SIGTERM', () => shutdown('SIGTERM'));
process.once('SIGINT', () => shutdown('SIGINT'));
startBot();
