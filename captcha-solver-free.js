/**
 * ============================================================
 *  FREE CAPTCHA SOLVER FOR goaokk.com / 13llottery LOGIN
 *  (Direct Navigation Version)
 * ============================================================
 */

const puppeteer = require('puppeteer');
const { PNG } = require('pngjs');
const axios = require('axios');

// ============================================================
//  HELPER FUNCTIONS
// ============================================================

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function randomInt(min, max) {
    return Math.floor(Math.random() * (max - min + 1)) + min;
}

// ============================================================
//  CAPTCHA IMAGE EXTRACTION
// ============================================================

async function extractCaptchaImages(page) {
    const imageData = await page.evaluate(() => {
        const bgImg = document.querySelector('.captcha_background');
        const sliderImg = document.querySelector('.captcha_slider');
        
        if (!bgImg || !sliderImg) return null;
        
        const bgContainer = bgImg.parentElement;
        const bgRect = bgContainer ? bgContainer.getBoundingClientRect() : bgImg.getBoundingClientRect();
        const sliderRect = sliderImg.getBoundingClientRect();
        
        return {
            bgSrc: bgImg.src,
            sliderSrc: sliderImg.src,
            displayWidth: bgRect.width,
            displayHeight: bgRect.height,
            sliderDisplayLeft: sliderRect.left,
            sliderDisplayTop: sliderRect.top,
        };
    });
    
    if (!imageData || !imageData.bgSrc || !imageData.sliderSrc) {
        return null;
    }
    
    let bgData, pieceData;
    
    try {
        const bgResponse = await axios.get(imageData.bgSrc, {
            responseType: 'arraybuffer',
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                'Referer': 'https://goaokk.com/',
                'Origin': 'https://goaokk.com'
            }
        });
        const bgPng = PNG.sync.read(Buffer.from(bgResponse.data));
        bgData = { width: bgPng.width, height: bgPng.height, data: bgPng.data };
        
        const pieceResponse = await axios.get(imageData.sliderSrc, {
            responseType: 'arraybuffer',
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                'Referer': 'https://goaokk.com/',
                'Origin': 'https://goaokk.com'
            }
        });
        const piecePng = PNG.sync.read(Buffer.from(pieceResponse.data));
        pieceData = { width: piecePng.width, height: piecePng.height, data: piecePng.data };
    } catch (err) {
        console.error('[CAPTCHA] Failed to download images via axios:', err.message);
        
        try {
            const bgBase64 = await page.evaluate((src) => {
                return new Promise((resolve) => {
                    const img = new Image();
                    img.onload = () => {
                        const canvas = document.createElement('canvas');
                        canvas.width = img.width;
                        canvas.height = img.height;
                        canvas.getContext('2d').drawImage(img, 0, 0);
                        resolve(canvas.toDataURL('image/png').split(',')[1]);
                    };
                    img.onerror = () => resolve(null);
                    img.src = src;
                });
            }, imageData.bgSrc);
            
            const pieceBase64 = await page.evaluate((src) => {
                return new Promise((resolve) => {
                    const img = new Image();
                    img.onload = () => {
                        const canvas = document.createElement('canvas');
                        canvas.width = img.width;
                        canvas.height = img.height;
                        canvas.getContext('2d').drawImage(img, 0, 0);
                        resolve(canvas.toDataURL('image/png').split(',')[1]);
                    };
                    img.onerror = () => resolve(null);
                    img.src = src;
                });
            }, imageData.sliderSrc);
            
            if (bgBase64 && pieceBase64) {
                const bgPng = PNG.sync.read(Buffer.from(bgBase64, 'base64'));
                bgData = { width: bgPng.width, height: bgPng.height, data: bgPng.data };
                const piecePng = PNG.sync.read(Buffer.from(pieceBase64, 'base64'));
                pieceData = { width: piecePng.width, height: piecePng.height, data: piecePng.data };
            }
        } catch (err2) {
            console.error('[CAPTCHA] Fallback also failed:', err2.message);
            return null;
        }
    }
    
    return {
        bgData,
        pieceData,
        displayWidth: imageData.displayWidth,
        displayHeight: imageData.displayHeight,
    };
}

// ============================================================
//  GAP DETECTION (Template Matching)
// ============================================================

function solveGapPosition(bgData, pieceData, displayWidth, displayHeight) {
    const { width: bgW, height: bgH, data: bgPixels } = bgData;
    const { width: pieceW, height: pieceH, data: piecePixels } = pieceData;
    
    const scaleX = displayWidth / bgW;
    
    const pieceOpaquePixels = [];
    let contentMinX = pieceW, contentMaxX = 0;
    let contentMinY = pieceH, contentMaxY = 0;
    
    for (let y = 0; y < pieceH; y++) {
        for (let x = 0; x < pieceW; x++) {
            const idx = (y * pieceW + x) * 4;
            const alpha = piecePixels[idx + 3];
            if (alpha > 80) {
                pieceOpaquePixels.push({
                    x, y,
                    r: piecePixels[idx] / 255,
                    g: piecePixels[idx + 1] / 255,
                    b: piecePixels[idx + 2] / 255,
                });
                contentMinX = Math.min(contentMinX, x);
                contentMaxX = Math.max(contentMaxX, x);
                contentMinY = Math.min(contentMinY, y);
                contentMaxY = Math.max(contentMaxY, y);
            }
        }
    }
    
    if (pieceOpaquePixels.length < 50) return -1;
    
    const bgR = new Float32Array(bgW * bgH);
    const bgG = new Float32Array(bgW * bgH);
    const bgB = new Float32Array(bgW * bgH);
    
    for (let i = 0; i < bgW * bgH; i++) {
        bgR[i] = bgPixels[i * 4] / 255;
        bgG[i] = bgPixels[i * 4 + 1] / 255;
        bgB[i] = bgPixels[i * 4 + 2] / 255;
    }
    
    let bestX = 0;
    let bestScore = Infinity;
    
    for (let x = 0; x <= bgW - pieceW; x += 2) {
        let totalDiff = 0;
        let count = 0;
        
        for (const pp of pieceOpaquePixels) {
            const bgX = x + pp.x;
            const bgY = pp.y;
            
            if (bgX >= 0 && bgX < bgW && bgY >= 0 && bgY < bgH) {
                const bgIdx = bgY * bgW + bgX;
                const dr = bgR[bgIdx] - pp.r;
                const dg = bgG[bgIdx] - pp.g;
                const db = bgB[bgIdx] - pp.b;
                totalDiff += Math.sqrt(dr * dr + dg * dg + db * db);
                count++;
            }
        }
        
        if (count > 0) {
            const avgDiff = totalDiff / count;
            if (avgDiff < bestScore) {
                bestScore = avgDiff;
                bestX = x;
            }
        }
    }
    
    const refineMin = Math.max(0, bestX - 15);
    const refineMax = Math.min(bgW - pieceW, bestX + 15);
    
    for (let x = refineMin; x <= refineMax; x++) {
        let totalDiff = 0;
        let count = 0;
        
        for (const pp of pieceOpaquePixels) {
            const bgX = x + pp.x;
            const bgY = pp.y;
            
            if (bgX >= 0 && bgX < bgW && bgY >= 0 && bgY < bgH) {
                const bgIdx = bgY * bgW + bgX;
                const dr = bgR[bgIdx] - pp.r;
                const dg = bgG[bgIdx] - pp.g;
                const db = bgB[bgIdx] - pp.b;
                totalDiff += Math.sqrt(dr * dr + dg * dg + db * db);
                count++;
            }
        }
        
        if (count > 0) {
            const avgDiff = totalDiff / count;
            if (avgDiff < bestScore) {
                bestScore = avgDiff;
                bestX = x;
            }
        }
    }
    
    const dragDistance = Math.round(bestX * scaleX);
    return dragDistance;
}

// ============================================================
//  HUMAN-LIKE DRAG SIMULATION
// ============================================================

async function performHumanDrag(page, dragDistance) {
    const handlerPos = await page.evaluate(() => {
        const handler = document.querySelector('.captcha_handler');
        if (!handler) return null;
        const rect = handler.getBoundingClientRect();
        return {
            x: rect.x + rect.width / 2,
            y: rect.y + rect.height / 2,
        };
    });
    
    if (!handlerPos) return false;
    
    const startX = handlerPos.x;
    const startY = handlerPos.y;
    const totalSteps = randomInt(50, 80);
    
    await page.mouse.move(startX, startY);
    await sleep(randomInt(200, 500));
    
    const dragResult = await page.evaluate(({ dragDistance, totalSteps }) => {
        return new Promise((resolve) => {
            const handler = document.querySelector('.captcha_handler');
            if (!handler) {
                resolve({ success: false, error: 'handler not found' });
                return;
            }
            
            const rect = handler.getBoundingClientRect();
            const cx = rect.x + rect.width / 2;
            const cy = rect.y + rect.height / 2;
            const endX = cx + dragDistance;
            
            const points = [];
            const jitter = (min, max) => min + Math.random() * (max - min);
            
            for (let i = 1; i <= totalSteps; i++) {
                const progress = i / totalSteps;
                let eased;
                
                if (progress < 0.05) {
                    eased = Math.pow(progress / 0.05, 2) * 0.05;
                } else if (progress < 0.2) {
                    const p = (progress - 0.05) / 0.15;
                    eased = 0.05 + p * p * 0.2;
                } else if (progress < 0.65) {
                    eased = 0.25 + ((progress - 0.2) / 0.45) * 0.4;
                } else if (progress < 0.85) {
                    const p = (progress - 0.65) / 0.20;
                    eased = 0.65 + (1 - Math.pow(1 - p, 2)) * 0.2;
                } else {
                    const p = (progress - 0.85) / 0.15;
                    eased = 0.85 + Math.pow(p, 2) * 0.15;
                }
                
                const px = cx + dragDistance * eased;
                const py = cy + jitter(-3, 3);
                points.push({ x: px, y: py, progress });
            }
            
            let pointIndex = 0;
            const dispatchNext = () => {
                if (pointIndex >= points.length) {
                    setTimeout(() => {
                        const upEvent = new PointerEvent('pointerup', {
                            bubbles: true, cancelable: true,
                            clientX: endX, clientY: cy, screenX: endX, screenY: cy,
                            pointerId: 1, pointerType: 'mouse'
                        });
                        handler.dispatchEvent(upEvent);
                        
                        const mouseUpEvent = new MouseEvent('mouseup', {
                            bubbles: true, cancelable: true, clientX: endX, clientY: cy
                        });
                        document.dispatchEvent(mouseUpEvent);
                        
                        setTimeout(() => resolve({ success: true }), 500);
                    }, 200);
                    return;
                }
                
                const point = points[pointIndex];
                let delay = 5 + Math.random() * 10;
                
                setTimeout(() => {
                    const moveEvent = new MouseEvent('mousemove', {
                        bubbles: true, cancelable: true,
                        clientX: point.x, clientY: point.y
                    });
                    document.dispatchEvent(moveEvent);
                    
                    pointIndex++;
                    dispatchNext();
                }, delay);
            };
            
            const downEvent = new PointerEvent('pointerdown', {
                bubbles: true, cancelable: true,
                clientX: cx, clientY: cy, screenX: cx, screenY: cy,
                pointerId: 1, pointerType: 'mouse'
            });
            handler.dispatchEvent(downEvent);
            
            const mouseDownEvent = new MouseEvent('mousedown', {
                bubbles: true, cancelable: true, clientX: cx, clientY: cy
            });
            handler.dispatchEvent(mouseDownEvent);
            
            setTimeout(() => dispatchNext(), 100);
        });
    }, { dragDistance, totalSteps });
    
    return dragResult.success;
}

async function isCaptchaVisible(page) {
    return await page.evaluate(() => {
        const bg = document.querySelector('.captcha_background');
        const slider = document.querySelector('.captcha_slider');
        if (!bg || !slider) return false;
        
        const overlay = document.querySelector('.van-overlay');
        if (overlay) {
            const style = window.getComputedStyle(overlay);
            if (style.display === 'none' || style.visibility === 'hidden') return false;
        }
        
        return true;
    });
}

async function solveCaptcha(page) {
    const images = await extractCaptchaImages(page);
    if (!images) return -1;
    return solveGapPosition(images.bgData, images.pieceData, images.displayWidth, images.displayHeight);
}

// ============================================================
//  COMPLETE LOGIN WITH DIRECT URL NAVIGATION TO WINGO 30S
// ============================================================

async function captchaLogin(userId, chatId, phone, password, bot, logBoth) {
    console.log(`[LOGIN] Starting captcha login for user ${userId}...`);
   let browser;
     try {
         browser = await puppeteer.launch({
             headless: true, 
             args: ['--no-sandbox', '--disable-setuid-sandbox', '--single-process', '--disable-gpu']
         });
         const page = await browser.newPage();
         await page.setDefaultNavigationTimeout(90000); 
         await page.setUserAgent('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36');
 
         let capturedToken = null;
         const normalizeCapturedToken = (value) => {
             if (value && typeof value === 'object') {
                 value = value.token || value.accessToken || value.access_token ||
                     value.jwt || value.data?.token || value.data?.accessToken ||
                     value.data?.access_token || value.data?.jwt || '';
             }
             const token = String(value || '').replace(/^Bearer\s+/i, '').trim();
             return token.length >= 20 ? token : null;
         };

         await page.setRequestInterception(true);
         page.on('request', (req) => {
             try {
                 const auth = req.headers()['authorization'] || req.headers()['x-auth-token'];
                 const token = normalizeCapturedToken(auth);
                 if (token) capturedToken = token;
                 req.continue();
             } catch (_) {
                 try { req.continue(); } catch (_) {}
             }
         });

         // Some versions of the site return the token in a JSON login/balance response
         // instead of placing it in the Authorization request header.
         page.on('response', async (response) => {
             if (capturedToken) return;
             const type = response.headers()['content-type'] || '';
             if (!type.includes('json')) return;
             try {
                 const body = await response.json();
                 const token = normalizeCapturedToken(body);
                 if (token) capturedToken = token;
             } catch (_) {}
         });
        
        // Navigate to login page
        await page.goto('https://13llottery.com/login', { 
            waitUntil: 'domcontentloaded', 
            timeout: 90000 
        });
        
        await page.waitForSelector('input', { timeout: 30000 });
        await sleep(1000);

        const visibleInputs = await page.$$('input');
        const isVisible = async (handle) => {
            try {
                return await handle.evaluate(el => {
                    const s = getComputedStyle(el);
                    const r = el.getBoundingClientRect();
                    return s.display !== 'none' && s.visibility !== 'hidden' && r.width > 0 && r.height > 0;
                });
            } catch (_) {
                return false;
            }
        };

        const candidates = [];
        for (const handle of visibleInputs) {
            if (await isVisible(handle)) candidates.push(handle);
        }

        const candidateMeta = [];
        for (const handle of candidates) {
            const meta = await handle.evaluate(el => ({
                type: String(el.getAttribute('type') || '').toLowerCase(),
                name: String(el.getAttribute('name') || '').toLowerCase(),
                placeholder: String(el.getAttribute('placeholder') || '').toLowerCase()
            }));
            candidateMeta.push({ handle, ...meta });
        }

        const safePhone = candidateMeta.find(item =>
            item.type !== 'password' &&
            /phone|mobile|number|username|account/.test(`${item.name} ${item.placeholder}`)
        ) || candidateMeta.find(item => item.type !== 'password');
        
        const safePhoneInput = safePhone?.handle;
        if (!safePhoneInput) throw new Error('Phone input not found');
        
        await safePhoneInput.click({ clickCount: 3 });
        await safePhoneInput.press('Backspace');
        await safePhoneInput.type(String(phone), { delay: 50 });

        await sleep(500);

        const passwordInput = candidateMeta.find(item => item.type === 'password')?.handle ||
            candidateMeta.find(item => item.handle !== safePhoneInput)?.handle;
            
        if (!passwordInput) throw new Error('Password input not found');
        
        await passwordInput.click({ clickCount: 3 });
        await passwordInput.press('Backspace');
        await passwordInput.type(String(password), { delay: 50 });
        
        // Click Login button
        await page.evaluate(() => {
            const btns = Array.from(document.querySelectorAll('button'));
            const loginBtn = btns.find(b => b.innerText.includes('Log in') || b.innerText.includes('Login'));
            if (loginBtn) loginBtn.click();
            else document.querySelector('form')?.submit();
        });
        
        await sleep(2000);
        
        let captchaDetected = false;
        for (let i = 0; i < 20; i++) {
            captchaDetected = await isCaptchaVisible(page);
            if (captchaDetected) break;
            await sleep(500);
        }
        
        if (captchaDetected) {
            console.log('[LOGIN] Captcha detected! Solving...');
            const dragDistance = await solveCaptcha(page);
            
            if (dragDistance < 10 || dragDistance > 330) {
                if (chatId) await logBoth(chatId, '❌ Captcha solve failed - invalid distance');
                return false;
            }
            
            const dragged = await performHumanDrag(page, dragDistance);
            if (!dragged) {
                if (chatId) await logBoth(chatId, '❌ Captcha solve failed - drag error');
                return false;
            }
            
            await sleep(3000);
            if (await isCaptchaVisible(page)) {
                if (chatId) await logBoth(chatId, '❌ Captcha solve failed - server rejected');
                return false;
            }
            console.log('[LOGIN] ✅ Captcha solved successfully!');
        }
        
        // === DIRECT NAVIGATION TO WINGO 30S URL ===
        try {
            await page.waitForNavigation({ waitUntil: 'domcontentloaded', timeout: 20000 });
        } catch (e) {}
        await sleep(3000);
        
        console.log('[LOGIN] Navigating directly to WinGo 30S page via URL...');
        await page.goto('https://13llottery.com/WinGo/WinGo_30S', {
            waitUntil: 'domcontentloaded',
            timeout: 10000
        });
        await sleep(3000);
        
         // === TOKEN CAPTURE (same as your original code) ===
        for (let i = 0; i < 50; i++) {
            if (capturedToken) break;
            await new Promise(r => setTimeout(r, 1000));
        }
        
        // Last fallback: authenticated SPAs often keep the token in browser storage.
        if (!capturedToken) {
            try {
                const storageToken = await page.evaluate(() => {
                    const values = [];
                    for (const storage of [localStorage, sessionStorage]) {
                        for (let i = 0; i < storage.length; i++) {
                            const key = storage.key(i) || '';
                            const value = storage.getItem(key) || '';
                            if (/token|auth|jwt|access/i.test(key)) values.push(value);
                        }
                    }
                    return values;
                });
                for (const value of storageToken || []) {
                    const token = normalizeCapturedToken(value);
                    if (token) { capturedToken = token; break; }
                }
            } catch (_) {}
        }

        if (capturedToken) {
            console.log('[LOGIN] ✅ Token captured and returned directly to bot.js');
            if (chatId) await logBoth(chatId, `✅ [SUCCESS] Token captured for user ${userId}!`);
            return capturedToken;
        } else {
            console.error('[LOGIN] ❌ Token not found');
            if (chatId) await logBoth(chatId, `❌ Login failed - token not captured for user ${userId}`, true);
            return false;
        }
        
    } catch (err) {
        console.error(`[LOGIN] Error: ${err.message}`);
        if (chatId) await logBoth(chatId, `❌ Login Error for user ${userId}: ${err.message}`, true);
        return false;
    } finally {
        if (browser) await browser.close();
    }
}

// ============================================================
//  EXPORTS
// ============================================================

module.exports = {
    captchaLogin,
    solveCaptcha,
    solveGapPosition,
    performHumanDrag,
    isCaptchaVisible,
    extractCaptchaImages,
};
