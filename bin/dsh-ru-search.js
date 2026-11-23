#!/usr/bin/env node
// dsh-ru-search — MCP-сервер «yandex» для dsh (stdio, без зависимостей): поиск Яндекса без API
// и загрузка страниц. Запросы выглядят как запросы Яндекс.Браузера (UA, client hints,
// Referer с yandex.ru), TLS-доверие расширено корневыми сертификатами Минцифры
// (Russian Trusted Root/Sub CA) — для сайтов с такими сертификатами.
//
// Честные ограничения:
//  - маскировка на уровне HTTP-заголовков; TLS-отпечаток остаётся отпечатком Node.js;
//  - капчу (SmartCaptcha) сервер не решает и не обходит — возвращает понятную ошибку;
//  - автоматизированные запросы к yandex.ru противоречат его правилам использования.
'use strict';
const https = require('https');
const http = require('http');
const tls = require('tls');
const zlib = require('zlib');
const fs = require('fs');
const path = require('path');

const os = require('os');
const CERT_DIR = process.env.YA_CERT_DIR || path.join(os.homedir(), '.dsh-ru-search', 'certs');
const YB_VER = process.env.YA_BROWSER_VERSION || '25.8.0.0';
const CH_VER = process.env.YA_CHROMIUM_VERSION || '138';
const UA = process.env.YA_USER_AGENT ||
  `Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${CH_VER}.0.0.0 YaBrowser/${YB_VER} Safari/537.36`;
const REGION = process.env.YA_REGION || '213'; // lr: 213 — Москва
const MAX_BYTES = 3 * 1024 * 1024;
const TIMEOUT_MS = 20000;

// ---------- TLS: системные корни + Минцифры ----------
function loadCa() {
  const extra = [];
  try {
    for (const f of fs.readdirSync(CERT_DIR)) {
      if (/\.(crt|cer)$/i.test(f)) extra.push(fs.readFileSync(path.join(CERT_DIR, f), 'utf8'));
    }
  } catch (_) { /* каталога нет — работаем только с системными корнями */ }
  return { ca: [...tls.rootCertificates, ...extra], extraCount: extra.length };
}
let { ca: CA, extraCount } = loadCa();
let agent = new https.Agent({ ca: CA, keepAlive: true, maxSockets: 4 });

// ---------- AIA: докачка недостающих промежуточных сертификатов ----------
// Часть сайтов (например np-sr.ru) не отдаёт промежуточный сертификат; браузеры докачивают его по
// ссылке «CA Issuers» из сертификата. Докачанный сертификат принимается ТОЛЬКО если он подписан
// доверенным корнем или уже принятым промежуточным (иначе подмена AIA дала бы доверенный сертификат).
const { X509Certificate } = require('crypto');
let rootObjs = null;
const aiaAccepted = new Map(); // fingerprint -> PEM
function trustedObjs() {
  if (!rootObjs) { rootObjs = []; for (const pem of CA) { try { rootObjs.push(new X509Certificate(pem)); } catch (_) {} } }
  return [...rootObjs, ...[...aiaAccepted.values()].map((p) => new X509Certificate(p))];
}
const derToPem = (der) => '-----BEGIN CERTIFICATE-----\n' + der.toString('base64').replace(/(.{64})/g, '$1\n') + '\n-----END CERTIFICATE-----\n';
function plainGet(u, hops = 3) {
  return new Promise((resolve, reject) => {
    const url = new URL(u);
    if (!/^https?:$/.test(url.protocol)) return reject(new Error('AIA: схема'));
    (url.protocol === 'https:' ? https : http).get(url, { timeout: 10000, headers: { 'User-Agent': 'Mozilla/5.0' } }, (res) => {
      if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location && hops > 0) { res.resume(); return plainGet(new URL(res.headers.location, url).toString(), hops - 1).then(resolve, reject); }
      const ch = []; let n = 0;
      res.on('data', (c) => { n += c.length; if (n > 100000) res.destroy(new Error('AIA: слишком большой ответ')); else ch.push(c); });
      res.on('end', () => resolve(Buffer.concat(ch)));
      res.on('error', reject);
    }).on('error', reject).on('timeout', function () { this.destroy(new Error('AIA: таймаут')); });
  });
}
function peerChain(host, port) {
  return new Promise((resolve, reject) => {
    const sock = tls.connect({ host, port, servername: host, rejectUnauthorized: false, timeout: 10000 }, () => {
      const out = []; let c = sock.getPeerCertificate(true);
      for (let i = 0; c && c.raw && i < 6; i++) { out.push(c.raw); if (!c.issuerCertificate || c.issuerCertificate === c) break; c = c.issuerCertificate; }
      sock.end(); resolve(out);
    });
    sock.on('error', reject).on('timeout', () => sock.destroy(new Error('AIA: таймаут TLS')));
  });
}
// true, если цепочка достроена до доверенного корня и добавлен хотя бы один сертификат.
// В доверенные кандидаты попадают только после успешной проверки ВСЕЙ цепочки.
async function fetchIntermediates(host, port) {
  const chain = (await peerChain(host, port)).map((d) => new X509Certificate(d));
  if (!chain.length) return false;
  const pending = [];
  let cur = chain[0];
  for (let depth = 0; depth < 4; depth++) {
    if (trustedObjs().some((t) => cur.checkIssued(t) && cur.verify(t.publicKey))) {
      let added = false;
      for (const c of pending) if (!aiaAccepted.has(c.fingerprint256)) { aiaAccepted.set(c.fingerprint256, c.toString()); added = true; }
      return added;
    }
    let cand = chain.find((c) => c !== cur && cur.checkIssued(c) && cur.verify(c.publicKey));
    if (!cand) {
      const m = /CA Issuers - URI:(\S+)/.exec(cur.infoAccess || '');
      if (!m) return false;
      const body = await plainGet(m[1]);
      try { cand = new X509Certificate(body); } catch (_) { try { cand = new X509Certificate(body.toString('utf8')); } catch (__) { return false; } }
      if (!(cur.checkIssued(cand) && cur.verify(cand.publicKey))) return false;
    }
    pending.push(cand);
    cur = cand;
  }
  return false;
}
// Корни Минцифры скачиваются при первом вызове, если их нет в CERT_DIR (YA_NO_CERT_DOWNLOAD=1 — отключить).
let certsChecked = false;
async function ensureCerts() {
  if (certsChecked) return; certsChecked = true;
  if (process.env.YA_NO_CERT_DOWNLOAD === '1') return;
  const need = ['root', 'sub'].filter((n) => !fs.existsSync(path.join(CERT_DIR, `russian_trusted_${n}_ca.crt`)));
  if (!need.length) return;
  try {
    fs.mkdirSync(CERT_DIR, { recursive: true });
    for (const n of need) {
      const t = (await plainGet(`https://gu-st.ru/content/lending/russian_trusted_${n}_ca_pem.crt`)).toString('utf8');
      new X509Certificate(t); // бросит ошибку, если это не сертификат
      fs.writeFileSync(path.join(CERT_DIR, `russian_trusted_${n}_ca.crt`), t.endsWith('\n') ? t : t + '\n');
    }
  } catch (e) { process.stderr.write(`[dsh-ru-search] не удалось скачать корни Минцифры: ${e.message}\n`); return; }
  ({ ca: CA, extraCount } = loadCa()); rootObjs = null; rebuildAgent();
  process.stderr.write(`[dsh-ru-search] корни Минцифры сохранены в ${CERT_DIR}\n`);
}
function rebuildAgent() { agent = new https.Agent({ ca: [...CA, ...aiaAccepted.values()], keepAlive: true, maxSockets: 4 }); }
// только по явному запросу (insecure:true): сайт без валидного сертификата (просрочен, заглушка хостинга)
const agentInsecure = new https.Agent({ rejectUnauthorized: false, keepAlive: true, maxSockets: 2 });

// ---------- HTTP как Яндекс.Браузер ----------
const jar = new Map(); // host -> Map(name -> value)
function cookieHeader(host) {
  const m = jar.get(host);
  return m && m.size ? [...m].map(([k, v]) => `${k}=${v}`).join('; ') : '';
}
function storeCookies(host, setCookie) {
  if (!setCookie) return;
  const m = jar.get(host) || new Map();
  for (const c of [].concat(setCookie)) {
    const [kv] = c.split(';');
    const i = kv.indexOf('=');
    if (i > 0) m.set(kv.slice(0, i).trim(), kv.slice(i + 1).trim());
  }
  jar.set(host, m);
}
function browserHeaders(url, referer) {
  const sameSite = referer && new URL(referer).hostname.split('.').slice(-2).join('.') === url.hostname.split('.').slice(-2).join('.');
  const h = {
    'User-Agent': UA,
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
    'Accept-Language': 'ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7',
    'Accept-Encoding': 'gzip, deflate, br',
    'sec-ch-ua': `"Not)A;Brand";v="8", "Chromium";v="${CH_VER}", "YaBrowser";v="${YB_VER.split('.').slice(0, 2).join('.')}", "Yowser";v="2.5"`,
    'sec-ch-ua-mobile': '?0',
    'sec-ch-ua-platform': '"Windows"',
    'Sec-Fetch-Dest': 'document',
    'Sec-Fetch-Mode': 'navigate',
    'Sec-Fetch-Site': referer ? (sameSite ? 'same-origin' : 'cross-site') : 'none',
    'Sec-Fetch-User': '?1',
    'Upgrade-Insecure-Requests': '1',
    'Cache-Control': 'max-age=0',
    'Connection': 'keep-alive',
  };
  if (referer) h['Referer'] = referer;
  const ck = cookieHeader(url.hostname);
  if (ck) h['Cookie'] = ck;
  return h;
}

function get(urlStr, { referer = 'https://yandex.ru/', hops = 6, insecure = false, aiaTried = false } = {}) {
  return new Promise((resolve, reject) => {
    let url;
    try { url = new URL(urlStr); } catch (e) { return reject(new Error('Некорректный URL: ' + urlStr)); }
    // «example.ru.» (точка на конце) уходит в SNI как есть, и многие виртуальные хосты
    // отдают сертификат-заглушку (ERR_TLS_CERT_ALTNAME_INVALID) — браузеры точку убирают
    if (url.hostname.endsWith('.')) url.hostname = url.hostname.replace(/\.+$/, '');
    if (!/^https?:$/.test(url.protocol)) return reject(new Error('Разрешены только http/https'));
    const lib = url.protocol === 'https:' ? https : http;
    const req = lib.request(url, { method: 'GET', headers: browserHeaders(url, referer), agent: url.protocol === 'https:' ? (insecure ? agentInsecure : agent) : undefined, timeout: TIMEOUT_MS }, (res) => {
      storeCookies(url.hostname, res.headers['set-cookie']);
      if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
        res.resume();
        if (hops <= 0) return reject(new Error('Слишком много перенаправлений'));
        const next = new URL(res.headers.location, url).toString();
        return get(next, { referer: url.toString(), hops: hops - 1, insecure, aiaTried }).then(resolve, reject);
      }
      let stream = res;
      const enc = (res.headers['content-encoding'] || '').toLowerCase();
      if (enc === 'gzip') stream = res.pipe(zlib.createGunzip());
      else if (enc === 'br') stream = res.pipe(zlib.createBrotliDecompress());
      else if (enc === 'deflate') stream = res.pipe(zlib.createInflate());
      const chunks = []; let size = 0;
      stream.on('data', (c) => { size += c.length; if (size > MAX_BYTES) { req.destroy(new Error('Ответ больше 3 МБ')); } else chunks.push(c); });
      stream.on('end', () => {
        const ct = res.headers['content-type'] || '';
        const m = /charset=([\w-]+)/i.exec(ct);
        let body;
        try { body = new TextDecoder((m && m[1]) || 'utf-8').decode(Buffer.concat(chunks)); }
        catch (_) { body = Buffer.concat(chunks).toString('utf8'); }
        resolve({ status: res.statusCode, url: url.toString(), contentType: ct, body });
      });
      stream.on('error', reject);
    });
    req.on('timeout', () => req.destroy(new Error('Таймаут запроса')));
    req.on('error', (err) => {
      // сервер не прислал промежуточный сертификат — достраиваем цепочку по AIA и повторяем один раз
      if (!insecure && !aiaTried && url.protocol === 'https:' && /UNABLE_TO_VERIFY_LEAF_SIGNATURE/.test(err.code || '')) {
        fetchIntermediates(url.hostname, Number(url.port) || 443).then((ok) => {
          if (!ok) return reject(err);
          rebuildAgent();
          get(urlStr, { referer, hops, insecure, aiaTried: true }).then(resolve, reject);
        }, () => reject(err));
      } else reject(err);
    });
    req.end();
  });
}

// ---------- разбор HTML ----------
const ENT = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ', laquo: '«', raquo: '»', mdash: '—', ndash: '–', hellip: '…' };
function decode(s) {
  return s.replace(/&(#x?[0-9a-f]+|[a-z]+);/gi, (m, e) => {
    if (e[0] === '#') { const n = e[1].toLowerCase() === 'x' ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10); return Number.isFinite(n) ? String.fromCodePoint(n) : m; }
    return ENT[e.toLowerCase()] ?? m;
  });
}
const strip = (s) => decode(s.replace(/<[^>]*>/g, ' ')).replace(/\s+/g, ' ').trim();

function htmlToText(html) {
  const title = (/<title[^>]*>([\s\S]*?)<\/title>/i.exec(html) || [])[1];
  let b = html.replace(/<(script|style|noscript|svg|template|iframe)[\s\S]*?<\/\1>/gi, ' ')
    .replace(/<!--[\s\S]*?-->/g, ' ')
    .replace(/<\/(p|div|li|tr|h[1-6]|section|article|header|footer|br)\s*>|<br\s*\/?>/gi, '\n');
  b = decode(b.replace(/<[^>]*>/g, ' ')).replace(/[ \t\f\v]+/g, ' ').replace(/ ?\n ?/g, '\n').replace(/\n{3,}/g, '\n\n').trim();
  return { title: title ? strip(title) : '', text: b };
}

function isCaptcha(res) {
  return /\/showcaptcha|\/captcha/i.test(res.url) || /smartcaptcha|id="js-button"|Вы не робот/i.test(res.body.slice(0, 60000)) && !/serp-item/.test(res.body);
}

function parseSerp(html) {
  const out = [];
  const blocks = html.split(/<li[^>]+class="[^"]*\bserp-item\b/i).slice(1);
  for (const raw of blocks) {
    const blk = raw.split(/<\/li>/i)[0];
    if (/\bAdvert\b|data-fast-name="(companies|market|afisha)"|Wizard/i.test(blk.slice(0, 600)) && !/OrganicTitle/.test(blk)) continue;
    const a = /<a[^>]+class="[^"]*OrganicTitle-Link[^"]*"[^>]*>([\s\S]*?)<\/a>/i.exec(blk) ||
              /<a[^>]+href="(https?:[^"]+)"[^>]*>\s*<h2[\s\S]*?<\/a>/i.exec(blk);
    if (!a) continue;
    const href = /href="([^"]+)"/i.exec(a[0]);
    if (!href) continue;
    let url = decode(href[1]);
    if (/^https?:\/\/(yabs|an)\.yandex\./.test(url)) continue; // реклама
    const title = strip(a[1]);
    const sn = /<(?:div|span)[^>]+class="[^"]*\b(?:OrganicText|ExtendedText|TextContainer|Organic-ContentWrapper)\b[^"]*"[^>]*>([\s\S]*?)<\/(?:div|span)>\s*(?:<\/div>|<div)/i.exec(blk);
    out.push({ title, url, snippet: sn ? strip(sn[1]) : '' });
  }
  return out;
}

// ---------- инструменты ----------
async function yandexSearch({ query, page = 1, region, site, count = 10 }) {
  if (!query || typeof query !== 'string') throw new Error('Нужен параметр query');
  const q = site ? `${query} site:${site}` : query;
  const u = new URL('https://yandex.ru/search/');
  u.searchParams.set('text', q);
  u.searchParams.set('lr', String(region || REGION));
  if (page > 1) u.searchParams.set('p', String(page - 1));
  // «Яндекс.Браузер» обычно приходит со стартовой страницы: сначала получаем куки (yandexuid)
  if (!jar.has('yandex.ru')) { try { await get('https://yandex.ru/', { referer: undefined }); } catch (_) {} }
  const res = await get(u.toString(), { referer: 'https://yandex.ru/' });
  if (isCaptcha(res)) {
    throw new Error('Яндекс показал капчу (SmartCaptcha) для IP сервера. Капчу плагин не решает и не обходит. ' +
      'Используйте mcp__search__* (SearXNG) или повторите позже; для стабильной работы нужен «чистый» исходящий IP (маршрут настраивается на уровне сети).');
  }
  if (res.status !== 200) throw new Error(`Яндекс вернул HTTP ${res.status}`);
  const items = parseSerp(res.body).slice(0, Math.max(1, Math.min(count, 30)));
  if (!items.length) throw new Error('Результаты не найдены или изменилась разметка выдачи Яндекса');
  return items.map((r, i) => `${i + 1}. ${r.title}\n   ${r.url}\n   ${r.snippet}`).join('\n\n');
}

async function fetchPage({ url, max_chars = 20000, referer, insecure = false, links = false }) {
  let res;
  try { res = await get(url, { referer: referer || 'https://yandex.ru/', insecure: !!insecure }); }
  catch (e) {
    if (!insecure && /altnames|certificate|CERT_|self.signed|unable to verify/i.test(e.message + (e.code || '')))
      throw new Error(e.message + '. '+(/altnames/.test(e.message) ? 'У сайта нет сертификата на это имя (заглушка хостинга; это не вопрос корней Минцифры)' : 'Цепочка сертификата не проходит проверку (корни Минцифры уже учтены)')+'. Если содержимое нужно прочитать несмотря на это — повторите с insecure:true (проверка подлинности сервера отключится для этого запроса).');
    throw e;
  }
  if (res.status >= 400) throw new Error(`HTTP ${res.status} для ${res.url}`);
  if (/application\/pdf|image\/|audio\/|video\/|octet-stream/i.test(res.contentType)) throw new Error('Не текстовый контент: ' + res.contentType);
  const { title, text } = /html|xml/i.test(res.contentType) || /<html/i.test(res.body.slice(0, 500)) ? htmlToText(res.body) : { title: '', text: res.body };
  const lim = Math.max(500, Math.min(max_chars, 100000));
  let linkList = '';
  if (links && /html/i.test(res.contentType)) {
    const seen = new Set(); const out = [];
    for (const m of res.body.matchAll(/<a\s[^>]*href="([^"#][^"]*)"[^>]*>([\s\S]*?)<\/a>/gi)) {
      let u; try { u = new URL(decode(m[1]), res.url).toString(); } catch { continue; }
      if (!/^https?:/.test(u) || seen.has(u)) continue; seen.add(u);
      out.push(`- ${strip(m[2]).slice(0, 80) || '(без текста)'} → ${u}`);
      if (out.length >= 100) break;
    }
    if (out.length) linkList = '\n\nСсылки:\n' + out.join('\n');
  }
  return `${insecure ? '⚠ ПРОВЕРКА СЕРТИФИКАТА ОТКЛЮЧЕНА (insecure:true)\n' : ''}URL: ${res.url}\nTitle: ${title}\n\n${text.slice(0, lim)}${text.length > lim ? '\n…[обрезано]' : ''}${linkList}`;
}

const FETCH_SCHEMA = { type: 'object', properties: {
  url: { type: 'string', description: 'http(s) URL' },
  max_chars: { type: 'integer', description: 'Максимум символов текста (500–100000, по умолчанию 20000)' },
  links: { type: 'boolean', description: 'Добавить список ссылок страницы (для навигации по сайту)' },
  referer: { type: 'string', description: 'Referer (по умолчанию https://yandex.ru/ — «переход из Яндекс.Браузера»)' },
  insecure: { type: 'boolean', description: 'Не проверять сертификат сервера (только если у сайта сломан сертификат и пользователь согласен на риск)' } }, required: ['url'] };

const TOOLS = [
  {
    name: 'web_open',
    description: 'Открыть любой сайт как Яндекс.Браузер с корнями Минцифры (Russian Trusted Root/Sub CA): работает на сайтах, которые требуют такой браузер/сертификат и на которых обычный web fetch падает с ошибкой сертификата. Возвращает текст страницы; links:true добавляет ссылки для перехода дальше. Cookie сохраняются между вызовами.',
    inputSchema: FETCH_SCHEMA,
    run: fetchPage,
  },
  {
    name: 'yandex_search',
    description: 'Поиск в Яндексе без API (разбор HTML выдачи). Хорош для русскоязычных и российских источников. При капче вернёт ошибку — тогда используйте mcp__search__*.',
    inputSchema: { type: 'object', properties: {
      query: { type: 'string', description: 'Поисковый запрос' },
      page: { type: 'integer', minimum: 1, description: 'Номер страницы выдачи (с 1)' },
      count: { type: 'integer', minimum: 1, maximum: 30, description: 'Максимум результатов (по умолчанию 10)' },
      site: { type: 'string', description: 'Ограничить поиск доменом (site:)' },
      region: { type: 'string', description: 'Код региона Яндекса lr (213 — Москва, 2 — Санкт-Петербург)' } }, required: ['query'] },
    run: yandexSearch,
  },
  { name: 'yandex_fetch', description: 'Алиас web_open (оставлен для совместимости).', inputSchema: FETCH_SCHEMA, run: fetchPage },
];

// ---------- MCP stdio ----------
function send(o) { process.stdout.write(JSON.stringify(o) + '\n'); }
async function handle(msg) {
  const { id, method, params } = msg;
  const reply = (result) => id !== undefined && send({ jsonrpc: '2.0', id, result });
  const fail = (code, message) => id !== undefined && send({ jsonrpc: '2.0', id, error: { code, message } });
  try {
    if (method === 'initialize') {
      return reply({ protocolVersion: (params && params.protocolVersion) || '2025-03-26', capabilities: { tools: {} }, serverInfo: { name: 'dsh-ru-search', version: '1.0.0' } });
    }
    if (method === 'ping') return reply({});
    if (method === 'tools/list') return reply({ tools: TOOLS.map(({ run, ...t }) => t) });
    if (method === 'tools/call') {
      const t = TOOLS.find((x) => x.name === params.name);
      if (!t) return fail(-32602, 'Неизвестный инструмент ' + params.name);
      try {
        await ensureCerts();
        const text = await t.run(params.arguments || {});
        return reply({ content: [{ type: 'text', text }] });
      } catch (e) {
        return reply({ isError: true, content: [{ type: 'text', text: 'Ошибка: ' + e.message }] });
      }
    }
    if (id !== undefined) fail(-32601, 'Метод не поддерживается: ' + method);
  } catch (e) { fail(-32603, e.message); }
}

if (require.main === module) {
  process.stderr.write(`[dsh-ru-search] UA=${UA}; дополнительных CA: ${extraCount}\n`);
  let buf = '', pending = 0, ended = false;
  process.stdin.setEncoding('utf8');
  process.stdin.on('data', (d) => {
    buf += d;
    let i;
    while ((i = buf.indexOf('\n')) >= 0) {
      const line = buf.slice(0, i).trim(); buf = buf.slice(i + 1);
      if (!line) continue;
      try { pending++; handle(JSON.parse(line)).finally(() => { pending--; if (ended && !pending) process.exit(0); }); } catch (e) { send({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'parse error' } }); }
    }
  });
  process.stdin.on('end', () => { ended = true; if (!pending) process.exit(0); });
} else {
  module.exports = { parseSerp, htmlToText, isCaptcha, get, ensureCerts, loadCa };
}
