'use strict';
const test = require('node:test');
const assert = require('node:assert');
const { spawn } = require('node:child_process');
const path = require('node:path');
const BIN = path.join(__dirname, '..', 'bin', 'dsh-ru-search.js');
const lib = require(BIN);

test('parseSerp: разбор выдачи, реклама пропускается', () => {
  const html = `<li class="serp-item serp-item_card"><div class="Organic"><a class="Link OrganicTitle-Link" href="https://example.ru/a?x=1&amp;y=2"><h2 class="OrganicTitle-LinkText"><span>Заголовок &laquo;один&raquo;</span></h2></a><div class="OrganicText"><span>Сниппет <b>текст</b></span></div></div></li><li class="serp-item Advert"><a class="OrganicTitle-Link" href="https://yabs.yandex.ru/x">реклама</a></li>`;
  const r = lib.parseSerp(html);
  assert.strictEqual(r.length, 1);
  assert.strictEqual(r[0].url, 'https://example.ru/a?x=1&y=2');
  assert.strictEqual(r[0].title, 'Заголовок «один»');
  assert.strictEqual(r[0].snippet, 'Сниппет текст');
});

test('htmlToText: вырезает скрипты, декодирует сущности', () => {
  const r = lib.htmlToText('<title>T &amp; Co</title><script>var x=1</script><p>Привет&nbsp;мир</p>');
  assert.strictEqual(r.title, 'T & Co');
  assert.ok(/Привет мир/.test(r.text) && !/var x/.test(r.text));
});

test('isCaptcha: распознает страницу капчи', () => {
  assert.ok(lib.isCaptcha({ url: 'https://yandex.ru/showcaptcha?cc=1', body: '' }));
  assert.ok(!lib.isCaptcha({ url: 'https://yandex.ru/search/', body: '<li class="serp-item">x</li>' }));
});

test('MCP: initialize и tools/list по stdio', async () => {
  const p = spawn(process.execPath, [BIN], { env: { ...process.env, YA_NO_CERT_DOWNLOAD: '1' } });
  let out = '';
  p.stdout.on('data', (d) => (out += d));
  p.stdin.write(JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'initialize', params: { protocolVersion: '2025-03-26' } }) + '\n');
  p.stdin.write(JSON.stringify({ jsonrpc: '2.0', id: 2, method: 'tools/list' }) + '\n');
  p.stdin.end();
  await new Promise((r) => p.on('close', r));
  const lines = out.trim().split('\n').map((l) => JSON.parse(l));
  assert.strictEqual(lines[0].result.serverInfo.name, 'dsh-ru-search');
  const names = lines[1].result.tools.map((t) => t.name).sort();
  assert.deepStrictEqual(names, ['web_open', 'yandex_fetch', 'yandex_search']);
});
