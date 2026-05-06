/* ===================================================================
   JSON Diff Viewer — app.js
   Pure ES2020, no build step required.
=================================================================== */
'use strict';

// ===================================================================
// CONFIG
// ===================================================================
const CFG = {
  DATA_URL:           '../data/',
  PREPROCESSED_URL:   '../preprocessed_data/',
  LARGE_FILE_BYTES:   5 * 1024 * 1024,   // 5 MB
  DEFAULT_MAX_DEPTH:  4,
  LARGE_MAX_DEPTH:    2,
  STRING_TRUNCATE:    120,
};

// ===================================================================
// STATE
// ===================================================================
let S = {
  /** @type {{name:string, leftUrl:string|null, rightUrl:string|null, paired:boolean}[]} */
  pairs:           [],
  currentPair:     null,  // pair name
  leftData:        null,  // parsed JSON
  rightData:       null,
  leftLabel:       '',    // display label for left panel
  rightLabel:      '',
  delta:           null,  // jsondiffpatch delta
  viewMode:        'unit',// 'unit' | 'tree' | 'raw'
  diffOnly:        false,
  searchQuery:     '',
  selectedPath:    null,
  selectedQuestionNum: 1,
};

// jsondiffpatch instance (set after load)
let jdp = null;

// ===================================================================
// INIT
// ===================================================================
async function init() {
  if (typeof jsondiffpatch !== 'undefined') {
    jdp = jsondiffpatch.create({ textDiff: { minLength: 60 } });
  }
  setupEventListeners();
  setupSidebarResize();
  await discoverFiles();
  renderSidebarList();
  if (S.pairs.length > 0) {
    await loadPair(S.pairs[0].name);
  }
  renderEmptyState();
}

// ===================================================================
// FILE DISCOVERY
// ===================================================================
async function discoverFiles() {
  const [leftFiles, rightFiles] = await Promise.all([
    tryFetchDirListing(CFG.DATA_URL),
    tryFetchDirListing(CFG.PREPROCESSED_URL),
  ]);

  const rightSet = new Set(rightFiles);
  const leftSet  = new Set(leftFiles);

  const pairs = [];
  for (const name of leftFiles) {
    pairs.push({ name, leftUrl: CFG.DATA_URL + name, rightUrl: CFG.PREPROCESSED_URL + name, paired: rightSet.has(name) });
  }
  // files only in right
  for (const name of rightFiles) {
    if (!leftSet.has(name)) {
      pairs.push({ name, leftUrl: null, rightUrl: CFG.PREPROCESSED_URL + name, paired: false });
    }
  }

  S.pairs = pairs;

  const sidebarStatus = document.getElementById('sidebar-status');
  if (pairs.length > 0) {
    const paired = pairs.filter(p => p.paired).length;
    sidebarStatus.textContent = `${pairs.length} file${pairs.length !== 1 ? 's' : ''}, ${paired} paired`;
  } else {
    sidebarStatus.textContent = 'auto-load unavailable';
  }
}

/**
 * Try to read directory listing served by python -m http.server (returns HTML).
 * Falls back to empty list on any error.
 */
async function tryFetchDirListing(url) {
  try {
    const resp = await fetch(url);
    if (!resp.ok) return [];
    const ct = resp.headers.get('content-type') || '';
    const text = await resp.text();

    if (ct.includes('text/html')) {
      // Python http.server returns an HTML page with <a href="filename.json"> links
      const parser = new DOMParser();
      const doc = parser.parseFromString(text, 'text/html');
      return Array.from(doc.querySelectorAll('a[href]'))
        .map(a => decodeURIComponent(a.getAttribute('href').replace(/^.*\//, '')))
        .filter(name => name.endsWith('.json'));
    }

    // If served as JSON manifest (array of strings)
    try {
      const arr = JSON.parse(text);
      if (Array.isArray(arr)) return arr.filter(f => typeof f === 'string' && f.endsWith('.json'));
    } catch (_) { /* not JSON */ }

    return [];
  } catch (err) {
    console.warn(`Dir listing unavailable for ${url}:`, err.message);
    return [];
  }
}

// ===================================================================
// FILE LOADING
// ===================================================================
async function loadPair(pairName) {
  const pair = S.pairs.find(p => p.name === pairName);
  if (!pair) return;

  S.currentPair = pairName;
  renderSidebarList();
  renderLoading();

  try {
    const [left, right] = await Promise.all([
      pair.leftUrl  ? fetchJSON(pair.leftUrl)  : null,
      pair.rightUrl ? fetchJSON(pair.rightUrl) : null,
    ]);
    S.leftData  = left;
    S.rightData = right;
    S.selectedQuestionNum = 1;
    S.leftLabel  = pair.paired ? pair.name : (left  ? pair.name : '—');
    S.rightLabel = pair.paired ? pair.name : (right ? pair.name : '—');
    computeDiff();
    renderViewer();
    renderSidebarList();
  } catch (err) {
    renderLoadError(err.message);
  }
}

async function fetchJSON(url) {
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(`HTTP ${resp.status} loading ${url}`);
  return resp.json();
}

async function readUploadedFile(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = e => {
      try { resolve(JSON.parse(e.target.result)); }
      catch (err) { reject(new Error(`Invalid JSON in "${file.name}": ${err.message}`)); }
    };
    reader.onerror = () => reject(new Error(`Could not read "${file.name}"`));
    reader.readAsText(file);
  });
}

// ===================================================================
// DIFF
// ===================================================================
function computeDiff() {
  if (!S.leftData || !S.rightData || !jdp) { S.delta = null; return; }
  try {
    S.delta = jdp.diff(S.leftData, S.rightData) ?? null;
  } catch (err) {
    console.error('jsondiffpatch error:', err);
    S.delta = null;
  }
}

function countDeltaChanges(delta) {
  let added = 0, removed = 0, modified = 0;
  walkDelta(delta, {
    onAdded:    () => added++,
    onRemoved:  () => removed++,
    onModified: () => modified++,
  });
  return { added, removed, modified };
}

function walkDelta(delta, cb) {
  if (!delta) return;
  if (Array.isArray(delta)) {
    if (delta.length === 1)                              cb.onAdded?.();
    else if (delta.length === 3 && delta[1] === 0 && delta[2] === 0) cb.onRemoved?.();
    else                                                 cb.onModified?.();
    return;
  }
  if (typeof delta === 'object') {
    for (const k of Object.keys(delta)) {
      if (k === '_t') continue;
      walkDelta(delta[k], cb);
    }
  }
}

function deltaHasAnyChange(delta) {
  if (!delta) return false;
  if (Array.isArray(delta)) return true;
  if (typeof delta !== 'object') return false;
  for (const k of Object.keys(delta)) {
    if (k === '_t') continue;
    if (deltaHasAnyChange(delta[k])) return true;
  }
  return false;
}

// ===================================================================
// RENDERING — MAIN
// ===================================================================
function renderViewer() {
  updatePanelHeader('left',  S.leftLabel,  S.leftData);
  updatePanelHeader('right', S.rightLabel, S.rightData);

  const lv = document.getElementById('left-viewer');
  const rv = document.getElementById('right-viewer');

  if (S.viewMode === 'unit') {
    renderUnitView(lv, rv);
  } else if (S.viewMode === 'tree') {
    renderTreeView(lv, S.leftData,  S.delta, 'left');
    renderTreeView(rv, S.rightData, S.delta, 'right');
  } else {
    renderRawView(lv, S.leftData);
    renderRawView(rv, S.rightData);
  }

  renderInfoBar(null);
  updateStatusBar();
}

function renderUnitView(leftContainer, rightContainer) {
  const leftItems = normalizeToArray(S.leftData);
  if (leftItems.length === 0) {
    leftContainer.innerHTML = '<div class="empty-state"><div class="es-icon">—</div><p>No left-side items available.</p></div>';
    rightContainer.innerHTML = '<div class="empty-state"><div class="es-icon">—</div><p>No right-side items available.</p></div>';
    return;
  }

  const qNum = clampQuestionNum(S.selectedQuestionNum, leftItems.length);
  S.selectedQuestionNum = qNum;

  const leftItem = leftItems[qNum - 1];
  const leftSrcIdx = String(getItemSourceIdx(leftItem)).trim();
  const rightMatches = getRightMatchesForSourceIdx(leftSrcIdx);

  renderLeftUnit(leftContainer, leftItem, qNum, leftSrcIdx);
  renderRightUnits(rightContainer, rightMatches, leftSrcIdx);
}

function renderLeftUnit(container, item, qNum, srcIdx) {
  const unit = extractLeftUnit(item);
  const extras = extractLeftExtras(item);
  const meta = buildUnitMeta(item, qNum - 1);
  const displayLabel = srcIdx || String(qNum);
  const card = `
    <article class="unit-card">
      <header class="unit-head">
        <span class="unit-title">${esc(displayLabel)}</span>
        <span class="unit-meta">${esc(meta)}</span>
      </header>
      <div class="unit-body" data-math-scope="left">
        <section class="unit-block">
          <div class="unit-label">Problem</div>
          ${renderMathText(unit.problem)}
        </section>
        <section class="unit-block">
          <div class="unit-label">Proof</div>
          ${renderMathText(unit.proof)}
        </section>
        <section class="unit-block">
          <div class="unit-label">Direct Answer</div>
          ${renderMathText(unit.directAnswer)}
        </section>
        ${renderExtraFieldsBlock(extras)}
      </div>
    </article>
  `;

  container.innerHTML = `<div class="unit-list">${card}</div>`;
  renderMathIn(container);
}

function renderRightUnits(container, items, srcIdx) {
  if (items.length === 0) {
    container.innerHTML = `<div class="empty-state"><div class="es-icon">∅</div><p>No right-side items with source_idx = "${esc(srcIdx)}".</p></div>`;
    return;
  }

  const cards = items.map((item, i) => {
    const content = extractRightContent(item);
    const meta = buildUnitMeta(item, i);
    const termBlock = renderTermBlock(item);
    return `
      <article class="unit-card">
        <header class="unit-head">
          <span class="unit-title">Match ${i + 1} · ${esc(srcIdx)}</span>
          <span class="unit-meta">${esc(meta)}</span>
        </header>
        <div class="unit-body" data-math-scope="right">
          ${termBlock}
          <section class="unit-block">
            <div class="unit-label">Content</div>
            ${renderContentBlock(content)}
          </section>
        </div>
      </article>
    `;
  }).join('');

  container.innerHTML = `<div class="unit-list">${cards}</div>`;
  renderMathIn(container);
}

function normalizeToArray(data) {
  if (!data) return [];
  if (Array.isArray(data)) return data;
  if (typeof data === 'object') return [data];
  return [];
}

function extractLeftUnit(item) {
  const root = (item && typeof item === 'object') ? item : {};
  const nested = (root.content && typeof root.content === 'object') ? root.content : {};
  return {
    problem: nested.problem ?? root.problem,
    proof: nested.proof ?? root.proof,
    directAnswer: nested.direct_answer ?? nested.directAnswer ?? root.direct_answer ?? root.directAnswer,
  };
}

function extractLeftExtras(item) {
  if (!item || typeof item !== 'object') return {};
  const root = { ...item };
  delete root.problem;
  delete root.proof;
  delete root.direct_answer;
  delete root.directAnswer;
  return root;
}

function extractRightContent(item) {
  if (!item || typeof item !== 'object') return item;
  if ('content' in item) return item.content;
  return item;
}

function getItemSourceIdx(item) {
  if (!item || typeof item !== 'object') return '';
  const nested = item.content && typeof item.content === 'object' ? item.content : {};
  return nested.source_idx ?? item.source_idx ?? '';
}

function getLeftQuestionLabel(item, qNum) {
  const sourceIdx = getItemSourceIdx(item);
  return sourceIdx !== '' ? String(sourceIdx) : String(qNum);
}

function getRightMatchesForSourceIdx(srcIdx) {
  const target = String(srcIdx).trim();
  if (!target) return [];
  const rightItems = normalizeToArray(S.rightData);
  const exact = rightItems.filter(item => String(getItemSourceIdx(item)).trim() === target);
  if (exact.length > 0) return exact;

  // 宽松匹配：兼容 Exercise 11.9 / exercise_11_9 / exercise-11-9 等格式
  const normTarget = normalizeSourceKey(target);
  return rightItems.filter(item => normalizeSourceKey(getItemSourceIdx(item)) === normTarget);
}

function normalizeSourceKey(v) {
  return String(v ?? '')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '');
}

function clampQuestionNum(n, max) {
  const v = Number.isFinite(n) ? n : 1;
  if (max <= 0) return 1;
  return Math.max(1, Math.min(max, Math.trunc(v)));
}

function buildUnitMeta(item, index) {
  if (!item || typeof item !== 'object') return `index:${index}`;
  const parts = [];
  if (item.source_idx !== undefined) parts.push(String(item.source_idx));
  if (item.kind !== undefined) parts.push(String(item.kind));
  if (item.source !== undefined) parts.push(String(item.source));
  if (parts.length === 0 && item.index !== undefined) parts.push(`index:${item.index}`);
  return parts.join(' | ') || `index:${index}`;
}

function processItemizeEnvironments(text) {
  // 处理 LaTeX itemize 环境，支持嵌套
  // 从最内层开始逐层处理，直到没有更多的 \begin{itemize}...\end{itemize}
  const placeholders = {};
  let counter = 0;

  while (text.includes('\\begin{itemize}')) {
    text = text.replace(
      /\\begin\{itemize\}([\s\S]*?)\\end\{itemize\}/,
      (match, content) => {
        // 分割 \item，创建列表项
        const items = content.split(/\\item\s+/);
        const liItems = items
          .map(item => item.trim())
          .filter(item => item.length > 0)
          .map(item => `<li>${item}</li>`)
          .join('\n');
        
        const html = `<ul>\n${liItems}\n</ul>`;
        
        // 使用占位符替换，避免后续 esc() 处理
        const placeholder = `___ITEMIZE_${counter}___`;
        placeholders[placeholder] = html;
        counter++;
        return placeholder;
      }
    );
  }

  // 返回处理后的文本和占位符映射
  return { text, placeholders };
}

function renderMathText(value) {
  if (value === undefined || value === null || value === '') {
    return '<div class="unit-text unit-missing">absent</div>';
  }
  let text = typeof value === 'string' ? value : JSON.stringify(value, null, 2);
  
  // 处理 itemize 环境
  const { text: processedText, placeholders } = processItemizeEnvironments(text);
  text = processedText;
  
  // 对普通文本进行 HTML 转义
  text = esc(text);
  
  // 恢复 itemize HTML（占位符在转义中被保留）
  Object.entries(placeholders).forEach(([placeholder, html]) => {
    text = text.replace(placeholder, html);
  });
  
  return `<div class="unit-text">${text}</div>`;
}

function renderContentBlock(value) {
  if (value === undefined || value === null || value === '') {
    return '<div class="unit-text unit-missing">absent</div>';
  }
  if (typeof value === 'string') {
    return `<div class="unit-text">${esc(value)}</div>`;
  }
  return `<pre class="unit-pre">${esc(JSON.stringify(value, null, 2))}</pre>`;
}

function renderExtraFieldsBlock(value) {
  if (!value || typeof value !== 'object') return '';
  const entries = Object.entries(value).filter(([, v]) => v !== undefined);
  if (entries.length === 0) return '';

  const rows = entries.map(([k, v]) => `
    <div class="unit-block">
      <div class="unit-label">${esc(k)}</div>
      ${renderContentBlock(v)}
    </div>
  `).join('');

  return `
    <section class="unit-block">
      <div class="unit-label">Additional Fields</div>
      <div class="unit-body" style="padding:0;gap:8px">
        ${rows}
      </div>
    </section>
  `;
}

function renderTermBlock(item) {
  const kind = String(item?.kind ?? '').trim();
  const needsTerm = kind === 'algo' || kind === 'opt_prob' || kind === 'defn';
  if (!needsTerm) return '';

  const term = item?.term;
  const text = term === undefined || term === null || term === ''
    ? '<div class="unit-text unit-missing">absent</div>'
    : `<div class="unit-text">${esc(String(term))}</div>`;

  return `
    <section class="unit-block">
      <div class="unit-label">Term</div>
      ${text}
    </section>
  `;
}

function renderMathIn(root) {
  if (typeof renderMathInElement !== 'function') return;
  renderMathInElement(root, {
    throwOnError: false,
    strict: 'ignore',
    delimiters: [
      { left: '$$', right: '$$', display: true },
      { left: '\\[', right: '\\]', display: true },
      { left: '$', right: '$', display: false },
      { left: '\\(', right: '\\)', display: false },
    ],
  });
}

function renderLoading() {
  ['left-viewer','right-viewer'].forEach(id => {
    document.getElementById(id).innerHTML =
      '<div class="loading"><div class="spinner"></div><span>Loading…</span></div>';
  });
}

function renderLoadError(msg) {
  const html = `<div class="empty-state"><div class="es-icon">⚠️</div><p>${esc(msg)}</p></div>`;
  document.getElementById('left-viewer').innerHTML  = html;
  document.getElementById('right-viewer').innerHTML = html;
}

function renderEmptyState() {
  const html = `<div class="empty-state">
    <div class="es-icon">📂</div>
    <p>Select a file from the list on the left, or upload JSON files manually.</p>
  </div>`;
  document.getElementById('left-viewer').innerHTML  = html;
  document.getElementById('right-viewer').innerHTML = html;
  renderInfoBar(null);
  document.getElementById('status-bar').innerHTML = '';
}

function updatePanelHeader(side, filename, data) {
  const el    = document.getElementById(`${side}-panel-header`);
  const label = side === 'left' ? 'Original · data/' : 'Preprocessed · preprocessed_data/';
  const size  = data ? `<span class="ph-size">${fmtSize(roughSize(data))}</span>` : '';
  const fname = filename
    ? `<span class="ph-filename" title="${esc(filename)}">${esc(filename)}</span>`
    : '';
  el.innerHTML = `<span class="ph-label">${label}</span>${fname}${size}`;
}

// ===================================================================
// RENDERING — TREE VIEW
// ===================================================================
function renderTreeView(container, data, delta, side) {
  if (!data) {
    container.innerHTML = `<div class="empty-state"><div class="es-icon">—</div><p>No file loaded for this side.</p></div>`;
    return;
  }

  const byteSize  = roughSize(data);
  const isLarge   = byteSize > CFG.LARGE_FILE_BYTES;
  const maxDepth  = isLarge ? CFG.LARGE_MAX_DEPTH : CFG.DEFAULT_MAX_DEPTH;
  const diffClass = S.diffOnly ? 'diff-only-mode' : '';

  let html = '';
  if (isLarge) {
    html += `<div class="large-warn">
      ⚠ Large file (${fmtSize(byteSize)}) — expand depth limited to ${maxDepth}.
      <button class="btn" data-expand-side="${esc(side)}">Expand All</button>
    </div>`;
  }

  html += `<div class="json-tree ${diffClass}" id="${side}-tree">`;
  html += buildNodeHtml(null, data, delta, side, '$', 0, maxDepth);
  html += '</div>';

  container.innerHTML = html;
  container.querySelector('.json-tree').addEventListener('click', handleTreeClick);
}

// ===================================================================
// RENDERING — NODE HTML BUILDER
// ===================================================================
/**
 * @param {string|number|null} key   — object key or array index, null for root
 * @param {*}      value             — current JSON value
 * @param {*}      delta             — jsondiffpatch delta for this node
 * @param {'left'|'right'} side
 * @param {string} path              — dotpath like $.foo[0].bar
 * @param {number} depth
 * @param {number} maxDepth
 */
function buildNodeHtml(key, value, delta, side, path, depth, maxDepth) {
  const directClass  = getDirectDiffClass(delta, side);
  const containsChg  = !directClass && deltaHasAnyChange(delta);
  const noDiff       = !directClass && !containsChg ? ' no-diff' : '';
  const containsCls  = containsChg ? ' diff-contains' : '';

  if (value === null || value === undefined || typeof value !== 'object') {
    // Leaf node
    const type    = value === null ? 'null' : typeof value;
    const rawStr  = value === null ? 'null' : String(value);
    const display = type === 'string'
      ? `"${esc(rawStr.length > CFG.STRING_TRUNCATE ? rawStr.slice(0, CFG.STRING_TRUNCATE) + '…' : rawStr)}"`
      : esc(rawStr);
    const longCls = (type === 'string' && rawStr.length > CFG.STRING_TRUNCATE) ? ' long' : '';
    const keyHtml = buildKeyHtml(key);

    return `<div class="jl${noDiff} ${directClass}"
      data-path="${esc(path)}"
      title="${esc(path)}">
      ${keyHtml}<span class="jv ${type}${longCls}">${display}</span>
    </div>`;
  }

  // Container node (object or array)
  const isArr   = Array.isArray(value);
  const entries = isArr ? [...value.entries()] : Object.entries(value);
  const count   = entries.length;
  const hint    = isArr ? `[${count}]` : `{${count}}`;
  const open    = depth < maxDepth;
  const keyHtml = buildKeyHtml(key);

  let inner = '';
  for (const [k, v] of entries) {
    const childPath  = isArr ? `${path}[${k}]` : `${path}.${esc2(String(k))}`;
    const childDelta = getChildDelta(delta, k, isArr);
    inner += buildNodeHtml(k, v, childDelta, side, childPath, depth + 1, maxDepth);
  }

  return `<details class="jn${noDiff}${containsCls} ${directClass}" data-path="${esc(path)}" ${open ? 'open' : ''}>
    <summary data-path="${esc(path)}">
      <span class="jn-toggle">▶</span>
      ${keyHtml}<span class="jn-typehint">${hint}</span>
    </summary>
    <div class="jn-children">${inner}</div>
  </details>`;
}

function buildKeyHtml(key) {
  if (key === null) return '';  // root
  if (typeof key === 'number') return `<span class="jn-key">${key}</span>`;
  return `<span class="jn-key">${esc(String(key))}</span>`;
}

// ===================================================================
// RENDERING — RAW VIEW
// ===================================================================
function renderRawView(container, data) {
  if (!data) {
    container.innerHTML = `<div class="empty-state"><div class="es-icon">—</div><p>No file loaded.</p></div>`;
    return;
  }
  const jsonStr = JSON.stringify(data, null, 2);
  let highlighted;
  try {
    highlighted = (typeof hljs !== 'undefined')
      ? hljs.highlight(jsonStr, { language: 'json' }).value
      : esc(jsonStr);
  } catch (_) {
    highlighted = esc(jsonStr);
  }
  container.innerHTML = `<pre class="raw-view"><code class="hljs language-json">${highlighted}</code></pre>`;
}

// ===================================================================
// DELTA UTILITIES
// ===================================================================
/**
 * Return the CSS diff class for a given delta at this node level.
 * delta is the delta *for this specific node*, not a parent.
 */
function getDirectDiffClass(delta, side) {
  if (!delta || !Array.isArray(delta)) return '';

  if (delta.length === 1)  // [newVal] — added
    return side === 'right' ? 'diff-added' : '';

  if (delta.length === 3 && delta[1] === 0 && delta[2] === 0)  // [old,0,0] — deleted
    return side === 'left'  ? 'diff-removed' : '';

  // [old, new] or [old, new, 2] (text diff) — modified
  return 'diff-modified';
}

/** Get the delta scoped to a child key/index. */
function getChildDelta(delta, key, isArray) {
  if (!delta || Array.isArray(delta) || typeof delta !== 'object') return undefined;

  if (isArray && delta._t === 'a') {
    // jsondiffpatch array delta:
    // deletions stored as '_<originalIndex>'
    // modifications/additions stored as '<index>'
    const del = delta['_' + key];
    if (del) return del;
    return delta[String(key)];
  }

  return delta[String(key)];
}

// ===================================================================
// RENDERING — FILE LIST
// ===================================================================
function renderSidebarList() {
  if (S.viewMode === 'unit' && normalizeToArray(S.leftData).length > 0) {
    renderQuestionList();
    return;
  }

  const list = document.getElementById('file-list');
  const q    = S.searchQuery.toLowerCase();
  const filtered = q
    ? S.pairs.filter(p => p.name.toLowerCase().includes(q))
    : S.pairs;

  if (filtered.length === 0) {
    const msg = S.pairs.length === 0
      ? 'No files found via auto-scan.<br>Use the upload buttons below.'
      : 'No files match the search.';
    list.innerHTML = `<div class="no-files-msg">${msg}</div>`;
    return;
  }

  list.innerHTML = filtered.map(p => `
    <div class="file-item ${p.name === S.currentPair ? 'active' : ''}"
         data-pair-name="${esc(p.name)}"
         title="${esc(p.name)}">
      <span class="fi-icon">📄</span>
      <span class="fi-name">${esc(p.name)}</span>
      <span class="fi-badge ${p.paired ? 'paired' : 'unpaired'}">${p.paired ? '⇄' : '1'}</span>
    </div>
  `).join('');
}

function renderQuestionList() {
  const list = document.getElementById('file-list');
  const leftItems = normalizeToArray(S.leftData);
  const q = S.searchQuery.toLowerCase();

  const rows = leftItems.map((item, idx) => {
    const qNum = idx + 1;
    const label = getLeftQuestionLabel(item, qNum);
    const srcIdx = String(getItemSourceIdx(item)).trim();
    const matches = srcIdx ? getRightMatchesForSourceIdx(srcIdx).length : 0;
    return { qNum, label, matches };
  }).filter(r => {
    if (!q) return true;
    return String(r.label).toLowerCase().includes(q) || String(r.qNum).includes(q);
  });

  const sidebarStatus = document.getElementById('sidebar-status');
  sidebarStatus.textContent = `${leftItems.length} questions`;

  if (rows.length === 0) {
    list.innerHTML = '<div class="no-files-msg">No questions match the search.</div>';
    return;
  }

  list.innerHTML = rows.map(r => `
    <div class="file-item ${r.qNum === S.selectedQuestionNum ? 'active' : ''}"
         data-question-num="${r.qNum}"
         title="${esc(String(r.label))}">
      <span class="fi-icon">#</span>
      <span class="fi-name">${esc(String(r.label))}</span>
      <span class="fi-badge ${r.matches > 0 ? 'paired' : 'unpaired'}">${r.matches}</span>
    </div>
  `).join('');
}

// ===================================================================
// RENDERING — INFO BAR
// ===================================================================
function renderInfoBar(info) {
  const bar = document.getElementById('info-bar');
  if (!info) {
    bar.innerHTML = '<div class="ib-placeholder">Click on a field to see its path and values</div>';
    return;
  }
  const { path, leftVal, rightVal } = info;
  const fmt = v => v !== undefined ? esc(JSON.stringify(v, null, 2)) : '<em style="opacity:.5">absent</em>';

  bar.innerHTML = `
    <div style="flex:1;min-width:0">
      <div class="ib-path">${esc(path)}</div>
      <div class="ib-cols">
        <div class="ib-col">
          <div class="ib-col-label">Left · Original</div>
          <div class="ib-col-value">${fmt(leftVal)}</div>
        </div>
        <div class="ib-col">
          <div class="ib-col-label">Right · Preprocessed</div>
          <div class="ib-col-value">${fmt(rightVal)}</div>
        </div>
      </div>
    </div>
  `;
}

// ===================================================================
// RENDERING — STATUS BAR
// ===================================================================
function updateStatusBar() {
  const bar = document.getElementById('status-bar');
  if (!S.leftData && !S.rightData) { bar.innerHTML = ''; return; }

  if (!S.delta) {
    bar.innerHTML = '<div class="sb-item sb-ok">✓ Files are identical</div>';
    return;
  }

  const { added, removed, modified } = countDeltaChanges(S.delta);
  bar.innerHTML = `
    <div class="sb-item"><div class="sb-dot green"></div>${added} added</div>
    <div class="sb-item"><div class="sb-dot red"></div>${removed} removed</div>
    <div class="sb-item"><div class="sb-dot yellow"></div>${modified} modified</div>
  `;
}

// ===================================================================
// EVENT LISTENERS
// ===================================================================
function setupEventListeners() {
  // File list click (event delegation)
  document.getElementById('file-list').addEventListener('click', e => {
    const item = e.target.closest('.file-item');
    if (!item) return;
    if (item.dataset.questionNum) {
      S.selectedQuestionNum = Number(item.dataset.questionNum);
      renderSidebarList();
      renderViewer();
      return;
    }
    if (item.dataset.pairName) loadPair(item.dataset.pairName);
  });

  // Search
  document.getElementById('search-input').addEventListener('input', e => {
    S.searchQuery = e.target.value;
    renderSidebarList();
  });

  // View mode toggle
  document.getElementById('btn-unit').addEventListener('click', () => setViewMode('unit'));

  // View mode toggle
  document.getElementById('btn-tree').addEventListener('click', () => setViewMode('tree'));
  document.getElementById('btn-raw').addEventListener('click',  () => setViewMode('raw'));

  // Diff-only toggle
  document.getElementById('toggle-diff-only').addEventListener('change', e => {
    S.diffOnly = e.target.checked;
    if (S.viewMode === 'tree' && (S.leftData || S.rightData)) renderViewer();
  });

  // Expand / Collapse all
  document.getElementById('btn-expand-all').addEventListener('click', () => toggleAllDetails(true));
  document.getElementById('btn-collapse-all').addEventListener('click', () => toggleAllDetails(false));

  // Export diff
  document.getElementById('btn-export-diff').addEventListener('click', exportDiff);

  // Export rendered panels as PDF
  document.getElementById('btn-export-left-pdf').addEventListener('click', () => exportPanelPdf('left'));
  document.getElementById('btn-export-right-pdf').addEventListener('click', () => exportPanelPdf('right'));

  // Manual upload — left
  document.getElementById('upload-left-input').addEventListener('change', async e => {
    const file = e.target.files[0];
    e.target.value = '';
    if (!file) return;
    try {
      S.leftData  = await readUploadedFile(file);
      S.leftLabel = file.name;
      S.currentPair = null;
      S.selectedQuestionNum = 1;
      computeDiff();
      renderViewer();
      setUploadBtnLabel('left', file.name);
      renderSidebarList();
    } catch (err) { showToast(err.message, 'error'); }
  });

  // Manual upload — right
  document.getElementById('upload-right-input').addEventListener('change', async e => {
    const file = e.target.files[0];
    e.target.value = '';
    if (!file) return;
    try {
      S.rightData  = await readUploadedFile(file);
      S.rightLabel = file.name;
      computeDiff();
      renderViewer();
      renderSidebarList();
      setUploadBtnLabel('right', file.name);
    } catch (err) { showToast(err.message, 'error'); }
  });

  // Expand-all button inside large-file banner (event delegation)
  document.getElementById('panels').addEventListener('click', e => {
    const btn = e.target.closest('[data-expand-side]');
    if (btn) expandAllInSide(btn.dataset.expandSide);
  });
}

// ===================================================================
// TREE CLICK HANDLER
// ===================================================================
function handleTreeClick(e) {
  // Find nearest element with data-path
  const target = e.target.closest('[data-path]');
  if (!target) return;

  const path     = target.dataset.path;
  const leftVal  = resolvePathInData(S.leftData,  path);
  const rightVal = resolvePathInData(S.rightData, path);

  renderInfoBar({ path, leftVal, rightVal });

  // Highlight selected
  document.querySelectorAll('.selected').forEach(el => el.classList.remove('selected'));
  target.classList.add('selected');
}

// ===================================================================
// VIEW MODE
// ===================================================================
function setViewMode(mode) {
  S.viewMode = mode;
  document.getElementById('btn-unit').classList.toggle('active', mode === 'unit');
  document.getElementById('btn-tree').classList.toggle('active', mode === 'tree');
  document.getElementById('btn-raw').classList.toggle('active',  mode === 'raw');
  renderSidebarList();
  if (S.leftData || S.rightData) renderViewer();
}

// ===================================================================
// EXPAND / COLLAPSE
// ===================================================================
function toggleAllDetails(open) {
  document.querySelectorAll('details.jn').forEach(d => { d.open = open; });
}

function expandAllInSide(side) {
  const tree = document.getElementById(`${side}-tree`);
  if (tree) tree.querySelectorAll('details').forEach(d => { d.open = true; });
}

// ===================================================================
// EXPORT DIFF
// ===================================================================
function exportDiff() {
  if (!S.delta) {
    showToast(
      !S.leftData || !S.rightData
        ? 'Load both files before exporting.'
        : 'Files are identical — no diff to export.',
      'warn'
    );
    return;
  }

  const out = {
    filename:  S.currentPair ?? 'manual-upload',
    exportedAt: new Date().toISOString(),
    summary:   countDeltaChanges(S.delta),
    delta:     S.delta,
  };
  const blob = new Blob([JSON.stringify(out, null, 2)], { type: 'application/json' });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href     = url;
  a.download = `diff_${(S.currentPair ?? 'export').replace('.json', '')}_${Date.now()}.json`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
  showToast('Diff exported!');
}

async function exportPanelPdf(side) {
  const panel = document.getElementById(`${side}-panel`);
  if (!panel) {
    showToast('Panel not found.', 'error');
    return;
  }

  const hasData = side === 'left' ? !!S.leftData : !!S.rightData;
  if (!hasData) {
    showToast(`No ${side} panel data to export.`, 'warn');
    return;
  }

  if (typeof html2canvas !== 'function') {
    showToast('Image export library not loaded.', 'error');
    return;
  }

  showToast(`Rendering ${side} panel image...`);

  // 克隆一份离屏节点，确保导出完整滚动内容而非仅可视区域
  const cloneWrap = document.createElement('div');
  cloneWrap.style.position = 'fixed';
  cloneWrap.style.left = '-100000px';
  cloneWrap.style.top = '0';
  cloneWrap.style.width = `${panel.clientWidth}px`;
  cloneWrap.style.background = getComputedStyle(document.body).backgroundColor;

  let contentClone;
  if (side === 'left') {
    // 左边只导出 problem 块
    const problemBlock = panel.querySelector('.unit-block');
    if (!problemBlock) {
      showToast('Problem block not found.', 'warn');
      return;
    }
    contentClone = problemBlock.cloneNode(true);
  } else {
    // 右边导出整个面板
    const panelClone = panel.cloneNode(true);
    const bodyClone = panelClone.querySelector('.panel-body');
    if (bodyClone) {
      bodyClone.style.height = 'auto';
      bodyClone.style.maxHeight = 'none';
      bodyClone.style.overflow = 'visible';
    }
    contentClone = panelClone;
  }

  cloneWrap.appendChild(contentClone);
  document.body.appendChild(cloneWrap);

  try {
    const canvas = await html2canvas(contentClone, {
      scale: 2,
      useCORS: true,
      backgroundColor: getComputedStyle(document.body).backgroundColor,
      logging: false,
    });

    // 导出为 JPG
    const jpgData = canvas.toDataURL('image/jpeg', 0.92);
    const fileBase = (S.currentPair || 'manual').replace(/\.json$/i, '');
    const filename = `${fileBase}_${side}_${S.viewMode}.jpg`;

    const a = document.createElement('a');
    a.href = jpgData;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    a.remove();

    showToast(`${side[0].toUpperCase() + side.slice(1)} image exported as JPG.`);
  } catch (err) {
    showToast(`Export failed: ${err.message}`, 'error');
  } finally {
    cloneWrap.remove();
  }
}

// ===================================================================
// PATH RESOLUTION
// ===================================================================
/**
 * Walk a path like $.foo.bar[0].baz into a JSON value.
 */
function resolvePathInData(data, path) {
  if (!data || !path || path === '$') return data;
  try {
    // Normalise: $.a.b[0].c  →  ['a','b','0','c']
    const segments = path
      .replace(/^\$\.?/, '')
      .replace(/\[(\d+)\]/g, '.$1')
      .split('.')
      .filter(Boolean);

    let cur = data;
    for (const seg of segments) {
      if (cur === null || cur === undefined) return undefined;
      cur = cur[seg];
    }
    return cur;
  } catch { return undefined; }
}

// ===================================================================
// SIDEBAR RESIZE
// ===================================================================
function setupSidebarResize() {
  const handle  = document.getElementById('sidebar-resize');
  const sidebar = document.getElementById('sidebar');
  let dragging  = false;
  let startX, startW;

  handle.addEventListener('mousedown', e => {
    dragging = true;
    startX = e.clientX;
    startW = sidebar.offsetWidth;
    handle.classList.add('dragging');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
  });

  document.addEventListener('mousemove', e => {
    if (!dragging) return;
    const w = Math.max(180, Math.min(640, startW + (e.clientX - startX)));
    sidebar.style.width = w + 'px';
  });

  document.addEventListener('mouseup', () => {
    if (!dragging) return;
    dragging = false;
    handle.classList.remove('dragging');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  });
}

// ===================================================================
// UTILITIES
// ===================================================================
function esc(str) {
  if (str === null || str === undefined) return '';
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

/** Escape for use inside a dotted path segment (no HTML escaping needed here, just safety). */
function esc2(str) {
  return str.replace(/\./g, '\\.');
}

function fmtSize(bytes) {
  if (bytes < 1024)        return bytes + ' B';
  if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
  return (bytes / (1024 * 1024)).toFixed(1) + ' MB';
}

/** Rough byte estimate without full serialisation on every call (uses JSON.stringify once). */
function roughSize(data) {
  try { return new TextEncoder().encode(JSON.stringify(data)).length; }
  catch { return 0; }
}

function setUploadBtnLabel(side, name) {
  const btn = document.getElementById(`upload-${side}-name`);
  btn.textContent = name;
  btn.classList.add('has-file');
}

let _toastTimer = null;
function showToast(msg, type = 'info') {
  const toast = document.getElementById('toast');
  toast.textContent = msg;
  toast.style.borderColor = type === 'error' ? 'var(--removed-border)'
    : type === 'warn' ? 'var(--modified-border)'
    : 'var(--border)';
  toast.classList.add('show');
  clearTimeout(_toastTimer);
  _toastTimer = setTimeout(() => toast.classList.remove('show'), 3000);
}

// ===================================================================
// BOOT
// ===================================================================
window.addEventListener('DOMContentLoaded', init);
