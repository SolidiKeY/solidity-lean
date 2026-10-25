// The examples viewer: `examples.json` lists the projects, and each project's
// `data/<id>/index.json` and per-file JSON are what `scripts/site/export.mjs`
// recorded from Lean's language server (`docs/site.md`). Nothing is checked
// here; the page only shows those answers, line by line.

const $ = (id) => document.getElementById(id);
const els = {
  project: $('project'), example: $('example'), code: $('code'), info: $('info'),
  title: $('title'), summary: $('summary'), source: $('source-link'), repo: $('repo-link'),
  about: $('about'), aboutOpen: $('about-open'), aboutRepo: $('about-repo'),
  aboutRecorded: $('about-recorded'), splitter: $('splitter'), workspace: $('workspace'),
};

const state = { config: null, indexes: new Map(), files: new Map(), project: null, entry: null, data: null, line: null };

const escapeHtml = (s) => s.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

// ------------------------------------------------------------ highlighting

const words = (s) => new Set(s.split(/\s+/).filter(Boolean));
const COMMANDS = words(`theorem lemma def example abbrev instance structure class inductive namespace
  section end open import variable universe set_option attribute private protected noncomputable
  partial unsafe local scoped macro macro_rules syntax notation infix infixl infixr prefix elab
  elab_rules deriving where extends mutual termination_by decreasing_by method prove_correct
  extract_program_for prove_precondition_decidable_for prove_postcondition_decidable_for derive_tester_for`);
const KEYWORDS = words(`fun λ let mut in if then else do return match with for while by have show
  from at calc this using suffices obtain require ensures invariant done_with decreasing
  break continue Type Prop Sort`);
const TACTICS = words(`apply exact intro intros simp simp_all simp_arith rfl rw rwa refine constructor
  cases rcases induction omega decide grind unfold split trivial assumption contradiction exfalso
  exists use left right specialize generalize subst congr ext funext norm_num linarith aesop
  first try repeat all_goals any_goals focus case next conv change show_term native_decide
  bv_decide loom_solve loom_smt done skip nofun nomatch injection`);
const SOLIDITY = words(`contract function returns uint uint8 uint16 uint32 uint64 uint128 uint256 int
  int8 int256 bool address mapping storage memory calldata public external internal payable view
  pure emit event modifier constructor struct revert assert transfer send msg sender value true
  false checked ignoringOverflow bytes string delete new try catch is super`);

/** Lean source to one HTML string per line. */
export function highlight(src) {
  const tokens = [];
  const push = (cls, text) => tokens.push([cls, text]);
  let i = 0;
  const n = src.length;
  const identStart = /[\p{L}_«]/u;
  const identChar = /[\p{L}\p{N}_'!?₀-₉ᵢ-ᵪⱼ.]/u;
  while (i < n) {
    const c = src[i];
    if (src.startsWith('/-', i)) {
      const doc = src[i + 2] === '-' || src[i + 2] === '!';
      let depth = 1, j = i + 2;
      while (j < n && depth) {
        if (src.startsWith('/-', j)) { depth++; j += 2; }
        else if (src.startsWith('-/', j)) { depth--; j += 2; }
        else j++;
      }
      push(doc ? 'doc' : 'comment', src.slice(i, j)); i = j;
    } else if (src.startsWith('--', i)) {
      let j = src.indexOf('\n', i); if (j < 0) j = n;
      push('comment', src.slice(i, j)); i = j;
    } else if (c === '"') {
      let j = i + 1;
      while (j < n && src[j] !== '"' && src[j] !== '\n') j += src[j] === '\\' ? 2 : 1;
      push('string', src.slice(i, j + 1)); i = j + 1;
    } else if (/[0-9]/.test(c) && !identChar.test(src[i - 1] ?? ' ')) {
      const m = /^(0x[0-9a-fA-F_]+|[0-9][0-9_]*(\.[0-9]+)?)/.exec(src.slice(i, i + 80));
      push('number', m[0]); i += m[0].length;
    } else if (c === '#' && /[a-z_]/.test(src[i + 1] ?? '')) {
      const m = /^#[a-z_A-Z?!]+/.exec(src.slice(i, i + 40));
      push('hash', m[0]); i += m[0].length;
    } else if (c === '@' && src[i + 1] === '[') {
      push('cmd', '@['); i += 2;
    } else if (identStart.test(c)) {
      let j = i;
      if (c === '«') { j = src.indexOf('»', i); j = j < 0 ? n : j + 1; }
      else while (j < n && identChar.test(src[j])) j++;
      const word = src.slice(i, j);
      const afterDot = src[i - 1] === '.';
      let cls = null;
      if (word === 'sorry' || word === 'admit') cls = 'sorry';
      else if (afterDot) cls = null;
      else if (COMMANDS.has(word)) cls = 'cmd';
      else if (KEYWORDS.has(word)) cls = 'kw';
      else if (TACTICS.has(word) || /^sol_[a-z_]+\??$/.test(word)) cls = 'tactic';
      else if (SOLIDITY.has(word)) cls = 'sol';
      else if (/^[A-Z]/.test(word)) cls = 'type';
      push(cls, word); i = j;
    } else {
      push(null, c); i++;
    }
  }
  const lines = [''];
  for (const [cls, text] of tokens) {
    text.split('\n').forEach((part, k) => {
      if (k > 0) lines.push('');
      if (!part) return;
      lines[lines.length - 1] += cls ? `<span class="tk-${cls}">${escapeHtml(part)}</span>` : escapeHtml(part);
    });
  }
  return lines;
}

function renderGoal(text, kind) {
  const html = text.split('\n').map((line) => {
    if (/^⊢/.test(line)) return `<span class="turnstile">⊢</span>${escapeHtml(line.slice(1))}`;
    if (/^case /.test(line)) return `<span class="case">${escapeHtml(line)}</span>`;
    const m = /^([^\s:][^:]*?) : /.exec(line);
    if (m && !/^\s/.test(line)) return `<span class="hyp-name">${escapeHtml(m[1])}</span>${escapeHtml(line.slice(m[1].length))}`;
    return escapeHtml(line);
  }).join('\n');
  return `<pre class="goal ${kind}">${html}</pre>`;
}

// ------------------------------------------------------------------- data

async function getJson(url) {
  const r = await fetch(url, { cache: 'no-cache' });
  if (!r.ok) throw new Error(`${url}: ${r.status}`);
  return r.json();
}

async function projectIndex(project) {
  if (!state.indexes.has(project.id)) {
    state.indexes.set(project.id, getJson(`data/${encodeURIComponent(project.id)}/index.json`).catch(() => null));
  }
  return state.indexes.get(project.id);
}

function entriesOf(project, index) {
  if (index) return index.examples;
  return project.examples.map((e) => ({ ...e, title: e.title ?? e.file.split('/').pop().replace(/\.lean$/, ''), status: 'missing' }));
}

// ----------------------------------------------------------------- routing

function readHash() {
  const p = new URLSearchParams(location.hash.slice(1));
  const line = Number(p.get('line'));
  return { project: p.get('project'), file: p.get('file'), line: Number.isInteger(line) && line > 0 ? line - 1 : null };
}

function writeHash() {
  const p = new URLSearchParams();
  if (state.project) p.set('project', state.project.id);
  if (state.entry) p.set('file', state.entry.file);
  if (state.line !== null) p.set('line', String(state.line + 1));
  const hash = `#${p.toString()}`;
  if (location.hash !== hash) history.replaceState(null, '', hash);
}

async function route() {
  const want = readHash();
  const projects = state.config.projects;
  const project = projects.find((p) => p.id === want.project) ?? projects[0];
  await selectProject(project, want.file, want.line);
}

// --------------------------------------------------------------- selection

async function selectProject(project, file = null, line = null) {
  state.project = project;
  els.project.value = project.id;
  const index = await projectIndex(project);
  const entries = entriesOf(project, index);
  els.example.replaceChildren();
  const groups = new Map();
  for (const e of entries) {
    const g = e.group ?? '';
    if (!groups.has(g)) {
      const og = document.createElement('optgroup');
      og.label = g || project.title;
      groups.set(g, og);
      els.example.append(og);
    }
    const opt = document.createElement('option');
    opt.value = e.file;
    opt.textContent = e.title + (e.status === 'ok' ? '' : e.status === 'missing' ? ' (not recorded)' : ` (${e.status})`);
    groups.get(g).append(opt);
  }
  const entry = entries.find((e) => e.file === file) ?? entries.find((e) => e.status !== 'missing') ?? entries[0];
  await selectExample(entry, index, line);
}

async function selectExample(entry, index, line = null) {
  state.entry = entry;
  state.line = null;
  els.example.value = entry.file;
  els.title.textContent = entry.title;
  els.summary.textContent = entry.summary ?? '';
  const repoUrl = state.config.repository;
  const root = state.project.root === '.' ? '' : `${state.project.root}/`;
  const rev = index?.commit ?? 'HEAD';
  els.source.href = `${repoUrl}/blob/${rev}/${root}${entry.file}`;
  document.title = `${entry.title} · solidity-lean examples`;
  els.aboutRecorded.innerHTML = index
    ? `This build was recorded with <code>${escapeHtml(index.toolchain)}</code> at commit <a href="${repoUrl}/commit/${index.commit}"><code>${escapeHtml(String(index.commit).slice(0, 10))}</code></a> on ${escapeHtml(new Date(index.recordedAt).toUTCString())}.`
    : '';

  state.data = null;
  if (entry.data) {
    const key = `${state.project.id}/${entry.data}`;
    if (!state.files.has(key)) state.files.set(key, getJson(`data/${encodeURIComponent(state.project.id)}/${encodeURIComponent(entry.data)}`).catch(() => null));
    state.data = await state.files.get(key);
  }
  if (state.entry !== entry) return; // another selection superseded this one
  renderCode();
  if (line !== null && state.data && line < state.data.source.split('\n').length) selectLine(line, true);
  else { renderOverview(); writeHash(); }
}

// ------------------------------------------------------------------ render

function messagesOn(line) {
  return (state.data?.messages ?? []).filter((m) => m.start.line <= line && line <= Math.max(m.start.line, m.end.line - (m.end.character === 0 && m.end.line > m.start.line ? 1 : 0)));
}

function worst(messages) {
  for (const s of ['error', 'warning', 'information', 'hint']) if (messages.some((m) => m.severity === s)) return s;
  return null;
}

function renderCode() {
  els.code.replaceChildren();
  if (!state.data) {
    const p = document.createElement('p');
    p.className = 'empty';
    p.style.padding = '16px';
    p.textContent = state.entry?.status === 'failed'
      ? `The language server failed on this file when the site was built: ${state.entry.error ?? ''}`
      : 'This example was not recorded in this build of the site.';
    els.code.append(p);
    return;
  }
  const lines = highlight(state.data.source);
  if (lines.length > 1 && lines[lines.length - 1] === '') lines.pop();
  const sev = new Map();
  for (let l = 0; l < lines.length; l++) {
    const s = worst(messagesOn(l));
    if (s) sev.set(l, s);
  }
  const frag = document.createDocumentFragment();
  lines.forEach((html, l) => {
    const div = document.createElement('div');
    div.className = 'ln';
    if (state.data.goals[l]) div.classList.add('has-goal');
    if (sev.has(l)) div.classList.add(`sev-${sev.get(l)}`);
    div.dataset.line = String(l);
    div.innerHTML = `<span class="no">${l + 1}</span><span class="tx">${html || ' '}</span>`;
    frag.append(div);
  });
  els.code.append(frag);
  els.code.scrollTop = 0;
}

function fileName() { return state.entry.file.split('/').pop(); }

function messageHtml(m, withJump) {
  const loc = `${fileName()}:${m.start.line + 1}:${m.start.character}`;
  return `<div class="msg ${m.severity}"><div class="msg-head"${withJump ? ` data-jump="${m.start.line}"` : ''}><span>${escapeHtml(loc)}</span><span class="sev">${m.severity}</span></div><pre>${escapeHtml(m.text)}</pre></div>`;
}

function allMessagesHtml(open) {
  const all = state.data?.messages ?? [];
  return `<details class="info-block"${open ? ' open' : ''}><summary>All Messages (${all.length})</summary><div class="info-body">${
    all.length ? all.map((m) => messageHtml(m, true)).join('') : '<p class="empty">No messages.</p>'}</div></details>`;
}

function recordedHtml() {
  return `<p class="recorded">Read-only: recorded from Lean's language server when the site was built. <a href="#" data-about>How to run it yourself</a></p>`;
}

function renderOverview() {
  const e = state.entry;
  const d = state.data;
  const goals = d ? Object.keys(d.goals).length : 0;
  const statusText = { ok: 'checked, no errors', errors: 'Lean reported errors', failed: 'not recorded (server failure)', missing: 'not recorded' }[e.status] ?? e.status;
  els.info.innerHTML = `<details class="info-block overview" open><summary>${escapeHtml(fileName())}</summary><div class="info-body">
    <dl>
      <dt>Project</dt><dd>${escapeHtml(state.project.title)}</dd>
      <dt>File</dt><dd><code>${escapeHtml(e.file)}</code></dd>
      <dt>Status</dt><dd class="status-${escapeHtml(e.status)}">${escapeHtml(statusText)}</dd>
      ${d ? `<dt>Elaboration</dt><dd>${(d.elapsedMs / 1000).toFixed(1)} s</dd><dt>Goals</dt><dd>${goals} lines with a goal</dd>` : ''}
    </dl>
    <p class="hint">Click a line (or use <kbd>↑</kbd> <kbd>↓</kbd>) to see the goal Lean shows with the cursor at its end, and the messages on it.</p>
  </div></details>${d ? allMessagesHtml(true) : ''}${recordedHtml()}`;
}

function renderInfo() {
  const l = state.line;
  const lineText = state.data.source.split('\n')[l] ?? '';
  const col = lineText.replace(/\s+$/, '').length;
  const g = state.data.goals[l];
  let goalHtml;
  if (!g) goalHtml = '<p class="empty">No goal at the end of this line.</p>';
  else if (g.kind === 'tactic') {
    goalHtml = g.goals.length
      ? `<p class="hint">${g.goals.length} goal${g.goals.length > 1 ? 's' : ''}</p>${g.goals.map((t) => renderGoal(t, 'tactic')).join('')}`
      : '<p class="empty">No goals</p>';
  } else goalHtml = renderGoal(g.goals[0], 'term');
  const here = messagesOn(l);
  els.info.innerHTML = `<details class="info-block" open><summary>${escapeHtml(fileName())}:${l + 1}:${col}</summary><div class="info-body">
      <h3>${g?.kind === 'term' ? 'Expected type' : 'Tactic state'}</h3>${goalHtml}
      <h3>Messages (${here.length})</h3>${here.length ? here.map((m) => messageHtml(m, false)).join('') : '<p class="empty">No messages on this line.</p>'}
    </div></details>${allMessagesHtml(false)}${recordedHtml()}`;
}

function selectLine(l, scroll) {
  if (!state.data) return;
  const rows = els.code.querySelectorAll('.ln');
  if (l < 0 || l >= rows.length) return;
  els.code.querySelector('.ln.sel')?.classList.remove('sel');
  rows[l].classList.add('sel');
  state.line = l;
  if (scroll) rows[l].scrollIntoView({ block: 'center' });
  renderInfo();
  writeHash();
}

// ------------------------------------------------------------------ events

els.code.addEventListener('click', (ev) => {
  const row = ev.target.closest('.ln');
  if (row) { selectLine(Number(row.dataset.line), false); els.code.focus({ preventScroll: true }); }
});
document.addEventListener('keydown', (ev) => {
  if (!state.data || ev.altKey || ev.ctrlKey || ev.metaKey) return;
  if (ev.target.closest?.('select, input, textarea, dialog')) return;
  const step = { ArrowDown: 1, ArrowUp: -1, j: 1, k: -1, PageDown: 20, PageUp: -20 }[ev.key];
  if (!step) return;
  ev.preventDefault();
  const rows = els.code.querySelectorAll('.ln');
  const next = Math.max(0, Math.min(rows.length - 1, (state.line ?? -1) + step));
  selectLine(next, false);
  rows[next].scrollIntoView({ block: 'nearest' });
});
els.info.addEventListener('click', (ev) => {
  const jump = ev.target.closest('[data-jump]');
  if (jump) selectLine(Number(jump.dataset.jump), true);
  if (ev.target.closest('[data-about]')) { ev.preventDefault(); els.about.showModal(); }
});
els.project.addEventListener('change', () => {
  const project = state.config.projects.find((p) => p.id === els.project.value);
  selectProject(project);
});
els.example.addEventListener('change', async () => {
  const index = await projectIndex(state.project);
  const entry = entriesOf(state.project, index).find((e) => e.file === els.example.value);
  selectExample(entry, index);
});
els.aboutOpen.addEventListener('click', () => els.about.showModal());
window.addEventListener('hashchange', () => {
  const want = readHash();
  if (want.project !== state.project?.id || want.file !== state.entry?.file) route();
  else if (want.line !== null && want.line !== state.line) selectLine(want.line, true);
});

els.splitter.addEventListener('pointerdown', (ev) => {
  els.splitter.setPointerCapture(ev.pointerId);
  els.splitter.classList.add('dragging');
  const rect = els.workspace.getBoundingClientRect();
  const move = (e) => {
    const pct = Math.min(80, Math.max(25, ((e.clientX - rect.left) / rect.width) * 100));
    els.workspace.style.setProperty('--split', `${pct}%`);
  };
  const up = () => {
    els.splitter.classList.remove('dragging');
    els.splitter.removeEventListener('pointermove', move);
    els.splitter.removeEventListener('pointerup', up);
  };
  els.splitter.addEventListener('pointermove', move);
  els.splitter.addEventListener('pointerup', up);
});

// -------------------------------------------------------------------- boot

(async () => {
  try {
    state.config = await getJson('examples.json');
  } catch (e) {
    els.title.textContent = 'Could not load the examples.';
    els.summary.textContent = String(e.message ?? e);
    return;
  }
  els.repo.href = state.config.repository;
  els.aboutRepo.href = state.config.repository;
  for (const p of state.config.projects) {
    const opt = document.createElement('option');
    opt.value = p.id;
    opt.textContent = p.title;
    els.project.append(opt);
  }
  await route();
})();
