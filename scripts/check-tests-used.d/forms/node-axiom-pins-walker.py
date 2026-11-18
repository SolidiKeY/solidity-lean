# H1234 (gh#1544, Q-X1ERR-7, Option C), form (1): the Node walker of the CI
# axiom-pin check. consumer_routes section axiom_pin_walker_reads, one row per
# reviewed source:
#   {runner: W, frames: [{path: W, blob, line}], form: 'node-axiom-pins-walk',
#    target, target_blob, purpose}
# W is a current CI root (kind 'CI', command exactly `node W`, cwd '.') in a
# top-level directory, so `resolve(dirname(fileURLToPath(import.meta.url)),
# "..")` is the checkout root. The H978 node-readFileSync-walk form does not
# accept this shape (the walker is an exported function called from main), so
# the walk is re-derived from W's measured bytes here, line by line:
# - one column-0 `export function collect(root) {` at brace depth 0 whose body is
#   exactly AXPIN_COLLECT_BODY (an unconditional recursive walk of Solidity/,
#   Bridge/ and tests/ that skips only `.lake`, Solidity/Scratch, dot paths,
#   vendor and node_modules and collects every `.lean` file, then reads each
#   with readFileSync(join(root, file), "utf8"), the frame line);
# - readFileSync/readdirSync/statSync from node:fs, join from node:path, and
#   `collect` never rebound;
# - `const main = process.argv[1] && resolve(process.argv[1]) ===
#   fileURLToPath(import.meta.url);` once at top level, `if (main &&
#   process.argv.includes("--fragment-op")) {` at depth 0 and its own `} else
#   if (main) {` whose first two statements are `const root = resolve(dirname(
#   fileURLToPath(import.meta.url)), "..");` and `const found = collect(root);`;
# - nothing in W before that `if` (collect, pins and every other definition
#   included) shows a way to end the run early: the form (a) audit
#   node_producer_quiet (no exit/abort/kill/reallyExit name, `process` only as
#   argv/env/exitCode, no process module, also in template substitutions);
#   no depth-0 statement there throws or calls a function W defines;
# - W's local static imports are exactly the reviewed modules, each importing
#   only node: built-ins and passing the same audit (they are evaluated first).
# So `node W` with no argument runs collect(root) before anything that can stop
# it, and a completed walk read every tracked `.lean` file under tests/ that no
# skip rule names. A row also needs the target to hold a lexical `#guard_msgs
# [(opts)] in #print axioms X` outside comments and strings (the pin W checks)
# and the inventory W compares against (AXPIN_INVENTORY, the literal `const
# INVENTORY` of W) to record at least one pin of that source, so the read is
# the pin comparison the CI step performs, not an incidental scan; an inventory
# that is missing, invalid or no longer records the source makes the row stale.
# Opt-in twice by exact tuple: the walker (W, blob, read line, ((import, blob),
# ...)) in REVIEWED_AXIOM_PIN_WALKERS and the source (target, blob) in
# REVIEWED_AXIOM_PIN_READS; anything else is rejected. A changed W, import or
# target object, or no such CI root, makes the row stale (no credit, no error).
# Consumption credit only: no pass, proof, elaboration, axiom-audit or
# runtime credit for the target, and nothing for any other path W reads.
# Reviewed on master abec4d99 (W blob c2e71772, CI root .github/workflows/
# trust.yml:60 `node scripts/check-axiom-pins.mjs`, run here at abec4d99:
# 17932 pins found, no pin error). Admitted: the 48 B3 sources of the retired
# x1e-classify-rest-rest list (02e437a0) that hold such pins and are recorded in
# scripts/g07-axiom-pins.json: roadmap-g19 (23), roadmap-g36 (14),
# v14-constructor (8), calldata-packets-1105/RawInt/Axioms.lean,
# sol-constant-depth/Axioms.lean and v14-help/IntegerReadBoundaryAxioms.lean.
# Refused, left unresolved: primitive-packets-1105/BitNot/Signatures.lean (no
# #print axioms) and roadmap-v16/CalculusControls.lean (bare `#print axioms`
# without #guard_msgs, so W finds no pin), and every other B3 source (no pin).
import json, posixpath, shlex
(FORM_CONTROLS, _check_lines, _current, _frames_current, _js_code, _js_destructured, _js_imported,
 _js_mask, _node_import, _observe, _plain_lines, canonical, register_consumer_section) = (globals()[name] for name in (
    'FORM_CONTROLS', '_check_lines', '_current', '_frames_current', '_js_code', '_js_destructured', '_js_imported',
    '_js_mask', '_node_import', '_observe', '_plain_lines', 'canonical', 'register_consumer_section'))
AXPIN_SECTION = 'axiom_pin_walker_reads'
AXPIN_FORM = 'node-axiom-pins-walk'
AXPIN_OPERATION = 'Node readFileSync of each .lean file the CI axiom-pin walker collect() yields, compared with the recorded pin inventory'
AXPIN_WALKER = 'scripts/check-axiom-pins.mjs'
AXPIN_WALKER_BLOB = 'c2e7177225ba3963a4a919c2a178bd4fbedd80f2'
AXPIN_COLLECT_BODY = (
    'const files = [];',
    '(function walk(dir) {',
    'for (const f of readdirSync(join(root, dir)).sort()) {',
    'const p = dir ? join(dir, f) : f;',
    'if (f === ".lake" || p === "Solidity/Scratch" || p.startsWith(".") || p === "vendor" || p === "node_modules") continue;',
    'if (statSync(join(root, p)).isDirectory()) { if (!dir && !["Solidity", "Bridge", "tests"].includes(p)) continue; walk(p); }',
    'else if (p.endsWith(".lean")) files.push(p);',
    '}',
    '})("");',
    'const found = new Map();',
    'for (const file of files) for (const pin of pins(readFileSync(join(root, file), "utf8")))',
    'found.set(`${file}:${pin.name}`, { ...pin, file });',
    'return found;',
    '}')
AXPIN_READ_OFFSET = 11  # the read is body line 11 after the header
AXPIN_MAIN = 'const main = process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url);'
AXPIN_FRAGMENT_IF = 'if (main && process.argv.includes("--fragment-op")) {'
AXPIN_MAIN_BRANCH = ('} else if (main) {', 'const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");', 'const found = collect(root);')
AXPIN_INVENTORY = 'scripts/g07-axiom-pins.json'
AXPIN_PIN = re.compile(r'#guard_msgs\s*(?:\([^)]*\)\s*)?in\s+#print\s+axioms\s+\S')
# (walker, blob, read line, ((local import, blob), ...))
REVIEWED_AXIOM_PIN_WALKERS = frozenset({
    (AXPIN_WALKER, AXPIN_WALKER_BLOB, 237, (('scripts/axiom-pin-drift-baseline.mjs', '80d23606e0cdaf3c2b21e9dffda0c9171d1c0dcc'),
                                            ('scripts/check-trust.mjs', '9a4e8eb53b3a1fb68d7ef8ac8c439600475b7e2d')))})
_AXPIN_SOURCES = '''
calldata-packets-1105/RawInt/Axioms.lean 6469fce6ff30fef4a8e12ff12bb2a52c5d053960
roadmap-g19/AssignmentBlocksAxioms.lean 2108f12166bfd9f0640484aac119df0ccfdf667b
roadmap-g19/AssignmentBlocksCompilerAxioms.lean 78b87ac5001bb8db355a7f57a12115c63b6be9b2
roadmap-g19/AssignmentDoWhileBreakAxioms.lean 2b3f0520a8f36c4a89e443eefa1795fc55b6bc8d
roadmap-g19/AssignmentDoWhileContinueAxioms.lean bd831de3287b5b7e601b519c15ce2f7578d7d8d5
roadmap-g19/AssignmentDoWhileReturnAxioms.lean 565af0a37b931db6202ddb73a58118db8fbdc443
roadmap-g19/AssignmentForBreakAxioms.lean 8bdadc5643a9df45d732b9ea0ce7524dd33971fc
roadmap-g19/AssignmentForContinueAxioms.lean 697f8fb445695e1dec8d706b3aef0be9b827898a
roadmap-g19/AssignmentForReturnAxioms.lean f22e7d985be3c692752a61a66f8044741c4d3236
roadmap-g19/AssignmentReturnFlagAxioms.lean d6069a896ebdb255545273dd572202b98645958b
roadmap-g19/AssignmentWhileBreakAxioms.lean c66727dfa0af3af97e54fac0641a9f11e086cbaa
roadmap-g19/AssignmentWhileContinueAxioms.lean 21bb10563749d11b5124ee4a1b2446e0e493b50b
roadmap-g19/AssignmentWhileResetAxioms.lean 5a9dc7620c5ef72ba8df8ce3cc8b67b23ef87429
roadmap-g19/ConditionalContinuationCompilerAxioms.lean 7818edb347b6937e385ccfa7add58c81ea1823bc
roadmap-g19/ConditionalReturnAxioms.lean 4ca1ed93ff08036bc3996f4065b6977ef96d8527
roadmap-g19/ConditionalReturnCompilerAxioms.lean 4c87c95f48ff7333a9d253f9d10bca63ce1afb65
roadmap-g19/ConditionalReturnContinuationAxioms.lean f574ff152373e1b39b32c71b4fb2062015b83db7
roadmap-g19/ConditionalSequenceAxioms.lean 5bd8b9e319babe71c84a7508401c67a7996475d4
roadmap-g19/ConditionalStatementAxioms.lean b465130a3da147e572f193bd025d2d44d62e4a6e
roadmap-g19/DoWhileReturnCompilerAxioms.lean 6dc2a5823f7b125e0d0ca3485bfee4c48e495828
roadmap-g19/ReturnPairAxioms.lean 9911778afbf180a004f2439c7850e0345612828c
roadmap-g19/ReturnPairCompilerAxioms.lean 41fedb8daa4e85e34a5cd2ad408b8970562d6287
roadmap-g19/ReturnTailAxioms.lean 509143b1a695f3511fbd1883b3e810f62de29382
roadmap-g19/WhileReturnAxioms.lean 21f2105846dfb67361ef5f526a9d28e72fd2161b
roadmap-g36/ConditionalSequenceCompilerAxioms.lean e29cd74bc1f1f5ec42b8c50df9a06095cfacd110
roadmap-g36/ConditionalSourceCompilerAxioms.lean 15ed41893dbe2ed685e25d4e01ecb7d1eda55cad
roadmap-g36/DoWhileBreakCompilerAxioms.lean 2e9ab0207b0eddfe2eb2bc7849fc1d3649ef7a0a
roadmap-g36/DoWhileContinueCompilerAxioms.lean aa874e383da5c597cc3118db5325daed5bf54795
roadmap-g36/ForBreakCompilerAxioms.lean 8fd09cf3ab42f36f14986826d6b657236e01ee35
roadmap-g36/ForContinueCompilerAxioms.lean 399a81db617760e2173d64f07e6cfabdb5f85e81
roadmap-g36/ForReturnCompilerAxioms.lean 43b8fa496644b0baff84188625bdbea010f62f43
roadmap-g36/MappedBranchAxioms.lean cf2a3f1257cee2a2e71940fde6d27cc4a7a23d30
roadmap-g36/MappedConditionAxioms.lean 6f2862cc4d4d4c9294a8ab33174e9f138aed758d
roadmap-g36/ReturnTailCompilerAxioms.lean bf06230d100d8d80d625a47054f3544eeffd3699
roadmap-g36/ScopedMappedSequenceAxioms.lean 0749d1a71c0466e14a272f9e3dd8a8c4b37baeeb
roadmap-g36/WhileBreakCompilerAxioms.lean c5295b99135d602d839d90542e4d0554fcd30d25
roadmap-g36/WhileContinueCompilerAxioms.lean 91afc2d07404ff7747383879390350c4f886e395
roadmap-g36/WhileReturnCompilerAxioms.lean 44dc9126a68bae14d7975d7b5715d20a14ceb733
sol-constant-depth/Axioms.lean e9709ce41bae879efb65809e37498a24fc1a6557
v14-constructor/Axioms.lean 479b5cf0bdae0fa45c159368883fd9e9cf8e1231
v14-constructor/BaseAxioms.lean 05e75b06f19ce1ede8f1642311b5bc6ff8f70412
v14-constructor/FailureAxioms.lean b307b3def0a3ec5d9336d706db892d7dd8700674
v14-constructor/FreshnessAxioms.lean b1939278b9433d3a60ceda50bddcda8a324998c9
v14-constructor/InitializationAxioms.lean fc9968f44a78fe9a05ae93586e107123b0ab3e13
v14-constructor/LinkIdentityAxioms.lean 5e3f74ab79eb7c1d55dd9fcfd4bbeffeb59b2560
v14-constructor/PatchOrderAxioms.lean cf70201f4236fd4f2a7a3993dfed8d82ddaf7c6d
v14-constructor/StorageFailureAxioms.lean 3506052df74f26c94ed9c6ca1ce338a6401685c4
v14-help/IntegerReadBoundaryAxioms.lean f127a2b250f5780a9956907c8558404a97e52a97
'''
REVIEWED_AXIOM_PIN_READS = frozenset(('tests/' + p, b) for p, b in (line.split() for line in _AXPIN_SOURCES.split('\n') if line))


def _axpin_depths(code):
    """Brace depth of masked code at the start of each line (index n-1 for line n)."""
    depths = []; depth = 0
    for line in code.split('\n'):
        depths.append(depth)
        for c in line:
            if c == '{': depth += 1
            elif c == '}': depth -= 1
            if depth < 0: return None
    return depths


def axiom_pin_walker(text):
    """W's read line if text shows the reviewed walk run from main (see above), else None.

    Returns (read line, local import paths relative to W's directory as written)."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code, _ = _js_mask(text, True); lines = text.split('\n'); masked = code.split('\n')
    if len(masked) != len(lines): return None
    depths = _axpin_depths(code)
    if depths is None: return None
    def code_line(n, expected):
        """Line n is, stripped, exactly expected and is code, not comment or template text."""
        if lines[n - 1].strip() != expected: return False
        if '`' in expected: return masked[n - 1].strip().startswith(expected[:expected.index('`')])
        found = _js_code(text, n)
        return found is not None and found[0].strip() == expected
    heads = [n for n, line in enumerate(lines, 1) if line == 'export function collect(root) {']
    if len(heads) != 1 or not code_line(heads[0], 'export function collect(root) {') or depths[heads[0] - 1] != 0: return None
    head = heads[0]
    if head + len(AXPIN_COLLECT_BODY) > len(lines): return None
    if not all(code_line(head + k, body) for k, body in enumerate(AXPIN_COLLECT_BODY, 1)): return None
    if depths[head + len(AXPIN_COLLECT_BODY)] != 0 or len(re.findall(r'\bfunction\s+collect\b', code)) != 1: return None
    if (re.search(r'(?<![\w$.])collect\s*=(?!=)', code) or _js_destructured(code, 'collect')
            or not _js_imported(text, code, ('readFileSync', 'readdirSync', 'statSync'), 'fs') or not _js_imported(text, code, ('join', 'resolve', 'dirname'), 'path')
            or not _js_imported(text, code, ('fileURLToPath',), 'url')):
        return None
    inventories = [n for n, line in enumerate(lines, 1) if line == 'const INVENTORY = ' + json.dumps(AXPIN_INVENTORY) + ';']
    if (len(inventories) != 1 or not code_line(inventories[0], lines[inventories[0] - 1]) or depths[inventories[0] - 1] != 0
            or len(re.findall(r'(?<![\w$.])INVENTORY\s*=(?!=)', code)) != 1 or _js_destructured(code, 'INVENTORY')):
        return None
    mains = [n for n, line in enumerate(lines, 1) if line == AXPIN_MAIN]
    if len(mains) != 1 or not code_line(mains[0], AXPIN_MAIN) or depths[mains[0] - 1] != 0: return None
    if len(re.findall(r'(?<![\w$.])main\s*=(?!=)', code)) != 1 or _js_destructured(code, 'main') or re.search(r'\b(?:function|let|var|class)\s+main\b', code):
        return None
    ifs = [n for n, line in enumerate(lines, 1) if line == AXPIN_FRAGMENT_IF]
    branches = [n for n, line in enumerate(lines, 1) if line == AXPIN_MAIN_BRANCH[0]]
    if len(ifs) != 1 or len(branches) != 1 or not code_line(ifs[0], AXPIN_FRAGMENT_IF) or not code_line(branches[0], AXPIN_MAIN_BRANCH[0]): return None
    opener, branch = ifs[0], branches[0]
    if not mains[0] < opener < branch or depths[opener - 1] != 0 or depths[branch - 1] != 1:
        return None
    if any(depths[n - 1] == 0 and masked[n - 1].strip() for n in range(opener + 1, branch)): return None  # the else closes that if
    following = [n for n in range(branch + 1, len(lines) + 1) if masked[n - 1].strip()][:2]
    if len(following) != 2 or not all(code_line(n, e) for n, e in zip(following, AXPIN_MAIN_BRANCH[1:])): return None
    # Everything before the opener (collect, pins and every other definition included): no way to end the
    # run early (the form (a) audit node_producer_quiet, also inside template substitutions).
    if not node_producer_quiet('\n'.join(lines[:opener - 1])): return None
    top = '\n'.join(m for n, m in enumerate(masked[:opener - 1], 1) if depths[n - 1] == 0)
    if re.search(r'(?<![\w$])(?:exit|abort|kill|reallyExit|throw)(?![\w$])|(?<![\w$])process(?![\w$])(?!\s*\.\s*argv(?![\w$]))', top): return None
    local = set(re.findall(r'\bfunction\s+([\w$]+)', code)) | set(re.findall(r'\b(?:const|let|var)\s+([\w$]+)\s*=\s*(?:async\s*)?(?:\([^()]*\)|[\w$]+)\s*=>', code))
    for name in local:
        if re.search(r'(?<![\w$.])' + re.escape(name) + r'\s*\((?![^()\n]*\)\s*\{)', re.sub(r'\bfunction\s+[\w$]+', ' ', top)): return None
    # Static imports: each column-0 line is a node: built-in or a literal relative module.
    imports = []
    for n in range(1, len(lines) + 1):
        if not re.match(r'import\b', masked[n - 1]): continue
        found = re.fullmatch(r'import\s*\{[^{}]*\}\s*from\s*"(node:[\w/]+|\.{1,2}/[^"\\]+\.mjs)";', lines[n - 1])
        if found is None or n > opener or _node_import('W', text, n) is None and not found[1].startswith('node:'): return None
        if not found[1].startswith('node:'): imports.append(found[1])
    if re.search(r'(?<![\w$.])(?:import\s*\(|createRequire\b)', code): return None
    return head + AXPIN_READ_OFFSET, sorted(imports)


def _axpin_builtin_only(text):
    """Every static import of text is a node: built-in (its top level runs first)."""
    if not isinstance(text, str) or not _plain_lines(text): return False
    code, _ = _js_mask(text, True)
    specifiers = re.findall(r'(?m)^\s*import\b[^;]*?\bfrom\s*["\']([^"\']+)["\']|^\s*import\s*["\']([^"\']+)["\']', text)
    # In an ES module `require` is a local name; createRequire would load CommonJS, so it is refused.
    return (not re.search(r'(?<![\w$.])(?:import\s*\(|createRequire\b)', code)
            and all((a or b).startswith('node:') for a, b in specifiers))


def _axpin_inventory(repo, cache):
    """Pin sources recorded in the inventory W compares against, from the measured tree."""
    if 'sources' not in cache:
        sources = set()
        if AXPIN_INVENTORY in repo.texts:
            try: recorded = json.loads(repo.texts[AXPIN_INVENTORY])
            except ValueError: recorded = None
            if isinstance(recorded, dict):
                sources = {k[:k.index('.lean:') + 5] for k in recorded if isinstance(k, str) and '.lean:' in k}
        cache['sources'] = sources
    return cache['sources']


def axiom_pin_walker_reads(classifier, graph, rows, walkers=None, reads=None):
    """H1234 (1): exact reads of pinned Lean sources by the CI axiom-pin walker."""
    repo = graph.repo; cache = {}
    walkers = REVIEWED_AXIOM_PIN_WALKERS if walkers is None else walkers
    reads = REVIEWED_AXIOM_PIN_READS if reads is None else reads
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'frames', 'form', 'target', 'target_blob', 'purpose'} or row['form'] != AXPIN_FORM
                or not isinstance(row['runner'], str) or not isinstance(row['target'], str) or not isinstance(row['target_blob'], str)
                or not isinstance(row['purpose'], str) or not row['purpose'].strip()):
            raise ValueError('invalid axiom-pin walker route')
        frames = row['frames']; target = row['target']; w = row['runner']
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        if len(frames) != 1 or frames[0]['path'] != w: raise ValueError('axiom-pin walker route must be one frame in its walker')
        frame = frames[0]
        reviewed = [r for r in walkers if r[:3] == (w, frame['blob'], frame['line'])]
        if len(reviewed) != 1: raise ValueError('unreviewed axiom-pin walker: ' + w)
        if (target, row['target_blob']) not in reads: raise ValueError('unreviewed axiom-pin walker read: ' + target)
        if not all(_current(repo, p, b) for p, b in reviewed[0][3]): continue
        root = graph.roots.get(w)
        try: words = shlex.split(root['command']) if root else None
        except ValueError: words = None
        if (root is None or 'derived_from' in root or root.get('source_only') or root.get('kind') != 'CI' or root.get('path') != w
                or root.get('cwd', '.') != '.' or words != ['node', w]): continue
        _check_lines(repo, frames)
        shape = axiom_pin_walker(repo.texts.get(w))
        if posixpath.dirname(w) == '' or '/' in posixpath.dirname(w) or shape is None or shape[0] != frame['line']:
            raise ValueError('axiom-pin walker is not the reviewed collect() walk run from main')
        local = sorted(posixpath.normpath(posixpath.join(posixpath.dirname(w), m)) for m in shape[1])
        if local != sorted(p for p, _ in reviewed[0][3]) or not all(_axpin_builtin_only(repo.texts.get(p)) and node_producer_quiet(repo.texts[p]) for p in local):
            raise ValueError('axiom-pin walker imports are not the reviewed built-in-only modules')
        parts = target.split('/')
        if (parts[0] != 'tests' or not target.endswith('.lean') or '.lake' in parts
                or repo.tree[target][0] not in ('100644', '100755') or target not in repo.texts):
            raise ValueError('axiom-pin walker target is not a tracked .lean file the walk collects')
        if not AXPIN_PIN.search(classifier['lean_code'](repo.texts[target])): raise ValueError('axiom-pin walker target has no #guard_msgs pin: ' + target)
        if target not in _axpin_inventory(repo, cache): continue  # inventory missing, invalid or not recording it: stale
        if classifier['excluded'](target) or classifier['excluded'](w): continue
        _observe(graph, w, row, frames, target, AXPIN_OPERATION, 'consumes', 'none',
                 {'kind': 'axiom-pin-walk', 'purpose': row['purpose'], 'ci_command': root['command'], 'inventory': AXPIN_INVENTORY})


register_consumer_section(AXPIN_SECTION, ('runner', 'form', 'target', 'frames'), True,
                          lambda c, g, _, rows: axiom_pin_walker_reads(c, g, rows))


def axiom_pin_walker_controls(env):
    """H1234 (1) controls: the reviewed tables, a synthetic CI walker credited
    only with both reviews and a recorded pin, and the refused shapes."""
    global REVIEWED_AXIOM_PIN_WALKERS, REVIEWED_AXIOM_PIN_READS
    commit, run, rejected, blob = (env[k] for k in ('commit', 'run', 'rejected', 'blob'))
    assert len(REVIEWED_AXIOM_PIN_WALKERS) == 1 and len(REVIEWED_AXIOM_PIN_READS) == 48
    assert all(p.startswith('tests/') and p.endswith('.lean') and re.fullmatch('[0-9a-f]{40}', b) for p, b in REVIEWED_AXIOM_PIN_READS)
    assert len({p for p, _ in REVIEWED_AXIOM_PIN_READS}) == 48 and next(iter(REVIEWED_AXIOM_PIN_WALKERS))[:3] == (AXPIN_WALKER, AXPIN_WALKER_BLOB, 237)
    W, H = 'scripts/pins.mjs', 'scripts/pinhelp.mjs'
    body = '\n'.join('  ' * k + line for k, line in zip((1, 1, 2, 3, 3, 3, 3, 2, 1, 1, 1, 2, 1), AXPIN_COLLECT_BODY[:-1]))
    walker = ('import { readFileSync, readdirSync, statSync } from "node:fs";\nimport { join, resolve, dirname } from "node:path";\n'
              'import { fileURLToPath } from "node:url";\nimport { blankLean } from "./pinhelp.mjs";\n\n'
              'const INVENTORY = "scripts/g07-axiom-pins.json";\n'
              'export function pins(text) {\n  return blankLean(text).includes("#print axioms") ? [{ name: "x" }] : [];\n}\n\n'
              'export function collect(root) {\n' + body + '\n}\n\n' + AXPIN_MAIN + '\n' + AXPIN_FRAGMENT_IF + '\n  process.exit(2);\n'
              + AXPIN_MAIN_BRANCH[0] + '\n  ' + AXPIN_MAIN_BRANCH[1] + '\n  ' + AXPIN_MAIN_BRANCH[2] + '\n  console.log(found.size, INVENTORY);\n}\n')
    read = walker.split('\n').index('export function collect(root) {') + 1 + AXPIN_READ_OFFSET
    assert axiom_pin_walker(walker) == (read, ['./pinhelp.mjs']) and 'readFileSync(join(root, file)' in walker.split('\n')[read - 1]
    for old, new in (('  const files = [];\n', '  const files = [];\n  return new Map();\n'),                        # early return in the walk
                     ('  const found = collect(root);', '  const found = new Map();'),                             # walk never called
                     (AXPIN_MAIN_BRANCH[0], '}\nif (main) {'),                                                     # not the else branch
                     ('export function collect(root) {\n', 'export function collect(root) {\n  if (root) return new Map();\n'),
                     ('const INVENTORY', 'process.exit(0);\nconst INVENTORY'), ('const INVENTORY', 'pins("x");\nconst INVENTORY'),
                     ('const INVENTORY', 'throw Error("x");\nconst INVENTORY'), ('const INVENTORY', 'const q = process;\nconst INVENTORY'),
                     ('export function collect', '/*\n*/ export function collect'), ('export function collect', 'export function collect2(root) {}\nfunction collect'),
                     ('const INVENTORY = "scripts/g07-axiom-pins.json"', 'const INVENTORY = "scripts/other.json"'),
                     ('import { blankLean', 'import "./side.mjs";\nimport { blankLean'), ('const INVENTORY', 'const m = await import("./y.mjs");\nconst INVENTORY'),
                     ('const INVENTORY', 'collect = () => new Map();\nconst INVENTORY'), ('\n', '\r\n'),
                     ('const INVENTORY', 'if (true) {\n  process.exit(0);\n}\nconst INVENTORY'), ('const INVENTORY', 'try {\n  process.exit(0);\n} finally {}\nconst INVENTORY'),
                     ('const INVENTORY', 'const s = `${process.exit(0)}`;\nconst INVENTORY'),
                     ('  return blankLean(text)', '  if (!text) process.exit(0);\n  return blankLean(text)')):
        assert walker.count(old) >= 1 and axiom_pin_walker(walker.replace(old, new, 1 if old != '\n' else -1)) is None, old
    assert axiom_pin_walker(None) is None and _axpin_builtin_only('import {x} from "node:fs";\nexport const y = 1;\n')
    assert not node_producer_quiet('import {x} from "node:fs";\nprocess.exit(0);\n')  # a helper that exits is refused too
    for t in ('import {x} from "./x.mjs";\n', 'const m = await import("node:fs");\n', 'import {createRequire} from "node:module";\n', 'import "./x.mjs";\n'):
        assert not _axpin_builtin_only(t), t
    pin = lambda name: "/-- info: '" + name + "' depends on axioms: [propext] -/\n#guard_msgs in\n#print axioms " + name + '\n'
    files = {W: walker, 'scripts/pins-arg.mjs': walker, H: 'import { readFileSync } from "node:fs";\nexport const blankLean = t => t;\n',
             '.github/workflows/pins.yml': 'jobs:\n  t:\n    steps:\n      - run: node scripts/pins.mjs\n      - run: node scripts/pins-arg.mjs --write\n',
             'scripts/g07-axiom-pins.json': json.dumps({p + ':Foo.' + n: ['propext'] for p, n in (('tests/ax/A.lean', 'a'), ('tests/ax/Bare.lean', 'b'),
                                                                                                ('tests/ax/Comment.lean', 'c'), ('docs/D.lean', 'd'))}),
             'tests/ax/A.lean': pin('Foo.a'), 'tests/ax/Bare.lean': '#print axioms Foo.b\n', 'tests/ax/Comment.lean': '/- ' + pin('Foo.c') + '-/\n',
             'tests/ax/Unrecorded.lean': pin('Foo.u'), 'tests/ax/data.txt': pin('Foo.t'), 'docs/D.lean': pin('Foo.d')}
    wc = commit(files, 'axiom pin walker'); later = commit({'tests/unrelated.txt': 'axpin later\n'}, 'axiom pin walker later')
    A = 'tests/ax/A.lean'; helper = ((H, blob(wc, H)),)
    row = lambda target=A, runner=W, line=read, **k: dict({'runner': runner, 'frames': [{'path': runner, 'blob': blob(wc, runner), 'line': line}],
                                                           'form': AXPIN_FORM, 'target': target, 'target_blob': blob(wc, target), 'purpose': 'Synthetic pin read.'}, **k)
    reads = lambda *rows: {AXPIN_SECTION: list(rows)}
    saved = REVIEWED_AXIOM_PIN_WALKERS, REVIEWED_AXIOM_PIN_READS
    try:
        base_model, base = run(later)
        assert base[A]['class'] != 'keep' and base_model['entry_points'][W]['kind'] == 'CI'
        rejected(later, 'unreviewed axiom-pin walker', reads(row()))
        REVIEWED_AXIOM_PIN_WALKERS = frozenset({(W, blob(wc, W), read, helper), ('scripts/pins-arg.mjs', blob(wc, W), read, helper)})
        rejected(later, 'unreviewed axiom-pin walker read', reads(row()))
        REVIEWED_AXIOM_PIN_READS = frozenset((p, blob(wc, p)) for p in files if p.endswith(('.lean', '.txt')))
        model, rows = run(later, reads(row()))
        chain = rows[A]['runner_chain']
        assert rows[A]['class'] == 'keep' and chain['entry']['derived_from'] == W and chain['entry']['consumer_route']['kind'] == 'axiom-pin-walk'
        assert chain['edges'][-1]['operation'] == AXPIN_OPERATION and chain['edges'][-1]['line'] == read
        assert sorted(p for p, r in rows.items() if canonical(r) != canonical(base[p])) == [A]  # one read only
        assert run(later, reads(row('tests/ax/Unrecorded.lean')))[1]['tests/ax/Unrecorded.lean']['class'] != 'keep'  # not recorded: stale
        for target in ('tests/ax/Bare.lean', 'tests/ax/Comment.lean'):
            rejected(later, 'no #guard_msgs pin', reads(row(target)))
        for target in ('tests/ax/data.txt', 'docs/D.lean'):
            rejected(later, 'tracked .lean file the walk collects', reads(row(target)))
        for bad, message in ((row(form='node-readFileSync-walk'), 'invalid axiom-pin walker route'), (dict(row(), extra=1), 'invalid axiom-pin walker route'),
                             (row(purpose=' '), 'invalid axiom-pin walker route'), (row(line=read - 1), 'unreviewed axiom-pin walker'),
                             (dict(row(), frames=row()['frames'] * 2), 'must be one frame'), (row(runner=H, line=1), 'must be one frame')):
            if bad['runner'] == H: bad['frames'] = row()['frames']
            rejected(later, message, reads(bad))
        # A CI command with an argument, or no CI root at all: no credit, no error.
        assert run(later, reads(row(runner='scripts/pins-arg.mjs')))[1][A]['class'] != 'keep'
        REVIEWED_AXIOM_PIN_WALKERS = frozenset({(W, blob(wc, W), read, ())})
        rejected(later, 'built-in-only modules', reads(row()))
        REVIEWED_AXIOM_PIN_WALKERS = frozenset({(W, blob(wc, W), read, helper)})
        # Changed target, walker import or workflow: stale, no credit, no error.
        changed = commit({A: pin('Foo.a') + '-- changed\n'}, 'axpin target changed')
        assert run(changed, reads(row()))[1][A]['class'] != 'keep'
        restored = commit({A: pin('Foo.a'), H: files[H] + '// changed\n'}, 'axpin helper changed')
        assert run(restored, reads(row()))[1][A]['class'] != 'keep'
        unrooted = commit({H: files[H], '.github/workflows/pins.yml': 'jobs:\n  t:\n    steps:\n      - run: echo none\n'}, 'axpin no root')
        assert run(unrooted, reads(row()))[1][A]['class'] != 'keep'
        back = commit({'.github/workflows/pins.yml': files['.github/workflows/pins.yml']}, 'axpin root back')
        assert run(back, reads(row()))[1][A]['class'] == 'keep'
    finally: REVIEWED_AXIOM_PIN_WALKERS, REVIEWED_AXIOM_PIN_READS = saved


FORM_CONTROLS.append(axiom_pin_walker_controls)
