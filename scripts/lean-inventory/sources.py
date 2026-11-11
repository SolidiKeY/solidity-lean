"""Source facts read from Git objects at one revision (never the working tree).

`clean` and `closure` are adapted from
`docs/audits/direction-tools/reachability/reach.py` (clean :46-71, closure :74-80),
which stays unchanged and whose historical `BASE` and `build()` are not used here.
Lexical scans in this module only propose candidates or bound extents; they never
establish a declaration use or its absence.
"""
import hashlib
import re
import subprocess

AREAS = ('Backend', 'Yul', 'Lowering', 'Frontend', 'SolcValidation', 'Source', 'Optimizer')
AREA_KEYS = {'Backend': 'backend', 'Yul': 'yul', 'Lowering': 'lowering', 'Frontend': 'frontend',
             'SolcValidation': 'solcValidation', 'Source': 'source', 'Optimizer': 'optimizer'}
# Library roots (lakefile.toml lean_lib / lean_exe roots). Test roots: libraries whose
# modules are checks rather than library code; their direct imports are test modules.
LIB_ROOTS = ('Solidity', 'SolidityExamples', 'SoliditySlowExamples', 'SolkeyTestSuite',
             'SolidityCorpus')
TEST_ROOTS = ('SolidityExamples', 'SoliditySlowExamples', 'SolkeyTestSuite', 'SolidityCorpus')
EXE_ROOTS = {'SolkeyCheck': 'solkeycheck', 'SolCases': 'solcases', 'SolidityLean': 'solidity-lean'}
GENERATED_ROOTS = ('Solidity.lean', 'SolidityExamples.lean', 'Bridge/SolidityBridge.lean')


def git(repo, *args, data=None):
    return subprocess.run(['git', '-C', str(repo), *args], input=data, check=True,
                          capture_output=True).stdout


def resolve(repo, rev):
    return git(repo, 'rev-parse', '--verify', rev + '^{commit}').decode().strip()


def tracked(repo, rev):
    """(path, blob id) for every tracked file at `rev`."""
    out = []
    for line in git(repo, 'ls-tree', '-r', '-z', rev).split(b'\0'):
        if not line:
            continue
        meta, path = line.split(b'\t', 1)
        _, kind, blob = meta.split()
        if kind == b'blob':
            out.append((path.decode(), blob.decode()))
    return sorted(out)


def blobs(repo, ids):
    """Contents of blob ids via one `git cat-file --batch`."""
    ids = list(dict.fromkeys(ids))
    raw = git(repo, 'cat-file', '--batch', data=''.join(i + '\n' for i in ids).encode())
    out, pos = {}, 0
    for i in ids:
        nl = raw.index(b'\n', pos)
        head = raw[pos:nl].split()
        if len(head) != 3 or head[1] != b'blob':
            raise ValueError('cannot read blob ' + i)
        size = int(head[2])
        out[i] = raw[nl + 1:nl + 1 + size].decode('utf-8', errors='replace')
        pos = nl + 1 + size + 1
    return out


def lean_tree_id(files):
    """Identity of the Lean sources: sha256 over sorted `path blob` lines of `*.lean`."""
    h = hashlib.sha256()
    for path, blob in files:
        if path.endswith('.lean'):
            h.update(f'{path} {blob}\n'.encode())
    return h.hexdigest()


def module_name(path):
    """Module name of a tracked `.lean` path (Bridge and vendored roots as in reach.py)."""
    rel = path
    for prefix in ('Bridge/vendor/', 'vendor/LeanTeX/', 'Bridge/'):
        if rel.startswith(prefix):
            rel = rel[len(prefix):]
            break
    return rel[:-len('.lean')].replace('/', '.')


def area_of(path):
    parts = path.split('/')
    if len(parts) > 2 and parts[0] == 'Solidity' and parts[1] in AREAS and path.endswith('.lean'):
        return parts[1]
    return None


def line_count(text):
    """Physical lines: newline-terminated lines plus a final unterminated one."""
    return text.count('\n') + (1 if text and not text.endswith('\n') else 0)


def clean(text):
    """Blank nested comments and strings, preserving offsets and newlines (from reach.py)."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, c = text[i:i + 2], text[i]
        if depth:
            if pair == '/-':
                out.extend('  '); depth += 1; i += 2; continue
            if pair == '-/':
                out.extend('  '); depth -= 1; i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            if c == '\\' and i + 1 < len(text):
                out.extend('  '); i += 2; continue
            if c == '"':
                string = False
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-':
            depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end; continue
        if c == '"':
            string = True; out.append(' ')
        else:
            out.append(c)
        i += 1
    return ''.join(out)


def closure(graph, roots):
    """Nodes reachable from `roots` (from reach.py)."""
    seen, stack = set(), list(roots)
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack.extend(graph.get(n, ()))
    return seen


HEADER_SKIP = re.compile(r'^(prelude|module)\b')
IMPORT_LINE = re.compile(r'^(?:(?:public|meta|private)\s+)*import\s+(.*)$')


def header_imports(text):
    """Imports of the module header: exact, since imports may appear only there."""
    out = []
    for line in clean(text).splitlines():
        s = line.strip()
        if not s or HEADER_SKIP.match(s):
            continue
        m = IMPORT_LINE.match(s)
        if not m:
            break
        out.extend(x for x in m.group(1).split() if x != 'all')
    return out


# Family grouping: X / XControls / XPins in one directory form one family; every other
# in-scope module joins its directory's family. A file named `Controls.lean` or
# `Pins.lean` is the Controls/Pins of its directory family.
def family_of(path, siblings):
    d, base = path.rsplit('/', 1)
    stem = base[:-len('.lean')]
    for suffix, role in (('Controls', 'controls'), ('Pins', 'pins')):
        if stem == suffix:
            return 'dir:' + d + '/', role
        if stem.endswith(suffix):
            return 'triple:' + d + '/' + stem[:-len(suffix)], role
    if (d + '/' + stem + 'Controls.lean') in siblings or (d + '/' + stem + 'Pins.lean') in siblings:
        return 'triple:' + d + '/' + stem, 'member'
    return 'dir:' + d + '/', 'member'


GROUPING_RULE = ("A module D/XControls.lean or D/XPins.lean, and D/X.lean when either exists, "
                 "form the family triple:D/X with roles controls, pins and member; D/Controls.lean "
                 "and D/Pins.lean are the controls/pins of the directory family dir:D/; every other "
                 "in-scope module belongs to dir:D/ of its own directory (not recursive).")

# Lexical command classification for uses outside every named declaration's range.
CONSUMER_COMMANDS = re.compile(r'^(#[A-Za-z_]\w*|example|run_cmd|run_elab|run_meta|run_tac)\b')
NONCONSUMER_COMMANDS = re.compile(
    r'^(@\[|attribute\b|open\b|export\b|set_option\b|namespace\b|section\b|end\b|variable\b|'
    r'universe\b|import\b|notation\b|infixl?\b|infixr\b|prefix\b|postfix\b|macro\b|macro_rules\b|'
    r'syntax\b|elab\b|elab_rules\b|declare_syntax_cat\b|deriving\b|initialize\b|builtin_initialize\b|'
    r'mutual\b|noncomputable\b|private\b|protected\b|local\b|scoped\b|theorem\b|lemma\b|def\b|'
    r'abbrev\b|instance\b|structure\b|inductive\b|class\b|axiom\b|opaque\b|partial\b|unsafe\b|'
    r'nonrec\b|omit\b|include\b|add_decl_doc\b|register_simp_attr\b|unseal\b|seal\b|'
    r'register_option\b|termination_by\b|decreasing_by\b|where\b)')
CONTINUATION = re.compile(r'^[|)\]},·.:=<>+*\-/\\]')


def command_starts(text):
    """1-based line -> first token of the command starting there (lexical)."""
    starts = {}
    for n, line in enumerate(clean(text).splitlines(), 1):
        if not line or line[0].isspace() or CONTINUATION.match(line):
            continue
        starts[n] = line.strip()
    return starts


def classify_command(head):
    if CONSUMER_COMMANDS.match(head):
        return 'consumer'
    if NONCONSUMER_COMMANDS.match(head):
        return 'declaration-or-scope'
    return 'unclassified'


ATTR_BLOCK = re.compile(r'@\[([^\]]*)\]')
ATTR_COMMAND = re.compile(r'^\s*(?:local\s+|scoped\s+)?attribute\s*\[([^\]]*)\]\s*([^\n]*)', re.M)
# Attributes that change compilation or unfolding only; the elaborator never inserts a
# use of a declaration because it carries one of these.
INERT_ATTRS = {'inline', 'noinline', 'specialize', 'reducible', 'irreducible', 'semireducible',
               'always_inline', 'macro_inline', 'deprecated', 'implemented_by', 'extern', 'export',
               'nospecialize', 'match_pattern', 'computed_field', 'expose', 'local', 'scoped',
               'inherit_doc', 'nolint', 'never_extract', 'reducible_instance', 'grind_norm_off'}


def attr_names(block):
    out = []
    for item in block.split(','):
        words = [w for w in item.replace('-', ' - ').split() if w not in ('local', 'scoped')]
        if words:
            out.append(words[0])
    return out


def attributed_heads(text):
    """Lines (1-based) carrying an `@[...]` with an attribute that is not inert."""
    lines = set()
    cleaned = clean(text)
    for m in ATTR_BLOCK.finditer(cleaned):
        if any(a not in INERT_ATTRS for a in attr_names(m.group(1))):
            lines.add(cleaned.count('\n', 0, m.start()) + 1)
    return lines


def attribute_commands(text):
    """Identifiers named by `attribute [...] ids` commands with a non-inert attribute."""
    out = set()
    for m in ATTR_COMMAND.finditer(clean(text)):
        if any(a not in INERT_ATTRS for a in attr_names(m.group(1))):
            out.update(t for t in re.findall(r"[^\W\d][\w'.!?]*", m.group(2)))
    return out


LEAN_INVOCATION = re.compile(r"lake (env|lean|exe|build)|['\"]lean['\"]|lean --run|leanc\b")
TEMPLATE_IMPORT = re.compile(r'import\s+((?:[A-Za-z_«][\w.«»\-]*)(?:\$\{|\{|%s|\'\s*\+|"\s*\+)?)')


def template_imports(text):
    """Module names (or dynamic prefixes ending in '*') after `import` in a runner's text."""
    out = set()
    for m in TEMPLATE_IMPORT.finditer(text):
        name = m.group(1)
        dynamic = name.endswith(('${', '{', '%s', '+'))
        base = re.sub(r"(\$\{|\{|%s|'\s*\+|\"\s*\+)$", '', name).rstrip('.')
        if not base:
            continue
        out.add(base + ('*' if dynamic or m.group(1).endswith('.') else ''))
    return out
