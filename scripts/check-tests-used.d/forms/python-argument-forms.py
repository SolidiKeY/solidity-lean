# H1090 (coord#1360/gh#1362, X1E-PY-ARG-INTERFACE): opt-in exact-blob python_argument_interface forms for two
# audited sources. Each recogniser runs only for its blob (PYTHON_ARGUMENT_FORMS key, rechecked on the text), rewrites
# the one unaudited construct in place (same line numbers) and hands the result to the unchanged
# python_argument_interface, so every other argv, sys and argparse refusal still applies. Any other blob keeps the
# audited interface, which refuses both shapes. Source role only: no read, argument, helper or output credit.
# The two (path, blob, commit) rows are already H996 rows of REVIEW_TABLE_PARTS['python-args'] (x1n); a second
# part repeating them is a ValueError in review_union, so this form adds none and its control pins them there.
import ast, hashlib, subprocess
from pathlib import Path

PY_ARG_TUPLE_LOOP_BLOB = '0224c0f28316d02a1489016c0e13c0fa20e6e80c'  # environment/test-known-stack-continuation.py
PY_ARG_DUNDER_SYS_BLOB = 'c9695f1c0bf66b40be1f138f3da7e1ebc147ffde'  # prepare-image-cache.py


def py_arg_git_blob(text):
    data = text.encode('utf-8', 'surrogateescape')
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def py_arg_splice(text, edits):
    """text with each single-line (line, start byte, end byte, replacement) spliced in; None if unsafe."""
    if '\r' in text: return None
    lines = text.encode('utf-8', 'surrogateescape').split(b'\n')
    for line, start, end, new in sorted(edits, reverse=True):
        if not 1 <= line <= len(lines) or not 0 <= start < end <= len(lines[line - 1]): return None
        lines[line - 1] = lines[line - 1][:start] + new.encode() + lines[line - 1][end:]
    return b'\n'.join(lines).decode('utf-8', 'surrogateescape')


def py_arg_parse(text):
    try: return ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None


def python_argument_tuple_loop(text):
    """Positional names added by one `for N in (<literal str>, ...): P.add_argument(N, ...)` loop.

    Exactly one add_argument/add_parser call has a non-literal first argument; it is the whole body of a plain for
    loop (no else) over a non-empty tuple of distinct literal names none starting with '-', its first argument is the
    loop name, it has no other positional argument and the loop holds no walrus. The name is read as the first
    literal and the audited interface gets every literal as a positional at the call's line; anything else refused
    there stays refused.
    """
    tree = py_arg_parse(text)
    if tree is None: return None
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
             and n.func.attr in ('add_argument', 'add_parser')
             and not (n.args and isinstance(n.args[0], ast.Constant) and isinstance(n.args[0].value, str))]
    if len(calls) != 1 or calls[0].func.attr != 'add_argument' or len(calls[0].args) != 1: return None
    call = calls[0]; name = call.args[0]
    loops = [n for n in ast.walk(tree) if isinstance(n, ast.For) and len(n.body) == 1
             and isinstance(n.body[0], ast.Expr) and n.body[0].value is call]
    if len(loops) != 1 or loops[0].orelse or any(isinstance(n, ast.NamedExpr) for n in ast.walk(loops[0])): return None
    loop = loops[0]
    if not (isinstance(name, ast.Name) and isinstance(loop.target, ast.Name) and loop.target.id == name.id
            and isinstance(loop.iter, ast.Tuple) and loop.iter.elts and name.lineno == name.end_lineno): return None
    if not all(isinstance(e, ast.Constant) and type(e.value) is str for e in loop.iter.elts): return None
    names = [e.value for e in loop.iter.elts]
    if len(set(names)) != len(names) or any(not n or n.startswith('-') for n in names): return None
    edited = py_arg_splice(text, [(name.lineno, name.col_offset, name.end_col_offset, repr(names[0]))])
    interface = None if edited is None else python_argument_interface(edited)
    if interface is None: return None
    positionals = {tuple(x) for x in interface['positionals']} | {(name.lineno, n) for n in names}
    return dict(interface, positionals=[list(x) for x in sorted(positionals)])


def python_argument_dunder_sys(text):
    """argv reads through `__import__("sys").argv`, as if through `import sys`.

    Every `__import__` in the program is the builtin called as exactly `__import__("sys")` (no other argument) whose
    value only has its `argv` read; nothing binds, deletes or names `__import__` otherwise (no attribute of that
    name either). Each call is read as `sys` and `import sys` is appended; the audited interface then refuses any
    write or method call on argv, any other binding of sys and the rest as for `import sys`.
    """
    tree = py_arg_parse(text)
    if tree is None: return None
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    calls, edits = [], []
    for n in ast.walk(tree):
        if isinstance(n, ast.Global) or isinstance(n, ast.Nonlocal):
            if '__import__' in n.names: return None
        elif isinstance(n, ast.Attribute) and n.attr == '__import__': return None
        elif isinstance(n, ast.Name) and n.id == '__import__':
            call = parents.get(n)
            if not (isinstance(n.ctx, ast.Load) and isinstance(call, ast.Call) and call.func is n): return None
            calls.append(call)
        elif any(getattr(n, field, None) == '__import__' for field in ('name', 'asname', 'arg')): return None
    for call in calls:
        parent = parents.get(call)
        if (call.keywords or len(call.args) != 1 or not isinstance(call.args[0], ast.Constant) or call.args[0].value != 'sys'
                or not isinstance(parent, ast.Attribute) or parent.value is not call or parent.attr != 'argv'
                or call.lineno != call.end_lineno): return None
        edits.append((call.lineno, call.col_offset, call.end_col_offset, 'sys'))
    if not edits: return None
    edited = py_arg_splice(text, edits)
    if edited is None: return None
    return python_argument_interface(edited + ('' if edited.endswith('\n') else '\n') + 'import sys\n')


def py_arg_exact_blob(blob, recogniser):
    return lambda text: recogniser(text) if py_arg_git_blob(text) == blob else None


PYTHON_ARGUMENT_FORMS[PY_ARG_TUPLE_LOOP_BLOB] = py_arg_exact_blob(PY_ARG_TUPLE_LOOP_BLOB, python_argument_tuple_loop)
PYTHON_ARGUMENT_FORMS[PY_ARG_DUNDER_SYS_BLOB] = py_arg_exact_blob(PY_ARG_DUNDER_SYS_BLOB, python_argument_dunder_sys)


def python_argument_form_controls(env):
    """H1090: both audited blobs get their interface only through their form; any other blob, and every variant
    shape, stays refused."""
    nb = 'tests/directruntime-20261104/native-browser/'; commit = 'ca73d1a4e1aecbcbc566acaa1aa7392cad472b3d'
    rows = {(nb + 'environment/test-known-stack-continuation.py', PY_ARG_TUPLE_LOOP_BLOB, commit),
            (nb + 'prepare-image-cache.py', PY_ARG_DUNDER_SYS_BLOB, commit)}
    h996 = [part for part in REVIEW_TABLE_PARTS['python-args'] if part[0] == 'H996']
    assert len(h996) == 1 and rows <= h996[0][1] and rows <= REVIEWED_PYTHON_ARGS
    root = Path(__file__).resolve().parents[2]
    texts = {blob: subprocess.run(['git', '-C', str(root), 'cat-file', 'blob', blob], check=True,
                                  capture_output=True).stdout.decode('utf-8', 'surrogateescape')
             for blob in (PY_ARG_TUPLE_LOOP_BLOB, PY_ARG_DUNDER_SYS_BLOB)}
    expected = {PY_ARG_TUPLE_LOOP_BLOB: {'argv_lines': [], 'argv_tail_lines': [], 'subcommands': [],
                                         'positionals': [[18, 'build'], [18, 'gate'], [18, 'report']]},
                PY_ARG_DUNDER_SYS_BLOB: {'argv_lines': [7], 'argv_tail_lines': [], 'positionals': [], 'subcommands': []}}
    other = 'f' * 40
    for blob, text in texts.items():
        assert py_arg_git_blob(text) == blob and python_argument_interface(text) is None, blob  # audited form unchanged
        assert python_argument_form(blob, text) == expected[blob], blob
        assert python_argument_form(other, text) is None, blob  # control: any other blob keeps refusing the shape
        assert PYTHON_ARGUMENT_FORMS[blob](text + '\n') is None  # one more byte is another blob
    assert PYTHON_ARGUMENT_FORMS[PY_ARG_TUPLE_LOOP_BLOB](texts[PY_ARG_DUNDER_SYS_BLOB]) is None
    loop = ('import argparse\np = argparse.ArgumentParser()\nfor name in ("a", "b"):\n    p.add_argument(name)\n'
            'p.parse_args()\n')
    assert python_argument_tuple_loop(loop) == {'argv_lines': [], 'argv_tail_lines': [], 'subcommands': [],
                                                'positionals': [[4, 'a'], [4, 'b']]}
    for variant in (loop.replace('("a", "b")', '["a", "b"]'), loop.replace('("a", "b")', '("a", B)'),
                    loop.replace('("a", "b")', '("a", "a")'), loop.replace('("a", "b")', '("-a", "b")'),
                    loop.replace('("a", "b")', '()'), loop.replace('add_argument(name)', 'add_argument(other)'),
                    loop.replace('add_argument(name)', 'add_argument(name, name)'),
                    loop.replace('add_argument(name)', 'add_parser(name)'),
                    loop.replace('    p.add_argument(name)\n', '    p.add_argument(name)\n    print(name)\n'),
                    loop.replace('p.parse_args()\n', 'else: pass\np.parse_args()\n'),
                    loop.replace('p.parse_args()', 'p.parse_args(["x"])'), loop + 'p.add_argument(NAME)\n',
                    loop.replace('add_argument(name)', 'add_argument(name, default=(name := "x"))'),
                    loop.replace('\n', '\r\n')):
        assert python_argument_tuple_loop(variant) is None, variant
    dunder = 'out = __import__("sys").argv[1]\nrest = __import__("sys").argv[2:]\n'
    assert python_argument_dunder_sys(dunder) == {'argv_lines': [1, 2], 'argv_tail_lines': [2], 'positionals': [], 'subcommands': []}
    for variant in ('print(1)\n', 'x = __import__("sys")\n', '__import__("os").argv[1]\n', '__import__("sys", {}).argv[1]\n',
                    '__import__("sys").path[0]\n', '__import__("sys").argv.append("x")\n', '__import__("sys").argv[1] = "x"\n',
                    '__import__ = print\n__import__("sys").argv[1]\n', 'import builtins\nbuiltins.__import__("sys").argv[1]\n',
                    'def f(__import__): pass\n__import__("sys").argv[1]\n', 'sys = 1\n__import__("sys").argv[1]\n',
                    'from os import path as __import__\n__import__("sys").argv[1]\n', 'f(__import__)\n__import__("sys").argv[1]\n',
                    '__import__(\n"sys").argv[1]\n'):
        assert python_argument_dunder_sys(variant) is None, variant


FORM_CONTROLS.append(python_argument_form_controls)
