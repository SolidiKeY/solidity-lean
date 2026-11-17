"""Reviewed source roles: H999 Lean check sources, H1015 Lean fixture sources,
the H1025 and H1004 widenings of the H997 non-Python entry review set, H1051
Python helper sources imported by kept entry roots and H1050 documentation
references read by the documentation navigation check.

Executed by fragments.py in its own namespace (helpers, review tables and the
self-test rebinding of REVIEWED_* names are shared). Classifier path: excluded
from candidate discovery like the rest of scripts/check-tests-used*."""


# H1025 (gh#1384, QX1E-ROLESET, Option A): x1e-classify-rest's 62 shell/Node
# programs that match the H997 interface, reviewed case by case under the
# unchanged H997 rules (nonpython_entry_root); same (path, blob, introducing
# commit) form. 61 pass. Refused, left unresolved: tests/fullscope-20261104/
# vo1/mcp-check.sh (removed from the tree, so no current blob to bind). For
# sol-expression-uniqueness/compiler-controls.mjs the blob was introduced twice
# (1058aa95df, then the squash 9e74823267): the earlier one is recorded and
# the other is refused as unreviewed. Membership is the only change: no
# execution, pass, read, helper, child, output, proof or runtime credit.
REVIEWED_NONPY_ENTRIES_H1025 = _review_table('''
@06f1aece06fb62e9654698a51e301c493610aa1f
T:yul-views/aggregate-dynamic-run.mjs ee89db0d218a203fa97a824d7177ce52e5d770e3
@0916c0099177fb89cfcac87f2c8e497a29f2180a
T:yul-views/abi-input-run.mjs 4b22c8071c7302a5446457b2fd815830d75d69f6
@0bdc978f23f06c70ea776ba2304245fcfe877bdc
T:yul-views/residual-memory-run.mjs 54010edc6ca89b449edb6b2f0aa68c20e2fa2b1a
@1058aa95dfe0fccdbcd468fe8b52555168a730e9
T:sol-expression-uniqueness/compiler-controls.mjs 195438b74253dc632524ed0cc0a1348d54a30968
T:sol-expression-uniqueness/runtime-mcp.sh 33e47c42458f23c12080c4d66ef8f2a935686a70
@1b133944b611b777a83f84beb06e1b22d81f613f
T:yul-views/signed-dynamic-run.mjs c003d203b16027472e71c55ce70d5f454c2a8de3
@1b695516b853974ceb57be3a2ae82682c405fde5
T:primitive-packets-1104/UnsignedMul/run.sh b4f27c0a8fd5d3cf2cf60a3e88f8de12eb17b54e
@1e37a2256e277ef24b04284ad0de9f822feaca8c
T:contract-world-certificates/replay-pipelines.mjs ebd450f4236a09675a247e2a0bae8d5b9581a718
@1ef94159af54611d70b10e213d59ca31309b8428
T:yul-views/owned-bool-dynamic-run.mjs 4afb8df7af20428f4c456061ff945148e2dd168e
@278633cfeedcf831b3131c370b5c810b55ef8939
T:yul-views/nested-mapping-run.mjs 2674898570297688e634bb2fde1fecc908aeffda
@2ad8438ad86d88e29a46188dfd45aa909bbaa165
T:yul-views/recursive-dynamic-run.mjs 0c216831b6d78e10d7de01167af753213376787c
@2bb7bb20852e986f81a44aaaadfda104cac9c3f4
T:yul-views/owned-bool-run.mjs 4cadb8c2f86c8dd9bbe8c3948f799440cc8e9f11
@3dad6f089d7c218d9ff9b1418aeb57689d0afa14
T:source-immutables/check-source.mjs 659d6cd4bf7d11f2ed36f0f44df5a0cf5f2a5b27
T:source-immutables/probe.mjs 726646550589a4e82acc58c827833e058c85577e
@3f920bba44c7c441ea4c329ca2c740b222537193
T:yul-views/residual-mcopy-run.mjs b1d0527430d3c9887d18a0fa91327c5693a061cc
@40337e715392c517a73f3bc1eefd85a036c2feb3
T:yul-views/dynamic-storage-run.mjs ab8ff5d41b90db3cd6a9992d67c5c1a96ba25cbd
@4131f468b7417ddf46c32d188d10ac6d85e03ef8
T:fullscope-20261104/vt1/check-data.sh 3202285954d3b54c59db4db8f814d0d30234ed44
T:fullscope-20261104/vt1/check-import.sh f19154f4bbaf658425c551490e9061f70e44ca63
@43b668aa45967d09c385133ff3afbdf3c834c4b0
T:sol-override-validation/compiler.mjs f4c64c57950ef2b52b2663c2ebeafcd6c75317df
T:sol-override-validation/getter-pipelines/check.mjs 27000ad76c48c9c0c278edb5119fa40ca138380c
@4704d9e7cfb8484e9eef4011cea5e01846b862fb
T:yul-views/physical-reference.mjs 37d2270025ea6fd3c5819cc708b6a0608d5ffeb7
@4d45820cc26824ca2ba1da8177be755655f820f5
T:calldata-packets-1105/RawBool/run.sh 55360017e55cefeb16029be0097366c7a4169d5d
T:calldata-packets-1105/RawBool/server.sh 7ab03f3d14d5b9bfbd601f0bcce7b03567d4d1b5
@52ed583076b758e5c0640f10732d1cf5e8e8de1e
T:fullscope-20261104/vt1/check-ir.sh e77e7c4f73af6e78a198368013743915e8b40afb
@57afdc4c9647c92cebed547c05b80d69beddf125
T:yul-views/scalar-dynamic-run.mjs 1b1f8a73ba3d0773c80db3643c99acfa3d1b3d3a
@5817182ebbb3a42057211abb0689b3e762e821f6
T:yul-views/root-sequence-run.mjs 016e337b66c0e916e460681d45c9474319061753
@5f7fcdb942232c3805a15a404a6faf836a170bc1
T:yul-views/mapping-transient-run.mjs 73d6aee6681fb36cf23b48239b0a7117a1fee24d
@65359b4b0e79c0441c231eb9c84cb2cc33419f9f
T:fullscope-20261104/vt1/check-dialect.sh 6dd326a113bc7b1350e78166942e742eafe7c30d
T:fullscope-20261104/vt1/generate-fixtures.mjs f7e1127f75b828e7d23018e1a2599e046152becd
@6d1cd27d58bb6d6c75511adf37fafb86c96a4b0c
T:calldata-packets-1105/RawBool/PinFollowup/audit-pins.mjs ce8ab0ba15cb60740529e6b12281a20ba9273314
T:calldata-packets-1105/RawBool/PinFollowup/run.sh 0e803749a863a0797ddacf341dd31ef7a548e755
T:calldata-packets-1105/RawBool/PinFollowup/server.sh 919f053f7babb9bd9c09ac49a523af89776e4a47
@6ea22a6e18d6bba57577a1e9e6c41d355538104b
T:sol-expression-uniqueness/gate.sh 3c98a65a02f53475179bf79bea443c7553e1397e
@759d34118b492d798447727e1af9631b68791ed7
T:yul-views/frame-calldata-run.mjs 69cb25895b3cdf4da7d66f743aafeb4a41204f05
@7787384b6f4be4a2402327de2b344baa4851a3f6
T:yul-views/object-allocation-run.mjs 52ebd53ad9fd8b7b2a92d352134c669c25464f7a
@781938cf63a9308e0e244d0d1dbd0b586dd3dafa
T:v14-help/calldata-aggregates-probe.mjs 1ef1b4511f45a89a7f268f65d18b444b4a565ca4
@7b0fc88517223bae9e98ddee11941af50834f691
T:primitive-packets-1105/CheckedSub/run.sh 8e529c0bcc5ba9c28793683ad758b0ce0f7501c3
@88bf2c0e533e87e020ae3535b6fcd67a185dbd75
T:sol-qualified-units/h27-location-probe.mjs 7188abddec388e859f494418b2b9be71916c9e12
T:sol-qualified-units/resolution-barrier-probe.mjs fefa276437365430438c29d5b7a7881d392355a6
T:sol-qualified-units/solc-fixtures.mjs 3a4813473c605d262ebca054f874d8cde845106f
@8cca58a669de87d58a05d5931c0b2144ff295df8
T:storage-values/final-gates.sh 771946e2497017da7135f16614ba595889f086b9
@93e97b28e61f1466eafeb6163baed9da1f9e8240
T:backend-environment/vectors.mjs fe53605c002ad8edc73f883377ce04d6f777a3ee
@94fc5bb6cf7c1f0c7c5d2d034df4d8c8a201f6ae
T:sol-numeric-literals/run-fixtures.mjs b71ff94f50a6d3a23aba41434a2df2470b440e06
@9b0b5b4cfa1b2bbe0e79b175ebe6c3b57cebabe2
T:yul-views/nested-dynamic-run.mjs 57c3988954535d54768901541d28a093aab35364
@a10e1609a00015e77bdda47e1be53be1f8c4ec21
T:yul-views/retained-allocation-run.mjs 0591d8961cd80012bb7499ce6c2edca2a9bdd35a
@b9dc71b38fa597d7b38a0ee4f2f32ce4c6dcf9ea
T:yul-views/recursive-declaration-run.mjs c04e5d19fe5643fd08f35ad1dfc99332b1b59bed
@bd475d424c4326521a40a6cb5a2d7d4a12b0563d
T:sol-c3-exactness/check-fixtures.mjs ff083fc2f349a9613dfab35036e32309c5d76d58
@bedad5225f2481e5821e7b1b30a487ed7d1bf2ae
T:yul-views/primitive-dynamic-run.mjs 505ec55065a3a7aa254196a35c5a88d0c9139440
@c1ff5dcb0913b287d03e62ec8ba64d9328124659
T:yul-views/tuple-storage-run.mjs 1f534002f391064b7807a5449b70bc6b99e0e967
@c360d104012547a94a6c55fa3575a9b3bef54d2f
T:storage-values/check-local-layers.mjs adaa5296d1a08994996902a8e52e362ae16d6302
@c4284f7201cc0b69fbb5c399985c86c34237c315
T:yul-views/packed-dynamic-run.mjs eef4c99a065e5e9573bb02df31dd87b854597ee7
@c5e92c6623c6308ea1936cb3f294d9a34a3ba7c5
T:fullscope-20261104/vt1/check-resolution.sh 4c40b106a1610dc9c7e330c37f5cb4525bf9a83f
T:fullscope-20261104/vt1/generate-object-data.mjs 61133720c0666849e45a4452f17431f9ad6b37e1
@d0dc0b421c46e103b32b851e42be8d451ff285ad
T:yul-views/declaration-packing-run.mjs 4f447384e2999763af5e94db74beefe737c19d84
@e26852e8d26663d1faeda40f39898dd1534c1596
T:fullscope-20261104/vt1/ImportFollowup/run.sh ef289e5e21f3f2c8495987ed4f9a951fd2d5261b
T:fullscope-20261104/vt1/ImportFollowup/server.sh 9326c2dfa644fd96c37d25c8f205d8f850c523fc
@eeaf2c03028196200fcfa464cb081579e1542e47
T:yul-views/retained-storage-run.mjs 52f24436bf6e614dfc30293a65b6b4381954c420
@f44d7c523159b07e0b0b4975ec9c035de94737cc
T:yul-views/origin-constants.mjs c26640b7807d3595183aa2dfabc3b3ac7c5573fd
T:yul-views/origin-sequence-run.mjs e64c39bda9f1a74f4792de38103e4159ba8996fe
@fb2382d2759199e774b5a175d7a804d3d45d5a86
T:yul-views/inherited-sequence-run.mjs adeb09dc75c286b40aff496db08e67b20f597ceb
@fd67008ed20590639e04345fbb12a9dfa645a95f
T:backend-environment/ownership.mjs c7e75bcd68c0b2347212973ffdfeba0c285362f9
''')
REVIEWED_NONPY_ENTRIES = REVIEWED_NONPY_ENTRIES | REVIEWED_NONPY_ENTRIES_H1025
# H1004 (gh#1340, X1E-SOURCE-PROGRAM-ROLES, Option B), form (1): the two Node
# CLI programs of x1e-classify-h28-h55 that match the H997 interface, reviewed
# under the unchanged H997 rules; same (path, blob, introducing commit) form.
# Membership only: no execution, pass, read, helper, output or runtime credit.
REVIEWED_NONPY_ENTRIES_H1004 = _review_table('''
@05b3f3f3a0bbb708eb00e86025811aee3eee15b3
T:h28-sol/type-grammar/run_solc.mjs cb05eeac7078737564180bdc3d7f030520c35065
@3b327d00fd2262cfb27ccecdc911e9c5d2e7d4f1
T:h28-sol/literal-grammar/solc-fixtures.mjs 56774afb5f8d6355c2e8fca81557371364b2b08d
''')
REVIEWED_NONPY_ENTRIES = REVIEWED_NONPY_ENTRIES | REVIEWED_NONPY_ENTRIES_H1004

LEAN_CHECK_KIND = 'lean-check-source-role'
LEAN_CHECK_PREFIX = 'lean-check:'
# H999 (gh#1334, X1E-LEAN-CHECK-ROLE): the driver line and the gate.sh
# per-file branch that forms the one command.
LEAN_CHECK_GATE = 'scripts/coord-tools/gate.sh'
LEAN_CHECK_DRIVER_LINE = 'bash scripts/coord-tools/gate.sh per-file "${files[@]}"'
LEAN_CHECK_GATE_BRANCH = 'if [ "$mode" = per-file ]; then'
LEAN_CHECK_GATE_LINE = '  for file in "${files[@]}"; do run_gate "lean:$file" lake lean "$file" -- --tstack=131072; done'
lean_check_command = lambda path: ['lake', 'lean', path, '--', '--tstack=131072']
# Reviewed sources (path, blob, introducing commit) and invocations (path,
# blob, driver, driver blob, gate line); each driver is a reviewed H997 entry.
# read-bounds-validate.sh is not reviewed: a top-level exec hands its gate line
# to validation-admission.py's recipe runner, which this audit does not follow.
REVIEWED_LEAN_CHECKS = frozenset({
    ('tests/directruntime-20261104/control-tuples/ProofAudit.lean', 'c60ce39b40db0e4a797d0afa4c1a8f14c40df466', 'e6849d3bdf516099d20c33d3581d523449764018'),
})
REVIEWED_LEAN_CHECK_INVOCATIONS = frozenset(
    ('tests/directruntime-20261104/control-tuples/ProofAudit.lean', 'c60ce39b40db0e4a797d0afa4c1a8f14c40df466', 'tests/directruntime-20261104/shared-translator/' + d, b, n)
    for d, b, n in (('address-validate.sh', '6f9014aa569e25b415aba09f7ef1c37f4a4dd3ea', 20),
                    ('environment-validate.sh', '9460e5febcad1c954204902e5b7a505c5a5f79da', 21),
                    ('fixed-byte-validate.sh', 'b4d495f62a04cab7ec344489563d20f63f832f33', 17),
                    ('h90-validate.sh', 'a67ec66c28490d60be84f27466897389d27dc82c', 17),
                    ('primitive-return-validate.sh', '074e6d15f01d4bfd67c2bd0af103663f96231923', 17)))
_LEAN_NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"


def lean_check_interface(lean_code, path, text):
    """Header imports and the lines of `#check [@]NAME` and `#print axioms NAME`,
    or None. Every other line is blank or comment only: any other command or
    declaration (#eval, run_cmd, set_option, open, def, ...), a term that is
    not one identifier, an indented or continued line, a late import, a
    double quote, ambiguous line breaks, NUL or no check command gives None."""
    if not path.endswith('.lean') or not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code = lean_code(text)
    if code.count('\n') != text.count('\n'): return None
    imports, checks, axioms = [], [], []
    for n, (line, raw) in enumerate(zip(code.split('\n'), text.split('\n')), 1):
        line = line.rstrip()
        if '"' in raw: return None
        if not line: continue
        match = re.fullmatch(r'import((?:[ \t]+' + _LEAN_NAME + r')+)', line)
        if not raw.startswith(line) or match and (checks or axioms): return None
        if match: imports.extend(match[1].split())
        elif re.fullmatch(r'#check[ \t]+@?' + _LEAN_NAME, line): checks.append(n)
        elif re.fullmatch(r'#print[ \t]+axioms[ \t]+' + _LEAN_NAME, line): axioms.append(n)
        else: return None
    return {'imports': imports, 'check_lines': checks, 'axiom_lines': axioms} if checks or axioms else None


def lean_check_invocation(text, path, line):
    """The driver reaches its column-0 LEAN_CHECK_DRIVER_LINE with path listed.

    Before it: balanced quotes per line; no continuation, here-document, exec,
    cd, PATH change, function, other builtin listed below, or compound command
    but column-0 `for ...; do`/`done`; `files` only as a whole-line files=(...)
    or files+=(...) without ; # ( ), reset only at column 0, path an unquoted
    word of a later column-0 assignment. Lexical; the review set gates."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(line) is not int or not 1 <= line <= len(lines) or lines[line - 1] != LEAN_CHECK_DRIVER_LINE: return False
    depth = 0; named = None
    for n, raw in enumerate(lines[:line - 1], 1):
        if n == 1 and raw.startswith('#!') or not raw.strip() or raw.strip().startswith('#'): continue
        try: shlex.split(raw, comments=True)
        except ValueError: return False
        if '<<' in raw or '`' in raw or raw.rstrip().endswith('\\') or '$(' in raw and re.search(r'(?<![\w$-])files\b', raw): return False
        if re.search(r'(?<![\w$-])(?:exec|exit|return|source|eval|trap|alias|hash|kill|declare|typeset|local|readonly|unset|builtin|command|enable|cd|pushd|popd|function|if|then|else|elif|fi|while|until|case|esac|select|shift)(?![\w-])'
                     r'|^\s*\.\s|(?<![\w$])PATH\+?=|\w\s*\(\s*\)|[{}]|&&|\|\||;\s*$|(?:^|[;&|]\s*)\(', raw): return False
        if re.match(r'for\s', raw):
            if depth or not re.search(r';\s*do\s*$', raw): return False
            depth = 1; continue
        if re.fullmatch(r'done\s*', raw):
            if not depth: return False
            depth = 0; continue
        if re.search(r'(?<![\w$-])do(?![\w-])', raw): return False
        if not re.search(r'(?<![\w$/-])files(?![\w./-])', raw): continue
        match = re.fullmatch(r'(\s*)files(\+?)=\(([^;#()]*)\)\s*', raw)
        if match is None or not match[2] and match[1] or not match[1] and re.search('["\'$]', match[3]): return False
        try: words = shlex.split(match[3])
        except ValueError: return False
        if not match[2]: named = False
        if not match[1] and not depth and path in words: named = True
    return depth == 0 and named is True


LEAN_FIXTURE_KIND = 'lean-fixture-source-role'
LEAN_FIXTURE_PREFIX = 'lean-fixture:'
# H1015 (gh#1359, X1E-LEAN-FIXTURE-REMAINDER, Option A): Lean fixture sources
# (definitions, #eval, examples, run_elab or main) that a reviewed H997 driver
# hands to the same gate.sh per-file line, audited one by one. Sources
# (path, blob, introducing commit) and invocations (path, blob, driver, driver
# blob, driver line), as for H999. Consumption only: no elaboration, pass,
# read, import, proof or runtime credit.
REVIEWED_LEAN_FIXTURES = _review_table('''
@0834bc67b042a63a8c804162781802245ae59c98
D:shared-translator/AddressLocalControls.lean 1b967893ecac51c9e5dfb437dd3596febd1ad291
@2366c57f099b27d4673dda504d258ba77ff3fcaf
D:control-tuples/ProductionControls.lean ca25c4ca010fa72c0512c2b7523fabcccbbad7e7
@44d89439afd8fe7aca251cd5693b5b7ea36cf603
D:shared-translator/EnvironmentMemberControls.lean 5180d8e8c04ac5e1e86ed13c4fef65f801c5afa0
@4a66db87c8ed848aef4c2ac1732b1df326c6fa97
D:shared-translator/FixedByteLocalControls.lean 49901e395dd580a8682dfdaa1dc38c610b3fad54
@957e5defaa3c2e32df1e692d8781e0d89fed5199
D:control-tuples/ObligationControls.lean 4195775c23abafdc47ec3ebabe1a6e011e3777cb
D:shared-translator/PrimitiveReturnControls.lean 73cb82f3ed73ec1ba4e0e69fb591f347fd6c3d0d
@b44f0de87c2ab845b79c9d84004dcb7c91babded
D:shared-translator/H90Census.lean e41529cb06d93c593259cb2714d02c51fd96a022
''')
# The H999 driver lines (address 20, environment 21, others 17); each driver
# lists the source in a column-0 files+=(...) word before its gate line.
_LEAN_GATE_DRIVERS = {d: (b, n) for _, _, d, b, n in REVIEWED_LEAN_CHECK_INVOCATIONS}
REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset(
    (p, b, 'tests/directruntime-20261104/shared-translator/' + d + '-validate.sh') + _LEAN_GATE_DRIVERS['tests/directruntime-20261104/shared-translator/' + d + '-validate.sh']
    for p, b, _ in REVIEWED_LEAN_FIXTURES for d in {
        'ObligationControls': 'address environment fixed-byte h90 primitive-return', 'ProductionControls': 'address environment fixed-byte h90 primitive-return',
        'AddressLocalControls': 'address environment', 'EnvironmentMemberControls': 'environment', 'FixedByteLocalControls': 'address environment fixed-byte',
        'H90Census': 'address environment', 'PrimitiveReturnControls': 'address environment fixed-byte primitive-return'}[posixpath.basename(p)[:-5]].split())


# Column-0 commands that make a body a fixture (declaration, evaluation, elaboration).
FIXTURE_COMMAND = (r'(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)[ \t]+)*'
                   r'(?:def|theorem|lemma|abbrev|instance|structure|inductive|class|example|opaque|axiom|#eval|#guard|#reduce'
                   r'|run_elab|run_cmd|run_meta|elab|macro|syntax|macro_rules|elab_rules)(?![\w.\'])')


def lean_fixture_interface(lean_code, path, text):
    """Header imports and the first body line of a Lean fixture source, or None.

    Only column-0 `import NAMES` lines and blank or comment lines precede the
    body; the body follows at least one import and holds no later import,
    prelude or module line and no #exit anywhere. The body must hold a
    column-0 declaration or evaluation command (FIXTURE_COMMAND), so a source
    of only #check/#print/open/set_option lines is never a fixture, whether or
    not the H999 grammar accepts it. NUL or ambiguous line breaks give None."""
    if not path.endswith('.lean') or not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code = lean_code(text)
    if code.count('\n') != text.count('\n') or lean_check_interface(lean_code, path, text) is not None: return None
    if re.search(r'#exit(?![\w.\'])', code): return None
    imports, body, command = [], None, False
    for n, (line, raw) in enumerate(zip(code.split('\n'), text.split('\n')), 1):
        line = line.rstrip()
        if not line: continue
        header = re.match(r'\s*(?:(?:public|private|meta)\s+)*(?:import|prelude|module)(?![\w.\'])', line)
        match = re.fullmatch(r'import((?:[ \t]+' + _LEAN_NAME + r')+)', line)
        if body is None and match and raw.startswith(line) and 'all' not in match[1].split(): imports.extend(match[1].split()); continue
        if header: return None
        if body is None: body = n
        command = command or re.match(FIXTURE_COMMAND, line) is not None
    return {'imports': imports, 'body_line': body} if imports and body and command else None


LEAN_CHECK_FORM = {'role': 'Lean check role', 'shape': 'check-only', 'interface': lean_check_interface, 'prefix': LEAN_CHECK_PREFIX,
    'flag': 'lean_check_role', 'source': 'Lean check source',
    'reason': 'Reviewed Lean check source run by reviewed drivers via gate.sh per-file; never run or certified to elaborate or pass. No execution, read, fixture, helper, import-dependency, output, proof or runtime credit.'}
LEAN_FIXTURE_FORM = {'role': 'Lean fixture role', 'shape': 'fixture', 'interface': lean_fixture_interface, 'prefix': LEAN_FIXTURE_PREFIX,
    'flag': 'lean_fixture_role', 'source': 'Lean fixture source',
    'reason': 'Reviewed Lean fixture source (definitions, #eval, examples, run_elab or main) consumed by reviewed drivers via gate.sh per-file; never run or certified to elaborate or pass. Consumption role only: no execution, read, fixture-read, helper, import-dependency, output, proof or runtime credit.'}


def _lean_gate_root(classifier, graph, catalog, entry, reviewed, invocations, form):
    """H999/H1015: a reviewed live non-root Lean source run by gate.sh per-file.

    Binds lean_check_command(P), the blob, its interface (form['interface']),
    the reviewed introducing commit and each invocation: a reviewed H997
    driver (blob, commit) whose gate line runs P. P is under tests/; a Lake
    package, root library, importer or changed gate.sh per-file line makes it
    stale. Never a validated runner; anchors nothing. Kept later while source
    and drivers are unchanged; a current definition of the path supersedes it."""
    repo = graph.repo; role = form['role']
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'invocations', 'purpose'}
    _role_schema(classifier, catalog, entry, required, role); calls = entry['invocations']
    if (not isinstance(calls, list) or not calls or any(not isinstance(c, dict) or set(c) != {'driver', 'driver_blob', 'driver_commit', 'line'} or type(c['line']) is not int
                   or not all(isinstance(c[k], str) for k in ('driver', 'driver_blob', 'driver_commit')) for c in calls)
            or len({canonical(c) for c in calls}) != len(calls)):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if entry['command'] != lean_check_command(p) or not p.endswith('.lean') or not p.startswith('tests/') or _clean(p) != p:
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed ' + role + ': ' + p)
    if any((p, blob, c['driver'], c['driver_blob'], c['line']) not in invocations or not c['driver'].endswith('.sh')
           or (c['driver'], c['driver_blob'], c['driver_commit']) not in REVIEWED_NONPY_ENTRIES for c in calls):
        raise ValueError('unreviewed ' + role + ' invocation: ' + p)
    pins = [(p, blob)] + [(c['driver'], c['driver_blob']) for c in calls]
    if not _role_current(classifier, repo, catalog, entry, pins): return
    if repo.tree[p][0] != '100644' or p not in repo.texts or any(repo.tree[c['driver']][0] not in ('100644', '100755') for c in calls):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    if not all(_introduced(classifier, repo, c['driver_commit'], c['driver'], c['driver_blob']) for c in calls):
        raise ValueError(role + ' driver lacks its introducing provenance: ' + p)
    # Lake packages, root libraries and importers are not pinned: they make the role stale.
    parts = p.split('/')
    if (any('/'.join(parts[:k]) + '/' + name in repo.tree for k in range(1, len(parts)) for name in ('lakefile.toml', 'lakefile.lean'))
            or 'lakefile.lean' in repo.tree or not _outside_root_libraries(repo, p)
            or any(e['target'] == p and e['operation'] == 'Lean import' for edges in graph.edges.values() for e in edges)): return
    interface = form['interface'](classifier['lean_code'], p, repo.texts[p])
    if interface is None: raise ValueError(role + ' lacks an audited ' + form['shape'] + ' interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError(role + ' interface mismatch: ' + p)
    for c in calls:
        if c['driver'] not in repo.texts or nonpython_entry_interface(c['driver'], repo.texts[c['driver']]) is None:
            raise ValueError(role + ' driver lacks an audited entry interface: ' + c['driver'])
        if not lean_check_invocation(repo.texts[c['driver']], p, c['line']): raise ValueError(role + ' driver does not run the source: ' + c['driver'])
    if '\n' + LEAN_CHECK_GATE_BRANCH + '\n' + LEAN_CHECK_GATE_LINE + '\n' not in repo.texts.get(LEAN_CHECK_GATE, ''): return
    identity = form['prefix'] + p
    graph.root(p, 'source-only ' + form['source'], shlex.join(entry['command']), calls[0]['driver'], calls[0]['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, form['flag']: True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': interface, 'provenance': doc, 'invocations': calls, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'], 'reason': form['reason']}})


def lean_check_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H999: a reviewed live non-root Lean check source as a source-only role."""
    _lean_gate_root(classifier, graph, catalog, entry, REVIEWED_LEAN_CHECKS if reviewed is None else reviewed,
                    REVIEWED_LEAN_CHECK_INVOCATIONS if invocations is None else invocations, LEAN_CHECK_FORM)


def lean_fixture_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H1015: a reviewed live non-root Lean fixture source as a source-only role.

    The H999 rules with lean_fixture_interface: consumption by its drivers
    only, never a check-only source and never elaboration, pass or proof."""
    _lean_gate_root(classifier, graph, catalog, entry, REVIEWED_LEAN_FIXTURES if reviewed is None else reviewed,
                    REVIEWED_LEAN_FIXTURE_INVOCATIONS if invocations is None else invocations, LEAN_FIXTURE_FORM)


def _outside_root_libraries(repo, path):
    """No root lakefile*.toml library or executable can name path's module."""
    import tomllib
    top = path.split('/')[0]
    for name in sorted(n for n in repo.texts if '/' not in n and re.fullmatch(r'lakefile.*\.toml', n)):
        try: config = tomllib.loads(repo.texts[name])
        except ValueError: return False
        for target in config.get('lean_lib', []) + config.get('lean_exe', []):
            source = target.get('srcDir', '.') if isinstance(target, dict) else None
            if not isinstance(source, str): return False
            source = posixpath.normpath(source)
            if source != '.':
                if path.startswith(source + '/') or source.startswith(('..', '/')): return False
                continue
            lists = [target.get(k, []) for k in ('roots', 'globs')]
            if any(not isinstance(x, list) for x in lists): return False
            names = [target.get('name'), target.get('root')] + lists[0] + lists[1]
            if any(not isinstance(n, str) or n.split('.')[0] in (top, '*', '+') for n in names if n is not None): return False
    return True


def lean_fixture_controls(env):
    """(9) H1015 controls, run by successor_controls with its helpers: the
    reviewed set, the fixture interface, the role and its negative controls."""
    global REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, route, frame, gate, reviewed_nonpy, files = (env[k] for k in (
        'commit', 'run', 'rejected', 'blob', 'route', 'frame', 'gate', 'reviewed_nonpy', 'files'))
    code = env['classifier']['lean_code']
    # The audited witnesses: 7 sources, 22 driver lines, all reviewed H997 drivers, disjoint from H999.
    assert len(REVIEWED_LEAN_FIXTURES) == 7 and len(REVIEWED_LEAN_FIXTURE_INVOCATIONS) == 22
    assert {(p, b) for p, b, _ in REVIEWED_LEAN_FIXTURES} == {(p, b) for p, b, _, _, _ in REVIEWED_LEAN_FIXTURE_INVOCATIONS}
    assert not {p for p, _, _ in REVIEWED_LEAN_FIXTURES} & {p for p, _, _ in REVIEWED_LEAN_CHECKS}
    assert all((d, db) in {(q, b) for q, b, _ in reviewed_nonpy} and (d, db, n) in {(d, b, n) for _, _, d, b, n in REVIEWED_LEAN_CHECK_INVOCATIONS}
               for _, _, d, db, n in REVIEWED_LEAN_FIXTURE_INVOCATIONS)
    assert ('tests/directruntime-20261104/control-tuples/ProductionControls.lean', 'ca25c4ca010fa72c0512c2b7523fabcccbbad7e7',
            '2366c57f099b27d4673dda504d258ba77ff3fcaf') in REVIEWED_LEAN_FIXTURES
    G, X = LEAN_CHECK_DRIVER_LINE, 'tests/f/F.lean'
    fixture = 'import Lib.Mod tests.f.Dep\n-- fixture\n\ndef F.v : Nat := 1\n#eval IO.FS.readFile "tests/data.txt"\ntheorem F.t : F.v = 1 := rfl\n'
    check = 'import Lib.Mod\n#check D.v\n'
    face = {'imports': ['Lib.Mod', 'tests.f.Dep'], 'body_line': 4}
    assert lean_fixture_interface(code, X, fixture) == face
    assert lean_fixture_interface(code, X, 'import A B -- c\n/- x -/\nrun_elab pure ()\n') == {'imports': ['A', 'B'], 'body_line': 3}
    assert lean_fixture_interface(code, X, 'import A\nopen A\n@[simp] private def x := 1\n#check x\n') == {'imports': ['A'], 'body_line': 2}
    for t in ('', 'import A\n', '-- c\n', 'def x := 1\n', fixture + 'import B\n', 'prelude\n' + fixture, fixture.replace('-- fixture', 'module'),
              fixture + '#exit\n', fixture + '  #exit\n', ' import A\n#eval 1\n', 'import A\r\n#eval 1\n', fixture + '\0\n', 'import A.\n#eval 1\n',
              check, 'import A\n#print axioms A\n', fixture.replace('\n', '\n\x0b', 1), 'import A\n#check Foo -- see "x"\n',
              'import A\n#check (Foo)\n', 'import A\nopen A\n#check Foo\n', 'import A\nset_option x true\n#print A\n', 'import A\n  def x := 1\n',
              'import A\ndef x := 1 #exit\n', 'import A\nset_option x true in #exit\n#eval 1\n', 'import all A\n#eval 1\n', 'import A\n#evaluate 1\n'):
        assert lean_fixture_interface(code, X, t) is None, t
    assert lean_fixture_interface(code, 'x.py', fixture) is None and lean_check_interface(code, X, fixture) is None
    head = '#!/usr/bin/env bash\nset -euo pipefail\nfiles=(tests/f/F.lean tests/f/C.lean tests/f/I.lean tests/f/X.lean tests/fpkg/F.lean)\n'
    driver = head + G + '\n'; gl = 4
    add = {'scripts/coord-tools/gate.sh': gate, 'tests/f/run.sh': driver, 'tests/f/exec.sh': driver.replace('set -euo pipefail\n', 'exec true\n'),
           X: fixture, 'tests/f/Dep.lean': 'def Dep.v : Nat := 1\n', 'tests/f/C.lean': check, 'tests/f/I.lean': fixture, 'tests/f/J.lean': 'import tests.f.I\n',
           'tests/f/X.lean': fixture + '#exit\n', 'tests/fpkg/lakefile.toml': 'name = "fpkg"\n', 'tests/fpkg/F.lean': fixture}
    lf = commit(add, 'Lean fixtures'); L = lf.ref; ll = commit({'tests/unrelated.txt': 'F\n'}, 'Lean fixtures later')
    assert lean_check_invocation(driver, X, gl) and not lean_check_invocation(add['tests/f/exec.sh'], X, gl)
    call = lambda d='tests/f/run.sh', **k: dict({'driver': d, 'driver_blob': blob(lf, d), 'driver_commit': L, 'line': gl}, **k)
    mk = lambda p=X, kind=LEAN_FIXTURE_KIND, interface=face: {
        'path': p, 'input_revision': L, 'source_blob': blob(lf, p), 'kind': kind, 'command': lean_check_command(p), 'interface': interface,
        'provenance': {'commit': L, 'path': p, 'blob': blob(lf, p)}, 'invocations': [call()], 'purpose': 'Synthetic fixture.'}
    role = mk(); base_model, base = run(ll, entries=[])
    assert base[X]['class'] != 'keep' and base['tests/f/Dep.lean']['class'] != 'keep'
    srcs = (X, 'tests/f/C.lean', 'tests/f/I.lean', 'tests/f/X.lean', 'tests/fpkg/F.lean')
    drivers = {(d, blob(lf, d), L) for d in ('tests/f/run.sh', 'tests/f/exec.sh')}
    saved = REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    REVIEWED_LEAN_FIXTURES = frozenset({(p, blob(lf, p), L) for p in srcs})
    REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset({(p, blob(lf, p), d, blob(lf, d), gl) for p in srcs for d in ('tests/f/run.sh', 'tests/f/exec.sh')})
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
    try:
        for repo in (lf, ll):
            model, rows = run(repo, standalone=[role]); entry = model['entry_points']['lean-fixture:' + X]
            assert rows[X]['class'] == 'keep' and entry['source_only'] and entry['lean_fixture_role'] and not entry.get('lean_check_role')
            assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['location'] == 'tests/f/run.sh:%d' % gl
            assert entry['command'] == 'lake lean tests/f/F.lean -- --tstack=131072' and entry['invocations'] == role['invocations']
            assert entry['interface'] == face and entry['provenance'] == role['provenance']
            if repo is ll:  # no import-dependency, driver, read, proof or runtime credit
                assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != X)
                assert set(model['entry_points']) == set(base_model['entry_points']) | {'lean-fixture:' + X}
        _, rows = run(ll, {'static_routes': [route(lf, 'lean-fixture:' + X, 'lean-readFile', [frame(lf, X, 5)], 'tests/data.txt')]}, standalone=[role])
        assert rows['tests/data.txt']['class'] != 'keep'
        Z = '0' * 40
        for change, text in (({'extra': 1}, 'invalid Lean fixture'), ({'purpose': ' '}, 'invalid Lean fixture'), ({'invocations': []}, 'invalid Lean fixture'),
                             ({'invocations': [call(), call()]}, 'invalid Lean fixture'), ({'invocations': [call(line=str(gl))]}, 'invalid Lean fixture'),
                             ({'invocations': [call(command=['bash'])]}, 'invalid Lean fixture'), ({'provenance': {'commit': L}}, 'invalid Lean fixture'),
                             ({'input_revision': 'HEAD'}, 'full commit revision'), ({'command': ['lean', X]}, 'unsupported Lean fixture role invocation'),
                             ({'command': ['lake', 'env', 'lean', X]}, 'unsupported Lean fixture role invocation'),
                             ({'command': lean_check_command(X) + ['x']}, 'unsupported Lean fixture role invocation'),
                             ({'source_blob': Z}, 'unreviewed Lean fixture role'), ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed Lean fixture role'),
                             ({'invocations': [call(line=gl - 1)]}, 'role invocation'), ({'invocations': [call(driver_blob=Z)]}, 'role invocation'),
                             ({'invocations': [call(driver_commit=Z)]}, 'role invocation'),
                             ({'invocations': [call(), call('tests/f/exec.sh')]}, 'Lean fixture role driver does not run the source'),
                             ({'interface': dict(face, body_line=2)}, 'Lean fixture role interface mismatch'),
                             ({'interface': {'imports': ['Lib.Mod'], 'check_lines': [2], 'axiom_lines': []}}, 'interface mismatch'),
                             ({'input_revision': Z}, 'unverifiable historical')):
            rejected(lf, text, standalone=[dict(role, **change)])
        rejected(lf, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')])
        # One path, one role: a check-only source is never a fixture; a fixture is never a check role.
        rejected(lf, 'conflicting standalone', standalone=[role, mk(kind=LEAN_CHECK_KIND)])
        rejected(lf, 'audited fixture interface', standalone=[mk('tests/f/C.lean')])
        rejected(lf, 'audited fixture interface', standalone=[mk('tests/f/X.lean')])
        rejected(lf, 'unreviewed Lean check role', standalone=[mk(kind=LEAN_CHECK_KIND)])
        for path in ('tests/f/I.lean', 'tests/fpkg/F.lean'):  # importer, Lake package: stale
            assert 'lean-fixture:' + path not in run(lf, standalone=[mk(path)])[0]['entry_points']
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy
        rejected(lf, 'unreviewed Lean fixture role invocation', standalone=[role])
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {('tests/f/run.sh', blob(lf, 'tests/f/run.sh'), env['A'])}
        rejected(lf, 'Lean fixture role driver lacks its introducing provenance', standalone=[dict(role, invocations=[call(driver_commit=env['A'])])])
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
        for order in (1, -1):  # a current definition supersedes
            model, _ = run(ll, standalone=[dict(role, input_revision=ll.ref, purpose='Now.'), role][::order])
            assert model['entry_points']['lean-fixture:' + X]['purpose'] == 'Now.'
        writer = {'path': X, 'blob': blob(lf, X), 'line': 5, 'literal': 'out.json'}
        policy = {'path': 'tests/gen/.gitignore', 'blob': blob(lf, 'tests/gen/.gitignore'), 'purpose': 'P.', 'matches': [{'line': 1, 'output': 'out.json', 'writer': writer}]}
        rejected(lf, 'not an entry point source', {'git_policies': [policy]}, standalone=[role])
        # A root library, changed gate.sh, source or driver drops the root later; a current claim on changed bytes is refused.
        for changes in ({'lakefile.toml': files['lakefile.toml'] + '[[lean_lib]]\nname = "tests"\n'}, {'scripts/coord-tools/gate.sh': gate.replace('131072', '65536')},
                        {X: fixture + '#eval 2\n'}, {'tests/f/run.sh': driver + 'echo\n'}, {'tests/f/J.lean': 'import tests.f.F\n'}):
            edited = commit(changes, 'edited')
            model, rows = run(edited, standalone=[role])
            assert 'lean-fixture:' + X not in model['entry_points'] and rows[X]['class'] != 'keep', changes
            if X in changes or 'tests/f/run.sh' in changes: rejected(edited, 'source mismatch', standalone=[dict(role, input_revision=edited.ref)])
            commit({'scripts/coord-tools/gate.sh': gate, X: fixture, 'tests/f/run.sh': driver, 'tests/f/J.lean': 'import tests.f.I\n',
                    'lakefile.toml': files['lakefile.toml']}, 'restored')
        REVIEWED_LEAN_FIXTURES = frozenset()
        rejected(lf, 'unreviewed Lean fixture role', standalone=[role])
    finally: REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES = saved


def nonpy_roleset_controls(env):
    """H1025 controls, run by the H997 self-test section (7) with its helpers:
    the reviewed widening, its T: table form and negative controls."""
    global REVIEWED_NONPY_ENTRIES
    run, rejected, blob, first, A, sh_role = (env[k] for k in ('run', 'rejected', 'blob', 'first', 'A', 'sh_role'))
    rows = REVIEWED_NONPY_ENTRIES_H1025; paths = {p for p, _, _ in rows}
    # 61 rows, one per path, disjoint from H997 and outside x1e-classify-runtime-upstream's directories.
    assert len(rows) == len(paths) == 61 and rows <= REVIEWED_NONPY_ENTRIES and len(REVIEWED_NONPY_ENTRIES) == 178
    assert not paths & {p for p, _, _ in REVIEWED_NONPY_ENTRIES - rows}
    # H1004 form (1): two H28 Node programs, one row per path, disjoint from the rest.
    h1004 = REVIEWED_NONPY_ENTRIES_H1004
    assert len(h1004) == len({p for p, _, _ in h1004}) == 2 and h1004 <= REVIEWED_NONPY_ENTRIES and not h1004 & rows
    assert {p for p, _, _ in h1004} == {'tests/h28-sol/type-grammar/run_solc.mjs', 'tests/h28-sol/literal-grammar/solc-fixtures.mjs'}
    assert not {p for p, _, _ in h1004} & {p for p, _, _ in REVIEWED_NONPY_ENTRIES - h1004}
    assert all(p.startswith('tests/') and not p.startswith(('tests/directruntime-20261104/', 'tests/upstream/'))
               and posixpath.splitext(p)[1] in NONPY_SHEBANGS and '.test.' not in posixpath.basename(p) for p in paths)
    for row in (('tests/backend-environment/ownership.mjs', 'c7e75bcd68c0b2347212973ffdfeba0c285362f9', 'fd67008ed20590639e04345fbb12a9dfa645a95f'),
                ('tests/calldata-packets-1105/RawBool/run.sh', '55360017e55cefeb16029be0097366c7a4169d5d', '4d45820cc26824ca2ba1da8177be755655f820f5'),
                ('tests/fullscope-20261104/vt1/check-data.sh', '3202285954d3b54c59db4db8f814d0d30234ed44', '4131f468b7417ddf46c32d188d10ac6d85e03ef8')):
        assert row in rows, row
    # Refused rows stay out: the removed program and the later cherry-pick provenance.
    assert 'tests/fullscope-20261104/vo1/mcp-check.sh' not in {p for p, _, _ in REVIEWED_NONPY_ENTRIES}
    cc = 'tests/sol-expression-uniqueness/compiler-controls.mjs', '195438b74253dc632524ed0cc0a1348d54a30968'
    assert [c for p, b, c in REVIEWED_NONPY_ENTRIES if (p, b) == cc] == ['1058aa95dfe0fccdbcd468fe8b52555168a730e9']
    assert not any(c == '9e74823267a4b646cc0fb8acbb14cedb24366d75' for _, _, c in REVIEWED_NONPY_ENTRIES)
    # The T: form expands to tests/; an unbound row or unknown abbreviation is refused.
    b = blob(first, 'tests/drive.sh'); t = _review_table('@' + A + '\nT:drive.sh ' + b + '\n')
    assert t == {('tests/drive.sh', b, A)}
    for text in ('T:drive.sh ' + b, '@' + A + '\nX:drive.sh ' + b, '@' + A + '\nT:drive.sh'):
        try: _review_table(text); raise AssertionError(text)
        except (ValueError, KeyError): pass
    # The widened set admits no other program; a T: row admits it exactly as an H997 row does.
    rejected(first, 'unreviewed non-Python entry role', standalone=[sh_role])
    saved = REVIEWED_NONPY_ENTRIES; REVIEWED_NONPY_ENTRIES = saved | t
    try:
        model, rs = run(first, standalone=[sh_role])
        assert rs['tests/drive.sh']['class'] == 'keep' and model['entry_points']['nonpy-entry:tests/drive.sh']['source_only']
        rejected(first, 'unreviewed non-Python entry role', standalone=[dict(sh_role, provenance=dict(sh_role['provenance'], commit='0' * 40))])
    finally: REVIEWED_NONPY_ENTRIES = saved


PY_IMPORT_KIND = 'python-import-source-role'
PY_IMPORT_PREFIX = 'py-import:'
# H1051 (gh#1373, H62-PYTHON-HELPER-ROUTES, Option A): an opt-in Python helper
# source imported by kept `python3 -B IMPORTER` entry roots through exact
# sibling-module resolution (sys.path[0] is the importer's directory). Helpers
# (path, blob, introducing commit) and imports (helper, helper blob, importer,
# importer blob, importer introducing commit, import line), reviewed one by one
# from x1e-classify-h62-scripts' list. Refused, left unresolved: any import that
# fails python_import_statement (after-baseline.py's sys.path.insert and
# candidate.py's importlib use are refused importers; their helpers keep their
# other reviewed importer). H1004 form (3) adds the three H28 helpers of
# x1e-classify-h28-h55; workers.py is imported by run.py through its one exact
# sys.path.insert of its runtime/ subdirectory. Source/consumption only: no
# execution, import, pass, read, fixture, child, output, proof or runtime credit.
_PY_IMPORT_ROWS = '''
@8a1794652d299cd042c815441a426e7efb642522
H:item2/audit-abi-world/receipts.py f863fce768398bc7b8cf6f74c8998a746d454a16
 H:item2/audit-abi-world/accept_runtime.py 5a0df8230341bd078680f542be8921e23c208c92 38aef082f5b0e96e257fb91b62d8e432e8eec48d 6
 H:item2/audit-abi-world/coverage.py c2c8b01802fa3500b1cdc15fe00f870487c83605 38aef082f5b0e96e257fb91b62d8e432e8eec48d 39
 H:item2/audit-abi-world/extract_vectors.py ce6483f9dae3fe02dbe716cee03436ed401f777a 38aef082f5b0e96e257fb91b62d8e432e8eec48d 6
@8e3023d10b62574b7be84630c064b53b8dcfbb09
H:item2/audit-abi-world/resume_sources.py 714d79517abf92322b312a25223adcb55ba82050
 H:item2/audit-abi-world/resume_accept.py 57cdfd9506bb1573432358e179b8d060c9612d92 a37430cd3673749dee65c301a069792efd1bccab 12
 H:item2/audit-abi-world/resume_mcp_call.py 68a3a88a246c7da9a75e247c890bedb87206a28e 8e3023d10b62574b7be84630c064b53b8dcfbb09 39
@c1384ed9310f9c5402d521036d0c75cacf79fc99
H:item2/audit-calculus/owners.py c471b8400bc553a8bd554c3b335bb6074bfc9a33
 H:item2/audit-calculus/acceptance.py 675133d51e0202e01e5cf4532a26996debb4371e c361178f68f34c276a02b15691cd726aaa85a51e 11
@febcbe09fe79e890c66baf4f266490beb674a357
H:item2/audit-language/gate_repair.py 84db13d263f185022e5e24b65c2f1ae7eaa37c63
 H:item2/audit-language/check.py 367616d8d65dd2bd6abb1e5fac7138050f2acc78 16e98ad46223e6fe4a97dadb8187497537f57dce 56
 H:item2/audit-language/retire_export.py 4748376ef83284136230125977bd0725e39fe43a 16e98ad46223e6fe4a97dadb8187497537f57dce 34
 H:item2/audit-language/verify.py 9f433a190b2e3da5ef46fbc977741621c6b807ba 16e98ad46223e6fe4a97dadb8187497537f57dce 22
@107cb28c032e3bff522ff6db0fdf0be54b2bbefd
H:item2/audit-theories/pending_impossibility.py 2bf62f1f7376305a6e152d1d7f3db2ba6da6de3f
 H:item2/audit-theories/coverage_ledger.py c459994e09c06ade984aabd8af6483287f5f215a 107cb28c032e3bff522ff6db0fdf0be54b2bbefd 12
 H:item2/audit-theories/mutability_input_roles.py c67019762b0c5dfb9d489b756866d5fa353131ca 107cb28c032e3bff522ff6db0fdf0be54b2bbefd 11
 H:item2/audit-theories/verify_acceptance_snapshot.py c805842b75bc519260d857f9730671c78421cbe1 107cb28c032e3bff522ff6db0fdf0be54b2bbefd 15
@56a137f709aa737d2e3886aca2daf9f52b40261c
H:item4/generic-primitive-packets/runtime.py 015e64e5fac885e6962e5bd90fe284b9c1ae2820
 H:item4/generic-primitive-packets/check.py c4be638c1f7ecb46ffcb3d6ff1cafa95c1ea3a54 0a34d9c508ca24f6a914553953a0bc4abf5863dc 18
 H:item4/generic-primitive-packets/measure.py b108aa52de426ccb7058056ebd39ce1ea18f9b50 0a34d9c508ca24f6a914553953a0bc4abf5863dc 17
@df554535e9c8d308276a99ea23611c7d63ae5919
H:item6/migrate-hash/lean_lex.py 98e527e654c4ed29919d56c4d343a72e75fca3fa
 H:item6/migrate-hash/census.py 0ddef2ed5405c2bbcd8ff199c43097a7a847147a df554535e9c8d308276a99ea23611c7d63ae5919 13
 H:item6/migrate-hash/full_measure.py cae845b44b6c50bd6ea69065b113099fe40eb73d df554535e9c8d308276a99ea23611c7d63ae5919 9
@d48bc8cb306d50626864c00c53cdd5c585438ec0
H:item6/migrate-lowering/process_group.py 31d1dba2b8ff9c33da3c25758b83227a7bebe5e3
 H:item6/migrate-lowering/bounded.py b4c9edefa18f3c1b3dd7f11f8ffa46c61aaf31bd aa07794d3f1084a560f308c2b469198a577ee1a5 6
 H:item6/migrate-lowering/supervise.py 38d19f87951efbbb531a321d9e0d48604ca4a78e aa07794d3f1084a560f308c2b469198a577ee1a5 4
@4e7929f0bf488c8c23c7b42f6a186121c6951a4c
H:item6/migrate-precompiles/contract.py 292e032d3602f997b88830c25d51bca1cc95f883
 H:item6/migrate-precompiles/census.py 634868cff19058fe2d32bbfc691c2c2694c23b3b d393a60b76120dfab477e62c569f11cf34cdcfcb 7
@df554535e9c8d308276a99ea23611c7d63ae5919
H:item6/migrate-root-gate/release_integrity.py 49a4e4707d6bfdcedef222b66a2f2af9df73c536
 H:item6/migrate-root-gate/cache-roundtrip.py ff642bece78b93da3e6cd534cdb66de4e73506b0 df554535e9c8d308276a99ea23611c7d63ae5919 19
@40be303ce78a6d6bcad5d4c4b8c7285cc1732767
H:item6/migrate-semantics/bounded.py 921f0c36065a3d5ba781b7fd46f324a5bf1c07a3
 H:item6/migrate-semantics/api_evidence.py 4cb5c110945cbeffa15ea2f48bb8a05d2fb29a9b 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 5
 H:item6/migrate-semantics/cgroup_controls.py ec85416b5b4134dc11fa801c4cb596109edfaa0a 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 5
 H:item6/migrate-semantics/cgroup_prerequisite.py eeb10340cfd2da86bc9f5839ef69dd3ad15f7fef 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 5
 H:item6/migrate-semantics/compare_samples.py c3fbd043c55091388a581dafe6cc6cdfc6a0e4ed 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 5
 H:item6/migrate-semantics/measure.py 2875c98d5b0ddb2fb825542114452b838a6f9bea 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 6
 H:item6/migrate-semantics/owner_hash_fixture.py 3e65a61636afff9d97f7f5bc9facd0425b8b7b94 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 5
 H:item6/migrate-semantics/probe.py d99f64b94069c8ef9d83c5f0be79c8fb99d61a28 40be303ce78a6d6bcad5d4c4b8c7285cc1732767 6
@22e91b98298078b2f7b43d0a9bd5e1553b7eb17d
T:h28-sol/automation-benchmark/scope_policy.py d4dc3f8b3abf74db4759b03dbb84b8e1bdfc9bbe
 T:h28-sol/automation-benchmark/test_scope_policy.py 01146f6d8222a26bc34a89beab21211c5cf3b440 bf64bc529d40d2dfc63d34f26b262c70f77a19de 2
@50a5679e38aeaf468850d8f46645bdf5e71aa706
T:h28-sol/mutation-testing/tools/selected_accounting.py 585c80fd909f44f89c526c3c9b9d999457374b82
 T:h28-sol/mutation-testing/tools/check_selected_controls.py fb128da9f4fc433f60f35560c05d5af7d4523888 50a5679e38aeaf468850d8f46645bdf5e71aa706 12
 T:h28-sol/mutation-testing/tools/verify_combined.py 521bd933f52e0bb6acd24d3864e506ac3a44a847 50a5679e38aeaf468850d8f46645bdf5e71aa706 106
@de1d76d922d7ff42d3a07bc020b740f8ec9f0105
T:h28-sol/non-vacuity/runtime/workers.py e375ec6f6126d4e3f6046fdfa5e9f421ef7e21f4
 T:h28-sol/non-vacuity/run.py f81c3d2a7b8a650b9a9e6d7f62c1e2083025586a de1d76d922d7ff42d3a07bc020b740f8ec9f0105 5
'''
_IMPORT_SHADOWS = frozenset({'importlib', 'imp', 'runpy', 'pkgutil', 'zipimport', 'site', 'builtins', '__builtins__',
                             '__import__', 'exec', 'eval', 'chdir', 'fchdir'})
_SYS_IMPORT_STATE = frozenset({'path', 'modules', 'meta_path', 'path_hooks', 'path_importer_cache', 'flags'})


def _import_table(text):
    """`@COMMIT` then `H:helper blob` rows, each followed by indented
    `importer blob commit line` rows (paths relative to _REVIEW_DIRECTORIES)."""
    helpers, imports, commit, helper = set(), set(), None, None
    for line in filter(str.strip, text.split('\n')):
        if line.startswith('@'): commit = line[1:]; helper = None; continue
        words = line.split()
        if line.startswith(' '):
            if helper is None or len(words) != 4: raise ValueError('invalid import review table')
            imports.add(helper + (_REVIEW_DIRECTORIES[words[0][:2]] + words[0][2:], words[1], words[2], int(words[3])))
            continue
        if commit is None or len(words) != 2: raise ValueError('invalid import review table')
        helper = (_REVIEW_DIRECTORIES[words[0][:2]] + words[0][2:], words[1]); helpers.add(helper + (commit,))
    return frozenset(helpers), frozenset(imports)


PY_IMPORT_HELPERS, PY_IMPORT_IMPORTS = _import_table(_PY_IMPORT_ROWS)


def _import_shadowed(helper, tree):
    """A package, another M.* file or a cached M.* beside the helper M.py."""
    directory, name = posixpath.split(helper)
    base = directory + '/' if directory else ''
    prefix = base + name[:-3]
    return any(p.startswith(prefix + '/') or p.startswith(prefix + '.') and p != helper
               or p.startswith(base + '__pycache__/' + name[:-3] + '.') for p in tree)


def python_import_statement(text, importer, line, helper, tree):
    """The names one static import binds from the sibling helper, or None.

    The statement at `line` of the importer is the only import node there:
    `import M` (one alias) or `from M import n, ...` (absolute, no `*`), M the
    helper's basename stem, a plain non-keyword identifier outside the
    standard library and built-in module names, and the helper in the
    importer's directory. Not audited, giving None: a package directory or any
    other `M.*` file beside the helper (FileFinder prefers packages and
    extension modules), any use of importlib, imp, runpy, pkgutil, zipimport,
    site, builtins, __import__, exec, eval or chdir, any sys.path, sys.modules,
    meta_path, path_hooks, path_importer_cache or sys.flags access, an aliased
    sys, sys reached through another object (`.sys`, `__dict__`, `from os
    import sys`) or used other than as `sys.ATTR`, a `from sys import` of
    import state, getattr/setattr/delattr/vars on sys, a dunder stem or a
    `__pycache__/M.*` file. Not audited (consumption credit only): what the
    importer's earlier sibling imports do at run time, whether the statement
    is reached, and the interpreter environment (PYTHONPATH, PYTHONSAFEPATH,
    site customisation).

    H1004 form (3) adds one exact path form: the helper is in the importer's
    subdirectory D when the module body has exactly one statement
    `sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent/'D'))`
    (D a plain name), after top-level plain `import pathlib` and `import sys`
    and before a top-level import statement at `line`; sys, pathlib, str and
    __file__ are never rebound (assignment, attribute store, argument,
    definition, except or match capture, import alias or star import) and no
    `M.py`, `M.*` or `M/` sits in the importer's own directory. That statement
    is the only sys.path access allowed.
    """
    import keyword, sys as interpreter
    directory, name = posixpath.split(helper)
    module = name[:-3] if name.endswith('.py') else ''
    if (not module.isidentifier() or keyword.iskeyword(module) or module.startswith('__')
            or module in interpreter.stdlib_module_names or module in interpreter.builtin_module_names):
        return None
    if _import_shadowed(helper, tree): return None
    try: parsed = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    home = posixpath.dirname(importer); skip = set()
    if home != directory:
        sub = posixpath.basename(directory)
        if posixpath.dirname(directory) != home or sub in ('', '.', '..') or '\\' in sub: return None
        template = ast.dump(ast.parse('sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent/' + repr(sub) + '))').body[0])
        inserts = [k for k, n in enumerate(parsed.body) if ast.dump(n) == template]
        if len(inserts) != 1: return None  # any other sys.path access is refused by the walk below
        at = inserts[0]
        for want in ('pathlib', 'sys'):
            if not any(isinstance(n, ast.Import) and any(a.name == want and a.asname is None for a in n.names) for n in parsed.body[:at]): return None
        stem = posixpath.join(home, module)
        if any(q == stem + '.py' or q.startswith(stem + '/') or q.startswith(stem + '.') for q in tree): return None  # no script-directory candidate
        if not any(isinstance(n, (ast.Import, ast.ImportFrom)) and n.lineno == line for n in parsed.body[at + 1:]): return None
        fixed = {'sys', 'pathlib', 'str', '__file__'}
        for n in ast.walk(parsed):
            if (isinstance(n, ast.Name) and n.id in fixed and not isinstance(n.ctx, ast.Load) or isinstance(n, ast.arg) and n.arg in fixed
                    or isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name in fixed
                    or isinstance(n, (ast.Global, ast.Nonlocal)) and set(n.names) & fixed
                    or isinstance(n, ast.alias) and ((n.asname or '') in fixed or n.name in ('str', '__file__'))
                    or isinstance(n, ast.ImportFrom) and any(a.name in fixed or a.name == '*' for a in n.names)
                    or isinstance(n, ast.ExceptHandler) and n.name in fixed
                    or isinstance(n, (ast.MatchAs, ast.MatchStar)) and n.name in fixed
                    or isinstance(n, ast.Attribute) and not isinstance(n.ctx, ast.Load) and isinstance(n.value, ast.Name) and n.value.id in fixed): return None
        skip = {id(n) for n in ast.walk(parsed.body[at])}
    parents = {child: node for node in ast.walk(parsed) for child in ast.iter_child_nodes(node)}
    found = []
    for n in ast.walk(parsed):
        if id(n) in skip: continue
        if isinstance(n, ast.Name) and n.id in _IMPORT_SHADOWS: return None
        if isinstance(n, ast.Name) and n.id == 'sys' and not (isinstance(parents.get(n), ast.Attribute) and parents[n].value is n): return None
        if isinstance(n, ast.Attribute) and (n.attr in ('chdir', 'fchdir', '__import__', 'sys', '__dict__')
                                             or n.attr in _SYS_IMPORT_STATE and isinstance(n.value, ast.Name) and n.value.id == 'sys'): return None
        if isinstance(n, ast.Import):
            for a in n.names:
                if a.name.split('.')[0] in _IMPORT_SHADOWS or a.name == 'sys' and a.asname not in (None, 'sys'): return None
        if isinstance(n, ast.ImportFrom):
            if (n.module or '').split('.')[0] in _IMPORT_SHADOWS or any(a.name in _IMPORT_SHADOWS or a.name == 'sys' for a in n.names): return None
            if n.module == 'sys' and any(a.name in _SYS_IMPORT_STATE or a.name == '*' for a in n.names): return None
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ('getattr', 'setattr', 'delattr', 'vars')
                and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id == 'sys'): return None
        if isinstance(n, (ast.Import, ast.ImportFrom)) and n.lineno == line: found.append(n)
    if len(found) != 1: return None
    n = found[0]
    if isinstance(n, ast.Import):
        return [] if len(n.names) == 1 and n.names[0].name == module else None
    if n.level != 0 or n.module != module or any(a.name == '*' for a in n.names): return None
    return sorted({a.name for a in n.names})


def python_import_bindings(text):
    """Names a helper binds at module top level (definitions, plain assignment
    targets and import aliases), or None when it does not parse."""
    try: parsed = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    names = set()
    for n in parsed.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)): names.add(n.name)
        elif isinstance(n, (ast.Assign, ast.AnnAssign)):
            for t in (n.targets if isinstance(n, ast.Assign) else [n.target]):
                names.update(e.id for e in ast.walk(t) if isinstance(e, ast.Name))
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            names.update((a.asname or a.name).split('.')[0] for a in n.names if a.name != '*')
    return names


def python_import_root(classifier, graph, catalog, entry, reviewed=None, imports=None):
    """H1051: a reviewed Python helper imported by kept entry roots, as a source-only role.

    Run after every other standalone definition (LATE_SOURCE_ROLE_KINDS) so
    the importers' roots exist. Binds the helper (path, blob, introducing
    commit, interface {'module', 'names'}) and each import (importer, blob,
    introducing commit, line): every importer is a current root whose command
    is exactly `python3 -B IMPORTER`, the statement passes
    python_import_statement and every imported name is a top-level binding of
    the helper. A shadowing package or `M.*` file, or a missing importer root
    at a later revision, makes it stale. Never a validated runner; anchors
    nothing. Kept later while helper and importers are unchanged; a current
    definition of the path supersedes it."""
    repo = graph.repo; role = 'Python import role'
    reviewed = PY_IMPORT_HELPERS if reviewed is None else reviewed
    imports = PY_IMPORT_IMPORTS if imports is None else imports
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'imports', 'purpose'}
    _role_schema(classifier, catalog, entry, required, role); calls = entry['imports']
    if (not isinstance(calls, list) or not calls or any(not isinstance(c, dict) or set(c) != {'importer', 'importer_blob', 'importer_commit', 'line'}
                   or type(c['line']) is not int or not all(isinstance(c[k], str) for k in ('importer', 'importer_blob', 'importer_commit')) for c in calls)
            or len({canonical(c) for c in calls}) != len(calls)):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if not p.endswith('.py') or _clean(p) != p or entry['command'] != ['python3', '-B', calls[0]['importer']]:
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed ' + role + ': ' + p)
    if any((p, blob, c['importer'], c['importer_blob'], c['importer_commit'], c['line']) not in imports for c in calls):
        raise ValueError('unreviewed ' + role + ' import: ' + p)
    pins = [(p, blob)] + [(c['importer'], c['importer_blob']) for c in calls]
    if not _role_current(classifier, repo, catalog, entry, pins): return
    if any(repo.tree[q][0] not in ('100644', '100755') or q not in repo.texts for q, _ in pins):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    if not all(_introduced(classifier, repo, c['importer_commit'], c['importer'], c['importer_blob']) for c in calls):
        raise ValueError(role + ' importer lacks its introducing provenance: ' + p)
    module = posixpath.basename(p)[:-3]
    if _import_shadowed(p, repo.tree):
        if revision == repo.ref: raise ValueError(role + ' helper is shadowed: ' + p)
        return  # shadowed later: stale
    bound = python_import_bindings(repo.texts[p])
    if bound is None: raise ValueError(role + ' helper does not parse: ' + p)
    names = set()
    for c in calls:
        found = python_import_statement(repo.texts[c['importer']], c['importer'], c['line'], p, repo.tree)
        if found is None: raise ValueError(role + ' import is not an exact sibling import: ' + c['importer'])
        if not set(found) <= bound: raise ValueError(role + ' imports an unbound helper name: ' + c['importer'])
        names.update(found)
        command = shlex.join(['python3', '-B', c['importer']])
        if not any(r['path'] == c['importer'] and r['command'] == command and not r.get('python_import_role')
                   and r.get('source_blob', c['importer_blob']) == c['importer_blob'] for r in graph.roots.values()):
            if revision == repo.ref: raise ValueError(role + ' importer is not a python3 -B entry root: ' + c['importer'])
            return
    interface = {'module': module, 'names': sorted(names)}
    if canonical(interface) != canonical(entry['interface']): raise ValueError(role + ' interface mismatch: ' + p)
    identity = PY_IMPORT_PREFIX + p
    graph.root(p, 'source-only Python import dependency', shlex.join(entry['command']), calls[0]['importer'], calls[0]['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'python_import_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': interface, 'provenance': doc, 'imports': calls, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed Python helper imported by reviewed python3 -B entry roots through exact sibling-module resolution; never run or certified to import or pass, and the interpreter environment is not audited. Source/consumption role only: no execution, read, fixture, child, generated-output, proof or runtime credit.'}})


def python_import_controls(env):
    """(10) H1051 controls, run by successor_controls with its helpers: the
    reviewed witnesses, the import guards, the role and its negative controls."""
    global PY_IMPORT_HELPERS, PY_IMPORT_IMPORTS
    commit, run, rejected, blob, program = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'program'))
    # The audited witnesses: 11 H62 helpers (27 sibling imports) and 3 H28 helpers (4 imports,
    # one through run.py's runtime/ path insert); one row per path.
    helpers = {p for p, _, _ in PY_IMPORT_HELPERS}
    assert len(PY_IMPORT_HELPERS) == len(helpers) == 14 and len(PY_IMPORT_IMPORTS) == 31
    assert len([p for p in helpers if p.startswith('scripts/h62/')]) == 11 and len([p for p in helpers if p.startswith('tests/h28-sol/')]) == 3
    assert all(p.endswith('.py') for p in helpers)
    assert {(p, b) for p, b, _ in PY_IMPORT_HELPERS} == {(p, b) for p, b, _, _, _, _ in PY_IMPORT_IMPORTS}
    assert all(posixpath.dirname(i) == posixpath.dirname(p) or (p, i) == ('tests/h28-sol/non-vacuity/runtime/workers.py', 'tests/h28-sol/non-vacuity/run.py')
               for p, _, i, _, _, _ in PY_IMPORT_IMPORTS)
    # Refused importers stay out: sys.path.insert and importlib use.
    assert not {i for _, _, i, _, _, _ in PY_IMPORT_IMPORTS} & {'scripts/h62/item6/migrate-root-gate/after-baseline.py',
                                                              'scripts/h62/item6/migrate-precompiles/candidate.py'}
    for text in ('@X\nH:a.py b\n  H:c.py d e\n', ' H:c.py d e 1\n', '@X\nH:a.py\n', '@X\nQ:a.py b\n'):
        try: _import_table(text); raise AssertionError(text)
        except (ValueError, KeyError): pass
    # The import guards on synthetic sources.
    H, I = 'tests/pi/util.py', 'tests/pi/run.py'
    tree = {H: 0, I: 0}
    ok = 'from util import VALUE, f\ndef main():\n    print(f())\nmain()\n'
    assert python_import_statement(ok, I, 1, H, tree) == ['VALUE', 'f']
    assert python_import_statement('import util\nimport sys\nprint(sys.argv, util.VALUE)\n', I, 1, H, tree) == []
    assert python_import_statement('import os\ndef g():\n    from util import f\n    return os.path.join(f())\n', I, 3, H, tree) == ['f']
    for text, line in (('import sys\nsys.path.insert(0, "x")\nfrom util import f\n', 3), ('import importlib\nfrom util import f\n', 2),
                       ('from util import *\n', 1), ('import util as u, os\n', 1), ('import util.sub\n', 1), ('from .util import f\n', 1),
                       ('import os\nos.chdir("x")\nfrom util import f\n', 3), ('from util import f\n__import__("util")\n', 1),
                       ('import sys as s\nfrom util import f\n', 2), ('from sys import path\nfrom util import f\n', 2),
                       ('import sys\nsys.modules["util"] = 1\nfrom util import f\n', 3), ('import sys\ngetattr(sys, "path")\nfrom util import f\n', 3),
                       ('exec("x")\nfrom util import f\n', 2), ('import runpy\nfrom util import f\n', 2), ('from util import f\n', 2),
                       ('from util import f; import util\n', 1), ('from other import f\n', 1), ('from util import f\n(', 1),
                       ('import os\nos.sys.path.insert(0, "x")\nfrom util import f\n', 3), ('import sys\nsys.__dict__["path"]\nfrom util import f\n', 3),
                       ('from os import sys\nfrom util import f\n', 2), ('import sys\ndef g(s): pass\ng(sys)\nfrom util import f\n', 4)):
        assert python_import_statement(text, I, line, H, tree) is None, text
    assert python_import_statement(ok, 'tests/other/run.py', 1, H, tree) is None  # not a sibling
    # H1004 form (3): the one exact runtime/ path insert, and its near misses.
    R, W = 'tests/nv/run.py', 'tests/nv/runtime/workers.py'
    ins = "import pathlib,sys\nsys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'runtime'))\nfrom workers import lean_workers\n"
    assert python_import_statement(ins, R, 3, W, {R: 0, W: 0}) == ['lean_workers']
    for text, line in ((ins.replace("'runtime'", "'other'"), 3), (ins.replace('resolve().', ''), 3), (ins.replace('(0,', '(1,'), 3),
                       (ins.replace('insert(0,', 'append('), 3), (ins + 'sys.path.pop(0)\n', 3),
                       (ins.replace('import pathlib,sys\n', 'import sys\nfrom pathlib import Path as pathlib\n'), 4),
                       (ins.replace('import pathlib,sys\n', 'import sys\n') + 'import pathlib\n', 3), (ins + 'str = repr\n', 3),
                       (ins.replace('import pathlib,sys\n', 'import pathlib\n'), 3), (ins + 'try:\n    pass\nexcept E as pathlib:\n    pass\n', 3),
                       (ins + 'match 1:\n    case sys:\n        pass\n', 3), ('from x import *\n' + ins, 4), (ins + 'pathlib.Path = None\n', 3),
                       ('import pathlib,sys\nfrom workers import lean_workers\n' + ins.split('\n', 1)[1], 2),
                       (ins.replace('from workers', 'if 1:\n    from workers'), 4), (ins.replace("sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'runtime'))", "if 1:\n    sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'runtime'))"), 4),
                       (ins.replace('\nfrom', "\nsys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'runtime'))\nfrom"), 4),
                       (ins + 'def f(__file__): pass\n', 3), (ins.replace('import pathlib,sys', 'import pathlib,sys,importlib'), 3)):
        assert python_import_statement(text, R, line, W, {R: 0, W: 0}) is None, text
    assert python_import_statement(ins, R, 3, W, {R: 0, W: 0, 'tests/nv/runtime/workers/__init__.py': 0}) is None
    assert python_import_statement(ins, R, 3, W, {R: 0, W: 0, 'tests/nv/workers.py': 0}) is None  # script-directory candidate
    assert python_import_statement(ins, 'tests/run.py', 3, W, {W: 0}) is None and python_import_statement(ins, R, 3, 'tests/nv/runtime/x/workers.py', {}) is None
    for shadow in ('tests/pi/util/__init__.py', 'tests/pi/util.cpython-312-x86_64-linux-gnu.so', 'tests/pi/util.pyc', 'tests/pi/util/x.txt',
                   'tests/pi/__pycache__/util.cpython-312.pyc'):
        assert python_import_statement(ok, I, 1, H, dict(tree, **{shadow: 0})) is None, shadow
    for name in ('json', 'sys', 'class', 'my-mod', '__main__'):  # standard library, built-in, keyword, not an identifier, dunder
        assert python_import_statement('import ' + name + '\n', 'tests/pi/r.py', 1, 'tests/pi/' + name + '.py', {}) is None, name
    assert python_import_bindings('import os.path as p, json\nfrom x import y\nA, (B, C) = 1, (2, 3)\nD: int = 4\ndef f(): pass\nclass K: pass\nif 1:\n    Z = 1\nE += 1\n') == {
        'p', 'json', 'y', 'A', 'B', 'C', 'D', 'f', 'K'}
    assert python_import_bindings('def (\n') is None
    # The role on a synthetic repository.
    helper = 'VALUE = 1\ndef f():\n    return VALUE\n'
    bad = {'tests/pi/path.py': 'import sys\nsys.path.insert(0, "x")\nfrom util import VALUE\ndef main():\n    print(VALUE)\nmain()\n',
           'tests/pi/lib.py': 'import importlib\nfrom util import VALUE\ndef main():\n    print(VALUE)\nmain()\n',
           'tests/pi/unbound.py': 'from util import missing\ndef main():\n    print(missing)\nmain()\n',
           'tests/pi/deep.py': 'X = 1\n'}
    add = {H: helper + 'from deep import X\n', I: ok, 'tests/pi/run2.py': 'import util\ndef main():\n    print(util.f())\nmain()\n', **bad,
           'tests/pj/json.py': 'X = 1\n', 'tests/pj/run.py': 'import json\ndef main():\n    print(json.X)\nmain()\n'}
    pi = commit(add, 'Python imports'); P = pi.ref; pl = commit({'tests/unrelated.txt': 'P\n'}, 'Python imports later')
    importer = lambda p, repo=pi: dict(program, path=p, input_revision=repo.ref, source_blob=blob(repo, p), command=['python3', '-B', p], entry_line=len(repo.texts[p].splitlines()))
    roots = [importer(I), importer('tests/pi/run2.py')]
    call = lambda i=I, line=1, **k: dict({'importer': i, 'importer_blob': blob(pi, i), 'importer_commit': P, 'line': line}, **k)
    face = {'module': 'util', 'names': ['VALUE', 'f']}
    mk = lambda p=H, calls=None, interface=face: {
        'path': p, 'input_revision': P, 'source_blob': blob(pi, p), 'kind': PY_IMPORT_KIND, 'command': ['python3', '-B', (calls or [call()])[0]['importer']],
        'interface': interface, 'provenance': {'commit': P, 'path': p, 'blob': blob(pi, p)}, 'imports': calls or [call(), call('tests/pi/run2.py')],
        'purpose': 'Synthetic helper.'}
    role = mk(); base_model, base = run(pl, standalone=roots)
    assert base[H]['class'] != 'keep' and base[I]['class'] == 'keep'
    saved = PY_IMPORT_HELPERS, PY_IMPORT_IMPORTS
    PY_IMPORT_HELPERS = frozenset({(p, blob(pi, p), P) for p in (H, 'tests/pi/deep.py', 'tests/pj/json.py')})
    PY_IMPORT_IMPORTS = frozenset({(H, blob(pi, H), i, blob(pi, i), P, n) for i, n in ((I, 1), ('tests/pi/run2.py', 1), ('tests/pi/path.py', 3),
                                   ('tests/pi/lib.py', 2), ('tests/pi/unbound.py', 1))}
                                  | {('tests/pi/deep.py', blob(pi, 'tests/pi/deep.py'), H, blob(pi, H), P, 4),
                                     ('tests/pj/json.py', blob(pi, 'tests/pj/json.py'), 'tests/pj/run.py', blob(pi, 'tests/pj/run.py'), P, 1)})
    try:
        for repo in (pi, pl):
            for order in (1, -1):  # dispatched after every other definition, in either order
                model, rows = run(repo, standalone=([role] + roots)[::order]); entry = model['entry_points'][PY_IMPORT_PREFIX + H]
                assert rows[H]['class'] == 'keep' and entry['source_only'] and entry['python_import_role'] and entry['interface'] == face
                assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['location'] == I + ':1'
                assert entry['command'] == 'python3 -B ' + I and entry['imports'] == role['imports'] and entry['provenance'] == role['provenance']
            if repo is pl:  # no import, execution, read, child or runtime credit beyond the helper itself
                assert rows['tests/pi/deep.py']['class'] != 'keep'
                assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != H)
                assert set(model['entry_points']) == set(base_model['entry_points']) | {PY_IMPORT_PREFIX + H}
        Z = '0' * 40
        for change, text in (({'extra': 1}, 'invalid Python import'), ({'purpose': ' '}, 'invalid Python import'), ({'imports': []}, 'invalid Python import'),
                             ({'imports': [call(), call()]}, 'invalid Python import'), ({'imports': [call(line='1')]}, 'invalid Python import'),
                             ({'imports': [call(extra=1)]}, 'invalid Python import'), ({'provenance': {'commit': P}}, 'invalid Python import'),
                             ({'input_revision': 'HEAD'}, 'full commit revision'), ({'command': ['python3', I]}, 'unsupported Python import role invocation'),
                             ({'command': ['python3', '-B', H]}, 'unsupported Python import role invocation'),
                             ({'source_blob': Z}, 'unreviewed Python import role'), ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed Python import role'),
                             ({'imports': [call(line=2)]}, 'unreviewed Python import role import'), ({'imports': [call(importer_blob=Z)]}, 'role import'),
                             ({'imports': [call(importer_commit=Z)]}, 'role import'), ({'interface': dict(face, names=['f'])}, 'Python import role interface mismatch'),
                             ({'interface': {'module': 'util', 'names': ['VALUE', 'f'], 'x': 1}}, 'interface mismatch'), ({'input_revision': Z}, 'unverifiable historical')):
            rejected(pi, text, standalone=[dict(role, **change)] + roots)
        rejected(pi, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')] + roots)
        for i, n, text in (('tests/pi/path.py', 3, 'not an exact sibling import'), ('tests/pi/lib.py', 2, 'not an exact sibling import'),
                           ('tests/pi/unbound.py', 1, 'imports an unbound helper name')):
            rejected(pi, text, standalone=[mk(calls=[call(i, n)])] + roots + [importer(i)])
        rejected(pi, 'not an exact sibling import', standalone=[mk('tests/pj/json.py', [call('tests/pj/run.py')], {'module': 'json', 'names': []}),
                                                                importer('tests/pj/run.py')])
        # Importers must be current python3 -B entry roots, never another import role.
        rejected(pi, 'not a python3 -B entry root', standalone=[role])
        rejected(pi, 'not a python3 -B entry root', standalone=[role, roots[0]])
        rejected(pi, 'not a python3 -B entry root', standalone=[role, mk('tests/pi/deep.py', [call(H, 4)], {'module': 'deep', 'names': ['X']})] + roots)
        assert PY_IMPORT_PREFIX + H not in run(pl, standalone=[role])[0]['entry_points']  # later: missing importer root is stale
        PY_IMPORT_IMPORTS = PY_IMPORT_IMPORTS | {(H, blob(pi, H), I, blob(pi, I), env['A'], 1)}
        rejected(pi, 'importer lacks its introducing provenance', standalone=[mk(calls=[call(importer_commit=env['A'])])] + roots)
        for order in (1, -1):  # a current definition supersedes
            model, _ = run(pl, standalone=[dict(role, input_revision=pl.ref, purpose='Now.'), role][::order] + roots)
            assert model['entry_points'][PY_IMPORT_PREFIX + H]['purpose'] == 'Now.'
        PY_IMPORT_HELPERS = saved[0]  # the audited set admits no other helper
        rejected(pi, 'unreviewed Python import role', standalone=[role] + roots)
        PY_IMPORT_HELPERS = frozenset({(H, blob(pi, H), P)})
        # A changed helper or importer, a shadowing extension module, package or cached
        # module drops the root later; a current claim on changed or shadowed bytes is refused.
        for changes in ({H: helper}, {I: '# edited\n' + ok}, {'tests/pi/util.abi3.so': 'x'}, {'tests/pi/util/__init__.py': ''},
                       {'tests/pi/__pycache__/util.cpython-312.pyc': 'x'}):
            edited = commit(changes, 'edited')
            model, rows = run(edited, standalone=[role, roots[1], importer(I, edited)])
            assert PY_IMPORT_PREFIX + H not in model['entry_points'] and rows[H]['class'] != 'keep', changes
            current = dict(role, input_revision=edited.ref)
            rejected(edited, 'source mismatch' if H in changes or I in changes else 'helper is shadowed', standalone=[current, roots[1], importer(I, edited)])
            for path in changes: (env['root'] / path).unlink()
            commit({H: add[H], I: ok, 'tests/unrelated.txt': 'restored %d\n' % len(path)}, 'restored')
    finally: PY_IMPORT_HELPERS, PY_IMPORT_IMPORTS = saved


DOC_REF_KIND = 'documentation-reference-role'
DOC_REF_PREFIX = 'doc-ref:'
# H1050 (gh#1365, X1E-REFERENCE-POLICY-OWNER, Option A), H966 reference role:
# a tracked Markdown document read by the documentation navigation check,
# which the fast checks table runs and gate.sh invokes. Documents (path, blob,
# introducing commit) and readers (path, blob, read line), reviewed one by one
# from x1e-classify-h28-h55's list. Refused, left unresolved:
# tests/h28-sol/mutation-testing/inventory.extended.errata.json (no reader on
# master). Reference role only: no test, fixture, proof or runtime credit.
REVIEWED_DOC_REFERENCES = _review_table('''
@05b3f3f3a0bbb708eb00e86025811aee3eee15b3
T:h28-sol/type-grammar/README.md e1a46f542832fa31f92f635162c480c2d39f4467
@5cf5fe5fe942a8a867a8c1d5c858d9360d782560
T:h28-terra/drift-reports/README.md 8c54e1c7e52a83c7adcaa030fafb025dc1584ca4
@67715897e4bdb8b83331bba8f2079d35a5a8e04c
T:h28-sol/automation-benchmark/README.md 563c3d605d8a16c89f7d5575940d8f4d88a488e6
@db525b4aac99bbd4449fb21bd232b5039f78606f
T:h28-sol/mutation-testing/tools/README.md 27e517d407f7d486547d742dee384b071a1ee0de
''')
REVIEWED_DOC_READERS = frozenset({('scripts/check-doc-navigation.py', '956ac0e78a2ce9622e1f205887a852dfa27b2b92', 138)})
DOC_NAV_COMMAND = ['python3', 'scripts/check-doc-navigation.py']
DOC_NAV_READ = '    graph = {p: set(links(p, (ROOT / p).read_text(), paths)) for p in paths}'
DOC_NAV_DOCUMENTS = ("    output = subprocess.check_output(\n        ['git', 'ls-files', '-z', '--', '*.md'], cwd=ROOT\n    ).decode()\n"
                     "    return {p for p in output.split('\\0') if p and (ROOT / p).is_file()} | {CATALOG}\n")
DOC_NAV_CATALOG = 'docs/document-index.md'
DOC_NAV_TABLE = ('scripts/ci/checks-fast.sh', "checks=$(cat <<'EOF'", 'EOF', 'doc-navigation\tpython3 scripts/check-doc-navigation.py',
                 "while IFS=$'\\t' read -r name cmd; do")
DOC_NAV_GATE = ('scripts/coord-tools/gate.sh', '  run_gate checks-fast bash scripts/ci/checks-fast.sh')


def doc_navigation_invoked(repo):
    """gate.sh runs the fast checks, whose name<TAB>command table names the
    navigation check on one exact row inside its here-document."""
    path, start, end, row, loop = DOC_NAV_TABLE
    lines = repo.texts.get(path, '').splitlines()
    if start not in lines or loop not in lines or DOC_NAV_GATE[1] not in repo.texts.get(DOC_NAV_GATE[0], '').splitlines(): return False
    body = lines[lines.index(start) + 1:]
    if end not in body: return False
    return body[:body.index(end)].count(row) == 1


def documentation_reference_root(classifier, graph, catalog, entry, reviewed=None, readers=None):
    """H1050/H966: a reviewed tracked Markdown document read by the documentation navigation check.

    Binds the document (path, blob, introducing commit), the reader (path,
    blob, read line, all reviewed) and DOC_NAV_COMMAND. At the measured
    revision the reader enumerates `git ls-files -- '*.md'` and reads each
    file on its exact read line, the catalog links the document, and gate.sh runs the
    fast checks table whose row runs the reader. A changed reader or a missing
    link or invocation makes it stale. Never a validated runner; anchors
    nothing. Reference credit only: no test, fixture, proof or runtime credit.
    Not audited: the reader reaches its read line only when the whole catalog
    equals its own render of the tree; this role checks the document's link
    line, not catalog freshness (the gate runs the reader on every merge).
    """
    repo = graph.repo; role = 'documentation reference role'
    reviewed = REVIEWED_DOC_REFERENCES if reviewed is None else reviewed
    readers = REVIEWED_DOC_READERS if readers is None else readers
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'reader', 'purpose'}
    _role_schema(classifier, catalog, entry, required, role); reader = entry['reader']
    if (not isinstance(reader, dict) or set(reader) != {'path', 'blob', 'line'} or type(reader['line']) is not int
            or not all(isinstance(reader[k], str) for k in ('path', 'blob'))):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if not p.endswith('.md') or _clean(p) != p or entry['command'] != DOC_NAV_COMMAND or entry['interface'] != {'catalog': DOC_NAV_CATALOG}:
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed ' + role + ': ' + p)
    if (reader['path'], reader['blob'], reader['line']) not in readers: raise ValueError('unreviewed ' + role + ' reader: ' + p)
    if not _role_current(classifier, repo, catalog, entry, [(p, blob)]): return
    if repo.tree[p][0] != '100644' or p not in repo.texts: raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    text = repo.texts.get(reader['path']) if _current(repo, reader['path'], reader['blob']) else None
    if text is None or reader['line'] > len(text.splitlines()) or text.splitlines()[reader['line'] - 1] != DOC_NAV_READ: return
    if DOC_NAV_DOCUMENTS not in text or "CATALOG = '" + DOC_NAV_CATALOG + "'" not in text.splitlines(): return
    link = '- [' + p + '](../' + p + ')'
    if link not in repo.texts.get(DOC_NAV_CATALOG, '').splitlines() or not doc_navigation_invoked(repo): return
    identity = DOC_REF_PREFIX + p
    graph.root(p, 'documentation reference', shlex.join(DOC_NAV_COMMAND), reader['path'], reader['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'documentation_reference_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': entry['interface'], 'provenance': doc, 'reader': reader, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': DOC_NAV_COMMAND,
            'reason': 'Reviewed Markdown document read by the documentation navigation check that the fast checks run; the check is not run or certified to pass here. Reference role only: no test, fixture, proof or runtime credit.'}})


def documentation_reference_controls(env):
    """(11) H1050 controls, run by successor_controls with its helpers: the
    reviewed documents, the reader and invocation bindings, the role and its
    negative controls."""
    global REVIEWED_DOC_REFERENCES, REVIEWED_DOC_READERS
    commit, run, rejected, blob, gate = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'gate'))
    # The audited witnesses: four H28 READMEs; the errata JSON (no reader) is refused.
    paths = {p for p, _, _ in REVIEWED_DOC_REFERENCES}
    assert len(REVIEWED_DOC_REFERENCES) == len(paths) == 4 and all(p.startswith('tests/h28-') and p.endswith('/README.md') for p in paths)
    assert 'tests/h28-sol/mutation-testing/inventory.extended.errata.json' not in paths and len(REVIEWED_DOC_READERS) == 1
    D = 'tests/doc/README.md'; N = 'scripts/check-doc-navigation.py'
    reader = ("import subprocess\nfrom pathlib import Path\nROOT = Path(__file__).resolve().parent.parent\nCATALOG = 'docs/document-index.md'\n\n\n"
              "def documents():\n" + DOC_NAV_DOCUMENTS + "\n\ndef main():\n    paths = documents()\n" + DOC_NAV_READ + "\n")
    rl = reader.splitlines().index(DOC_NAV_READ) + 1
    table = ("#!/usr/bin/env bash\nchecks=$(cat <<'EOF'\nother\tpython3 x.py\n" + DOC_NAV_TABLE[3] + "\nEOF\n)\n"
             + DOC_NAV_TABLE[4] + "\n  bash -c \"$cmd\"\ndone <<< \"$checks\"\n")
    catalog = '# Catalog\n- [' + D + '](../' + D + ')\n'
    add = {D: '# Doc\n', 'tests/doc/other.md': '# Other\n', N: reader, DOC_NAV_TABLE[0]: table, DOC_NAV_CATALOG: catalog,
           DOC_NAV_GATE[0]: gate + DOC_NAV_GATE[1] + '\n'}
    dr = commit(add, 'documentation references'); R = dr.ref; dl = commit({'tests/unrelated.txt': 'D\n'}, 'documentation later')
    mk = lambda p=D, **k: dict({'path': p, 'input_revision': R, 'source_blob': blob(dr, p), 'kind': DOC_REF_KIND, 'command': DOC_NAV_COMMAND,
        'interface': {'catalog': DOC_NAV_CATALOG}, 'provenance': {'commit': R, 'path': p, 'blob': blob(dr, p)},
        'reader': {'path': N, 'blob': blob(dr, N), 'line': rl}, 'purpose': 'Synthetic document.'}, **k)
    role = mk(); base_model, base = run(dl, standalone=[])
    assert base[D]['class'] != 'keep'
    saved = REVIEWED_DOC_REFERENCES, REVIEWED_DOC_READERS
    REVIEWED_DOC_REFERENCES = frozenset({(p, blob(dr, p), R) for p in (D, 'tests/doc/other.md')})
    REVIEWED_DOC_READERS = frozenset({(N, blob(dr, N), rl)})
    try:
        for repo in (dr, dl):
            model, rows = run(repo, standalone=[role]); entry = model['entry_points'][DOC_REF_PREFIX + D]
            assert rows[D]['class'] == 'keep' and entry['source_only'] and entry['documentation_reference_role'] and entry['reader'] == role['reader']
            assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['location'] == N + ':%d' % rl
            if repo is dl:  # no test, fixture, reader, proof or runtime credit
                assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != D)
                assert set(model['entry_points']) == set(base_model['entry_points']) | {DOC_REF_PREFIX + D}
        Z = '0' * 40
        for change, text in (({'extra': 1}, 'invalid documentation reference'), ({'purpose': ' '}, 'invalid documentation reference'),
                             ({'reader': dict(role['reader'], line=str(rl))}, 'invalid documentation reference'),
                             ({'reader': dict(role['reader'], extra=1)}, 'invalid documentation reference'),
                             ({'input_revision': 'HEAD'}, 'full commit revision'), ({'command': ['python3', '-B', N]}, 'unsupported documentation reference'),
                             ({'interface': {'catalog': 'docs/README.md'}}, 'unsupported documentation reference'),
                             ({'source_blob': Z}, 'unreviewed documentation reference role'),
                             ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed documentation reference role'),
                             ({'reader': dict(role['reader'], line=rl - 1)}, 'role reader'), ({'reader': dict(role['reader'], blob=Z)}, 'role reader'),
                             ({'input_revision': Z}, 'unverifiable historical')):
            rejected(dr, text, standalone=[dict(role, **change)])
        rejected(dr, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')])
        rejected(dr, 'unsupported documentation reference', standalone=[mk(N)])  # not Markdown
        # Reviewed but not linked from the catalog: no root.
        assert DOC_REF_PREFIX + 'tests/doc/other.md' not in run(dr, standalone=[mk('tests/doc/other.md')])[0]['entry_points']
        REVIEWED_DOC_REFERENCES = saved[0]
        rejected(dr, 'unreviewed documentation reference role', standalone=[role])
        REVIEWED_DOC_REFERENCES = frozenset({(D, blob(dr, D), R)})
        for order in (1, -1):  # a current definition supersedes
            model, _ = run(dl, standalone=[dict(role, input_revision=dl.ref, purpose='Now.'), role][::order])
            assert model['entry_points'][DOC_REF_PREFIX + D]['purpose'] == 'Now.'
        # A changed reader, enumeration, catalog, table row, table position, loop or gate line drops the root.
        stale = ({N: reader.replace('(ROOT / p).read_text()', '""')}, {N: reader.replace("'*.md'", "'docs/*.md'")},
                 {DOC_NAV_CATALOG: '# Catalog\n'}, {DOC_NAV_TABLE[0]: table.replace(DOC_NAV_TABLE[3] + '\n', '')},
                 {DOC_NAV_TABLE[0]: table.replace(DOC_NAV_TABLE[3] + '\nEOF\n', 'EOF\n' + DOC_NAV_TABLE[3] + '\n')},
                 {DOC_NAV_TABLE[0]: table.replace(DOC_NAV_TABLE[3], '# ' + DOC_NAV_TABLE[3])},
                 {DOC_NAV_TABLE[0]: table.replace(DOC_NAV_TABLE[3], DOC_NAV_TABLE[3] + '\n' + DOC_NAV_TABLE[3])},
                 {DOC_NAV_TABLE[0]: table.replace(DOC_NAV_TABLE[4], 'while read -r name cmd; do')},
                 {DOC_NAV_GATE[0]: gate}, {D: '# Changed\n'})
        # Even a reviewed reader blob grants nothing without the exact read line, enumeration and catalog name.
        for variant in (reader.replace('(ROOT / p).read_text()', '""'), reader.replace("'*.md'", "'docs/*.md'"),
                        reader.replace("CATALOG = 'docs/document-index.md'", "CATALOG = 'docs/index.md'")):
            edited = commit({N: variant}, 'reviewed variant')
            REVIEWED_DOC_READERS = frozenset({(N, blob(edited, N), rl)})
            model, rows = run(edited, standalone=[dict(role, reader=dict(role['reader'], blob=blob(edited, N)))])
            assert DOC_REF_PREFIX + D not in model['entry_points'] and rows[D]['class'] != 'keep', variant
            commit({N: reader}, 'restored')
        REVIEWED_DOC_READERS = frozenset({(N, blob(dr, N), rl)})
        for changes in stale:
            edited = commit(changes, 'edited')
            model, rows = run(edited, standalone=[role])
            assert DOC_REF_PREFIX + D not in model['entry_points'] and rows[D]['class'] != 'keep', changes
            if D in changes: rejected(edited, 'source mismatch', standalone=[dict(role, input_revision=edited.ref)])
            commit({k: add[k] for k in changes}, 'restored')
    finally: REVIEWED_DOC_REFERENCES, REVIEWED_DOC_READERS = saved


# H1009 (gh#1350, X1E-NONPASSING-READ-PERSISTENCE, Option B): the persistence
# form of nonpassing reads (QX1E-NONPASS uses the same rule). A
# consumer_routes.persistent_reads row may carry an ordinary nonpassing read
# (runner nonpassing:P, NONPASS_READ_OPERATION, frames with code identity)
# recorded at the revision of P's nonpassing-unittest definition. At a later
# --ref it credits that one read while P's definition blob, every frame and the
# target are the same blobs now and at that revision, P is a declared unittest
# runner and a frame of P lies in an entered test or setup context. Runners are
# reviewed case by case (path, blob, commit that introduced that blob at P).
# The run failed: the root is source-only, never validated or passing, and
# anchors nothing; only the named in-scope target is credited (consumption):
# recorded helper frames are provenance only, never credited.
# Reviewed: the 11 nonpassing-unittest runners of check-tests-used-routes.json
# whose recorded blob is live at 6ace6ff4. Refused, left unresolved:
# tests/h62/item1/pin-fragments/probe.py (blob 65bb252c changed to 4479dfaa).
NONPASS_READ_OPERATION = 'Observed fixture read during nonpassing unittest'
PERSISTED_NONPASS_OPERATION = 'blob-bound persisted fixture read observed during a failed unittest run'
NONPASS_PERSIST_PREFIX = 'nonpassing-persisted:'
REVIEWED_NONPASS_PERSISTENCE = _review_table('''
@99252640c3531e36b5de3eac0aac4ee71fa50a32
H:item1/packet-panic/test_mul_proposal.py c15efd3896a87de0264cb94adaa906a713f70f34
@77913ac1cff1147d1129caea943c881b4aa61ec7
D:shared-translator/validation-input-controls.py a351764a4447049ec8a2d52e6e73993753d89b2e
@6ebe96b19a37cc1de816b7322d8aa4638568e1ee
T:h55/vectors-tables/test_fixture_controls.py 05d3cf96943793d1961afafc3b5d16dac82fd362
@880f5fb630eedf12f582aa2b8ba9ba92250c636f
T:h55/vectors-tables/test_table_proposals.py 0991231c4b170fadd64029edcba4a71284a04a74
@b632012265807642cf690e15aed0d3dc753b96d8
T:h62/item2/audit-bytecode-selection/test_inventory_report.py 05f260b9f57a57caff8fb2250e87dcc2bc4f74d8
@49b10df66755e2501962470b69f744ea291f54e6
T:h62/item4/generic-memorycopies/test_semantic_groups.py 6337febfe539ddbb97480f9f60499209a3102abf
@c9df585f9c78134adc2f14ff383925d207502679
T:h62/item6/migrate-evm/test_census.py 9f93078e0455433b5b6fccd327ed3a4b3b1b83df
@03024461482e758b24f0c2376c6b166513a71665
T:roadmap-v15-bounded-observe.py 4453c7b8e54ae381b397803a703172753c078108
@f18f3815ea0c718dc06b5381149802596eb14c9f
T:roadmap-v17/test_evidence.py 1afb5c3f29e957ed58a9defc7952b8b21687c7be
@036114cb851f637298cf1ed8410a0ba0f7333389
T:roadmap-v17/test_verify_compacted.py 28c0268375f47d7cec8be2582ad327b48e7280a1
@d92c074c0c90f2bf4936b5c63f3bc439d6116812
T:yul-composition/plan-approx-generator-test.py edb153f609028cf4f9193c9fc680e3788a227e1f
''')


def persisted_nonpassing_read(classifier, graph, catalog, row, reviewed=None):
    """H1009: one persisted nonpassing read (see the comment above). A changed or
    missing object or a superseding current definition of P grants nothing; a
    row whose objects match but whose form does not hold is rejected."""
    repo = graph.repo
    reviewed = REVIEWED_NONPASS_PERSISTENCE if reviewed is None else reviewed
    runner, revision, target, frames = row['runner'], row['input_revision'], row['target'], row['frames']
    if not isinstance(runner, str) or not runner.startswith('nonpassing:'): raise ValueError('persisted nonpassing read needs a nonpassing runner')
    p = runner[len('nonpassing:'):]
    definitions = [e for e in catalog['standalone'] if e.get('path') == p and e.get('input_revision') == revision]
    definition = definitions[0] if len(definitions) == 1 else {}
    scopes = definition.get('input_scope')
    if (definition.get('kind') != 'nonpassing-unittest' or definition.get('command') != ['python3', '-B', p]
            or not isinstance(definition.get('source_blob'), str) or not isinstance(definition.get('purpose'), str)
            or not definition['purpose'].strip() or not isinstance(scopes, list) or not all(isinstance(s, str) for s in scopes)):
        raise ValueError('persisted nonpassing read lacks its nonpassing runner definition')
    blob = definition['source_blob']
    commits = sorted(c for q, b, c in reviewed if q == p and b == blob)
    if len(commits) != 1: raise ValueError('unreviewed nonpassing read persistence: ' + p)
    if not isinstance(target, str) or not isinstance(row['target_blob'], str): raise ValueError('invalid persisted read target')
    if not isinstance(frames, list) or not frames or any(
            not isinstance(f, dict) or set(f) != {'path', 'blob', 'line', 'code_qualname', 'code_firstlineno'}
            or not isinstance(f['path'], str) or not isinstance(f['blob'], str) or type(f['line']) is not int
            or not isinstance(f['code_qualname'], str) or type(f['code_firstlineno']) is not int or f['code_firstlineno'] < 1 for f in frames):
        raise ValueError('invalid persisted nonpassing frame')
    if frames[0]['path'] != p: raise ValueError('persisted read does not start at its runner')
    if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return
    pins = sorted({(f['path'], f['blob']) for f in frames} | {(p, blob), (target, row['target_blob'])})
    if not all(_current(repo, q, b) for q, b in pins): return
    _check_lines(repo, frames)
    if not _historical_objects(classifier, repo, revision, pins):
        raise ValueError('persisted route objects differ at recorded revision ' + revision)
    if not _introduced(classifier, repo, commits[0], p, blob): raise ValueError('persisted nonpassing runner lacks its introducing provenance: ' + p)
    declaration = classifier['declared_unittest'](repo, p)
    if declaration is None: raise ValueError('nonpassing source is not a declared unittest runner')
    if not any(f['path'] == p and any(c['first'] <= f['line'] <= c['last'] and c['qualname'] == f['code_qualname']
               and c['code_firstlineno'] == f['code_firstlineno'] for c in declaration['test_contexts']) for f in frames):
        raise ValueError('nonpassing read lacks an entered test or setup context')
    if not all(v not in classifier['SCOPE'] and (v in repo.tree or v.endswith('/') and any(q.startswith(v) for q in repo.tree)) for v in scopes):
        raise ValueError('nonpassing test lacks reviewed fixture scope')
    if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): return
    identity = NONPASS_PERSIST_PREFIX + p
    if not any(target == s or s.endswith('/') and target.startswith(s) for s in scopes):
        graph.uncertain_reads[target].add(identity); return
    graph.root(p, 'persisted nonpassing unittest runner source', shlex.join(['python3', '-B', p]), p, declaration['main_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'source_blob': blob, 'role_provenance': declaration, 'other_reads': 'unresolved',
        'provenance': {'commit': commits[0], 'path': p, 'blob': blob},
        'validation_at_measured_revision': {'status': 'unavailable', 'command': ['python3', '-B', p],
            'reason': 'Normal run failed at each recorded revision and is not run here. Persisted test-context reads only; no execution, pass, helper, child, output, proof or runtime credit.'}})
    details = {'kind': 'persisted-nonpassing-read', 'observed_revision': revision, 'validation_at_observed_revision': 'failed',
               'runner_definition_blob': blob, 'purpose': definition['purpose']}
    # Only the named target is credited: the recorded frames stay in the chain
    # as provenance but no frame (helper or data) is observed or credited.
    derived = identity + ':' + details['kind'] + ':' + hashlib.sha256(canonical(row)).hexdigest()
    graph.roots[derived] = {**graph.roots[identity], 'derived_from': identity, 'observed_target': target, 'consumer_route': details}
    edges = [{'source': a['path'], 'target': b['path'], 'line': a['line'], 'operation': 'Recorded nonpassing unittest call stack (persisted; no credit)',
              'kind': 'executes', 'validated_for': derived} for a, b in zip(frames, frames[1:])]
    edges.append({'source': frames[-1]['path'], 'target': target, 'line': frames[-1]['line'], 'operation': PERSISTED_NONPASS_OPERATION,
                  'kind': 'consumes', 'validated_for': derived})
    graph.observed.append((target, {'root': derived, 'entry': graph.roots[derived], 'edges': edges}))


def nonpassing_persistence_controls(env):
    """(12) H1009 controls, run by successor_controls with its helpers."""
    global REVIEWED_NONPASS_PERSISTENCE
    commit, run, rejected, blob, route = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'route'))
    paths = {p for p, _, _ in REVIEWED_NONPASS_PERSISTENCE}
    assert len(REVIEWED_NONPASS_PERSISTENCE) == len(paths) == 11 and 'tests/h62/item1/pin-fragments/probe.py' not in paths
    P = 'tests/np_test.py'; D = 'tests/np-data.txt'; O = 'tests/np-other.txt'
    text = ("import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  open('tests/np-data.txt').read()\n"
            "  open('tests/np-other.txt').read()\n  self.fail('nonpassing')\nif __name__ == '__main__': unittest.main()\n")
    H = 'tests/np_helper.py'
    add = {P: text, D: 'np data\n', O: 'np other\n', H: 'def load(p):\n    return open(p).read()\n'}
    nc = commit(add, 'nonpassing'); N = nc.ref; nl = commit({'tests/unrelated.txt': 'N\n'}, 'nonpassing later')
    defn = {'path': P, 'input_revision': N, 'source_blob': blob(nc, P), 'command': ['python3', '-B', P], 'kind': 'nonpassing-unittest',
            'purpose': 'Synthetic failing test.', 'input_scope': [D]}
    fr = lambda line=4, qual='T.test_it', first=3, repo=nc: {'path': P, 'blob': blob(repo, P), 'line': line, 'code_qualname': qual, 'code_firstlineno': first}
    row = lambda target=D, frames=None, **k: dict({'runner': 'nonpassing:' + P, 'input_revision': N, 'frames': frames or [fr(7, '<module>', 1), fr()],
        'target': target, 'target_blob': blob(nc, target), 'operation': NONPASS_READ_OPERATION}, **k)
    reads = lambda *rows: {'persistent_reads': list(rows)}
    base_model, base = run(nl, standalone=[defn])
    assert base[D]['class'] != 'keep' and NONPASS_PERSIST_PREFIX + P not in base_model['entry_points']
    saved = REVIEWED_NONPASS_PERSISTENCE
    REVIEWED_NONPASS_PERSISTENCE = frozenset({(P, blob(nc, P), N)})
    try:
        model, rows = run(nl, reads(row()), standalone=[defn]); entry = model['entry_points'][NONPASS_PERSIST_PREFIX + P]
        chain = rows[D]['runner_chain']
        assert rows[D]['class'] == 'keep' and chain['entry']['consumer_route']['kind'] == 'persisted-nonpassing-read'
        assert chain['entry']['consumer_route']['validation_at_observed_revision'] == 'failed' and chain['edges'][-1]['operation'] == PERSISTED_NONPASS_OPERATION
        assert entry['source_only'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
        assert 'validated:' + P not in model['entry_points'] and 'nonpassing:' + P not in model['entry_points']
        assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p not in (D, P))  # one read, no other credit
        # At its own revision the row is the ordinary failed-run read.
        model, rows = run(nc, reads(row()), standalone=[defn])
        assert rows[D]['class'] == 'keep' and rows[D]['runner_chain']['entry']['validation_at_measured_revision']['status'] == 'failed'
        # Out of the reviewed scope: an unreviewed read, never keep, and no root.
        model, rows = run(nl, reads(row(O, [fr(7, '<module>', 1), fr(5)])), standalone=[defn])
        assert rows[O]['class'] is None and 'unreviewed_readers' in rows[O]['secondary']
        assert NONPASS_PERSIST_PREFIX + P not in model['entry_points']
        # Recorded helper or data frames are provenance only: never credited.
        for extra in ({'path': H, 'blob': blob(nc, H), 'line': 2, 'code_qualname': 'load', 'code_firstlineno': 1},
                      {'path': O, 'blob': blob(nc, O), 'line': 1, 'code_qualname': 'x', 'code_firstlineno': 1}):
            _, rows = run(nl, reads(row(frames=[fr(7, '<module>', 1), fr(), extra])), standalone=[defn])
            assert rows[D]['class'] == 'keep' and canonical(rows[extra['path']]) == canonical(base[extra['path']]), extra['path']
        # A broad or missing scope in the historical definition is refused.
        for scope in (['tests/'], ['tests/missing.txt']):
            rejected(nl, 'reviewed fixture scope', reads(row(O, [fr(7, '<module>', 1), fr(5)])), standalone=[dict(defn, input_scope=scope)])
        # The failed-run root anchors nothing.
        anchored = route(nc, NONPASS_PERSIST_PREFIX + P, 'node-readFileSync', [{'path': P, 'blob': blob(nc, P), 'line': 4}], O)
        assert run(nl, dict(reads(row()), static_routes=[anchored]), standalone=[defn])[1][O]['class'] != 'keep'
        Z = '0' * 40
        for bad, message in ((row(operation='validated Python read of measured bytes'), 'needs a validated runner'),
                             (row(runner='validated:' + P, operation=NONPASS_READ_OPERATION), 'needs a nonpassing runner'),
                             (row(input_revision=Z), 'lacks its nonpassing runner definition'),
                             (row(frames=[{k: v for k, v in fr().items() if k != 'code_qualname'}]), 'invalid persisted nonpassing frame'),
                             (row(frames=[fr(first=0)]), 'invalid persisted nonpassing frame'),
                             (row(frames=[fr(7, '<module>', 1)]), 'entered test or setup context'),
                             (row(frames=[fr(qual='T.test_other')]), 'entered test or setup context'),
                             (row(frames=[fr(first=2)]), 'entered test or setup context'),
                             (row(frames=[fr(99)]), 'location mismatch'),
                             (row(frames=[dict(fr(), path='tests/unrelated.txt', blob=blob(nl, 'tests/unrelated.txt'))]), 'does not start at its runner'),
                             (row(target_blob=None), 'invalid persisted read target')):
            rejected(nl, message, reads(bad), standalone=[defn])
        for change, message in (({'kind': 'unittest', 'other_reads': 'unresolved'}, 'nonpassing runner definition'), ({'command': ['python3', P]}, 'nonpassing runner definition'),
                                ({'purpose': ' '}, 'nonpassing runner definition'), ({'input_scope': None}, 'nonpassing runner definition')):
            rejected(nl, message, reads(row()), standalone=[dict(defn, **change)])
        # A row naming objects that were never together at the recorded revision.
        later_data = commit({D: 'np changed\n'}, 'changed data')
        forged = dict(row(), target_blob=blob(later_data, D))
        rejected(later_data, 'objects differ at recorded revision', reads(forged), standalone=[defn])
        restored = commit({D: add[D]}, 'restored data')
        REVIEWED_NONPASS_PERSISTENCE = frozenset({(P, blob(nc, P), nl.ref)})
        rejected(restored, 'introducing provenance', reads(row()), standalone=[defn])
        REVIEWED_NONPASS_PERSISTENCE = frozenset({(P, Z, N)})
        rejected(restored, 'unreviewed nonpassing read persistence', reads(row()), standalone=[defn])
        REVIEWED_NONPASS_PERSISTENCE = saved
        rejected(restored, 'unreviewed nonpassing read persistence', reads(row()), standalone=[defn])
        REVIEWED_NONPASS_PERSISTENCE = frozenset({(P, blob(nc, P), N)})
        assert run(restored, reads(row()), standalone=[defn])[1][D]['class'] == 'keep'
        # Stale objects grant nothing; a current definition of P supersedes.
        for changes in ({D: 'np changed\n'}, {P: text + '# changed\n'}):
            edited = commit(changes, 'edited')
            model, rows = run(edited, reads(row()), standalone=[defn])
            assert rows[D]['class'] != 'keep' and NONPASS_PERSIST_PREFIX + P not in model['entry_points'], changes
            commit({k: add[k] for k in changes}, 'restored')
        current = dict(defn, input_revision=restored.ref)
        model, rows = run(restored, reads(row()), standalone=[defn, current])
        assert rows[D]['class'] != 'keep' and NONPASS_PERSIST_PREFIX + P not in model['entry_points']
    finally: REVIEWED_NONPASS_PERSISTENCE = saved
