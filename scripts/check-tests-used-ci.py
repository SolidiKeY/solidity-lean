"""Reviewed CI use recipes, bound to complete committed source blobs.

These recipes are manual source audits, not lexical mention classifiers. Each
route records the call that actually reaches a reader. Named manifest members
are validated independently; no whole-directory keep rule is used. Source drift
invalidates the recipe and requires review. No runner executes from this module.
"""
import hashlib
import json
import posixpath
import re

AUDITED = {'.github/workflows/editor-parity.yml': 'bff550f3fa4ae04972f9be9193142f6eca238755',
 '.github/workflows/lean.yml': '0a5f66b11664079ce46781d63119c6c4a201e4af',
 '.github/workflows/pages.yml': 'da4e027df7c1c68cfe6932b802ec09e9a086657a',
 'scripts/aggregates.test.mjs': 'a768f5e74ba9d9f10a41d5fc7440bb11c7fccb4b',
 'scripts/declarations-metadata.test.mjs': '46f3d4d1c09ee9b3f1c46eb17f30766414f5513d',
 'scripts/solc-ast.mjs': 'df8c4edb8e654038a9a916d97229de75ad5d6e4a',
 'scripts/solidity-lean.test.mjs': 'f636f487eadf4a1f3389a7f9a99379fa73c7d87d',
 'scripts/solkey-migration.mjs': '5c0be020a4ca26cbdab46bf24850f7ef085cb6b2',
 'scripts/test-compiler.mjs': '72f956c7eb9ab68c8f5f85dff5788b6687886c1a',
 'scripts/test-solidity.mjs': 'b0c71c0b438aa38b19384fbf3e8920132dc4e172',
 'scripts/test-solidity.test.mjs': '15c0f09962ec59de89ccc355eeff93c7fbfc2817',
 'scripts/tool-job.mjs': 'b4cbb7b75cd41c9fc01ae2bb5336beac7482a8ca',
 'tests/h62/item5/statement-graph/h112-tooling.test.mjs': 'ebf5bf9921b591d697cf9cfcdb0ea6f6c526505c',
 'tests/h62/item5/statement-graph/test_w0_tooling.py': 'ab4358ad36ca3e7426bf328334ff0b52882ac648',
 'vscode/parity/stdio.cjs': '8dde283ddd2f47ec606b248e91cf18d08058e984',
 'vscode/parity/workloads.cjs': '4f68cf7b780140ca58e7a0c4374a27e1e5eae72e',
 'web/test/website.cjs': '6e3c4d1537a9e3454284e68e1c1528425d33916e'}

AUDITED.update({'scripts/preconditions.test.mjs': 'f535ed435c25f271dd5aecd1bf47fdef8423730d', 'scripts/finite-spec-sets.test.mjs': '4f5c59221a2faf88b244de6e19e5f02386bec128', 'scripts/counterexamples.test.mjs': 'd56092b2d3b2b2f3ea03079cc2ca71fa6978cb6c', 'scripts/lex-metrics.test.mjs': '7863106bf02ba5a3f59d05c435a656a2eea4ba95', 'scripts/source-shadowing.test.mjs': 'f77fe036ec0757372891c423dd23816dac69efb3', 'scripts/spec-hygiene.test.mjs': '61f93c59bbe0dba313552ef8ad5fbc8fe68f4b5b', 'scripts/filtered-spec-sets.test.mjs': 'dee22d06271b51db7c6f111f15037e23313bc02c'})

def add(graph):
    repo = graph.repo
    lean_workflow = '.github/workflows/lean.yml'
    def approved(paths):
        if not all(p in repo.tree for p in paths): return False
        bad = [p for p in paths if repo.tree[p][2] != AUDITED.get(p)]
        if bad:
            graph.notes.append('UNREVIEWED_SOURCE: CI recipe source changed: ' + ', '.join(sorted(bad)))
            return False
        return True
    def ci(source, workflow, line, identity, **details):
        command = repo.texts[workflow].splitlines()[line - 1].strip()
        if command.startswith('run:'): command = command[4:].strip()
        graph.root(source, 'CI', command, workflow, line, root_id=identity)
        graph.roots[identity].update({'cwd': '.', **details})
        if workflow == lean_workflow and line == 188:
            graph.roots[identity]['environment_paths_relative_to_checkout'] = {
                'SOLKEY_ROOT': 'tests/migration/solkey',
                'SOLJSON_DIR': 'tests/migration/solkey/keyext.solidity.core/build/soljson',
                'LEAN_NUM_THREADS': '1'}
    def edge(source, target, line, operation, context, executes=False):
        graph.edge(source, target, line, operation, validated_for=context,
                   kind='executes' if executes else 'consumes')

    test = 'scripts/test-solidity.test.mjs'
    compiler = 'scripts/test-compiler.mjs'
    migration = 'scripts/solkey-migration.mjs'
    runner = 'scripts/test-solidity.mjs'
    if approved([lean_workflow, test, compiler, migration, runner, 'scripts/solc-ast.mjs', 'scripts/tool-job.mjs']):
        context = 'ci:frozen-solkey-snapshot'
        ci(test, lean_workflow, 188, context)
        edge(test, compiler, 12, 'module initializer calls solkeyTestOptions()', context, True)
        edge(compiler, migration, 33, 'solkeyTestOptions calls verifySnapshot(tests/migration/solkey)', context, True)
        manifest_path = 'tests/migration/solkey/snapshot.json'
        pin_path = 'tests/migration/solkey.pin.json'
        edge(migration, manifest_path, 45, 'verifySnapshot reads named snapshot manifest', context)
        edge(migration, pin_path, 46, 'verifySnapshot reads companion integrity pin', context)
        manifest = json.loads(repo.bytes(manifest_path))
        pin = json.loads(repo.bytes(pin_path))
        valid = (manifest.get('version') == 1 and manifest.get('commit') == pin.get('commit') and
                 hashlib.sha256(repo.bytes(manifest_path)).hexdigest() == pin.get('manifestSha256'))
        entries = manifest.get('files', [])
        seen = set(); verified = []
        for entry in entries:
            relative = entry.get('path')
            if not isinstance(relative, str) or relative.startswith('/'):
                valid = False; continue
            path = posixpath.normpath('tests/migration/solkey/' + relative)
            if not path.startswith('tests/migration/solkey/') or path in seen or path not in repo.tree:
                valid = False; continue
            seen.add(path)
            if hashlib.sha256(repo.bytes(path)).hexdigest() != entry.get('sha256'):
                valid = False; continue
            verified.append(path)
        if valid and entries and len(verified) == len(entries):
            for path in sorted(verified):
                edge(migration, path, 56, 'verifySnapshot reads each manifest-named file and verifies its SHA256; measured bytes match', context)
                graph.properties.setdefault(path, {})['frozen_upstream_snapshot'] = {
                    'manifest': manifest_path, 'foreign_commit': manifest['commit']}
        else:
            graph.notes.append('UNVERIFIABLE_INPUT: frozen SolKey snapshot manifest/pin/file consistency failed')
        # Each invocation gets a context so a Runner.sol call cannot be reused
        # to explain ArrayShapes.sol merely because both call the same helper.
        text = repo.texts[test]
        calls = re.finditer(r'runSolidityTests\s*\(\s*\[([^\]]*)\]', text)
        for call in calls:
            start = text.rfind('\n', 0, call.start()) + 1
            prefix = text[start:call.start()].strip()
            if not re.fullmatch(r'(?:const|let)\s+\w+\s*=\s*', prefix): continue
            line = text.count('\n', 0, call.start()) + 1
            for target in re.findall(r'[\x22\x27](tests/[^\x22\x27]+)[\x22\x27]', call[1]):
                if target not in repo.tree: continue
                identity = f'ci:source-call:{line}:{target}'
                ci(test, lean_workflow, 188, identity, selected_call=f'{test}:{line}', source_argument=target)
                edge(test, runner, line, 'runSolidityTests(paths, options), wrapper at lines 14-15 delegates to runSourceTests', identity, True)
                edge(runner, target, 117, 'runSourceTests reads selected source bytes after compilation; source argument bound by selected_call', identity)
        for name in ('SolcArithmeticOpen', 'SolcConstructorsOpen', 'SolcFunctionCallsOpen',
                     'SolcHigherLevelOpen', 'SolcPaymentsOpen', 'SolcSmtControlFlowOpen', 'SolcTypesOpen'):
            target = f'tests/solc/open/{name}.sol'
            identity = 'ci:open-source:' + name
            ci(test, lean_workflow, 188, identity, selected_call=f'{test}:949', source_argument=target)
            edge(test, runner, 952, 'explicit seven-name array maps each name to tests/solc/open/${name}.sol and calls runSolidityTests', identity, True)
            edge(runner, target, 117, 'runSourceTests reads selected source bytes', identity)
        context = 'ci:enum-fixtures'
        ci(test, lean_workflow, 188, context)
        for name, source_line, ast_line in (('EnumDeclarationBounds',1121,1123), ('EnumAbiRanges',1152,1154)):
            edge(test, f'tests/solc/{name}.sol', source_line, 'enum regression directly reads source to check sourceSha256', context)
            for suffix in ('', '-viaIR'):
                edge(test, f'tests/solc/{name}{suffix}.ast.json', ast_line, 'explicit suffix loop reads each pinned enum AST', context)
        for name, line in (('EnumBounds',1133),('EnumAbiRanges',1163),('AbiEntryReplay',1170),('Replay',1172)):
            target = 'tests/upstream/' + name + '.lean'
            identity = 'ci:upstream-lean:' + name
            ci(test, lean_workflow, 188, identity)
            edge(test, runner, line, 'calls imported runTool(lake, --no-build lean FILE -- --tstack=131072)', identity, True)
            edge(runner, 'scripts/tool-job.mjs', 36, 'runTool spawns Node supervisor with checkpoint, timeout, command and arguments; cwd=repository root', identity, True)
            edge('scripts/tool-job.mjs', target, 26, 'supervisor spawns lake --no-build lean ' + target + ' -- --tstack=131072', identity, True)

    for source, ast, sol, ast_line, sol_line in (
        ('scripts/aggregates.test.mjs','Aggregates.ast.json','Aggregates.sol',11,14),
        ('scripts/declarations-metadata.test.mjs','DeclarationMetadata.ast.json','DeclarationMetadata.sol',19,7)):
        if not approved([lean_workflow, source, runner]): continue
        context = 'ci:metadata:' + source
        ci(source, lean_workflow, 188, context)
        edge(source, 'tests/solc/' + ast, ast_line, 'direct readFileSync of pinned AST (URL resolved relative to module for declaration metadata)', context)
        if source.endswith('/aggregates.test.mjs'):
            edge(source, 'tests/solc/' + sol, sol_line, 'direct source read for AST source hash comparison', context)
        else:
            edge(source, runner, sol_line, 'calls runSolidityTests with literal DeclarationMetadata.sol source', context, True)
            edge(runner, 'tests/solc/' + sol, 117, 'runSourceTests reads selected source bytes', context)

    policy = 'scripts/solidity-lean.test.mjs'
    if approved([lean_workflow, policy]):
        context = 'ci:assumption-policy-table'
        ci(policy, lean_workflow, 222, context)
        edge(policy, 'tests/cli/assumption-policies.txt', 111, 'direct readFileSync compared to exhaustive policyTable output', context)

    pages = '.github/workflows/pages.yml'; website = 'web/test/website.cjs'
    if approved([pages, website]):
        for line in (94, 241):
            context = f'ci:browser-proofs:{line}'
            ci(website, pages, line, context)
            edge(website, 'tests/automation/ClosedSpecs.sol', 89, '--proofs enables direct fixture read and browser verification request', context)

    workflow = '.github/workflows/editor-parity.yml'; stdio = 'vscode/parity/stdio.cjs'; workloads = 'vscode/parity/workloads.cjs'
    if approved([workflow, stdio, workloads]):
        context = 'ci:editor-parity-stdio'
        ci(stdio, workflow, 117, context, conditional="workflow_dispatch inputs.transport == 'stdio'", targets=['dafny','local'])
        edge(stdio, workloads, 124, '--scope full calls servicesWorkload for default dafny and local targets', context, True)
        for suffix in ('dfy','sol'):
            target = 'tests/editor-parity/services.' + suffix
            edge(workloads, target, 39, 'servicesWorkload reads selected target fixture', context)
            edge(stdio, target, 388, 'report records SHA256 of both named service fixtures', context)

    h112 = 'tests/h62/item5/statement-graph/h112-tooling.test.mjs'
    w0 = 'tests/h62/item5/statement-graph/test_w0_tooling.py'
    if approved([h112]):
        edge(h112, 'scripts/h62/item5/statement-graph/reproduce_pin_drift.py', 87,
             'negative control executes python3 -O FILE; requires exit 1 and optimized-Python refusal; no post-guard inputs claimed',
             'scripts/coord-tools/gate.sh', True)
    if approved([w0]):
        edge(w0, 'scripts/h62/item5/statement-graph/reproduce_core_baseline.mjs', 99,
             'negative control executes node FILE with a history-override environment variable; requires early refusal; no post-guard inputs claimed',
             'scripts/coord-tools/gate.sh', True)

    # Explicit selected calls, including variable arguments and a cached helper.
    # The preconditions/counterexamples early-refusal calls are not readers.
    source_cases = [('preconditions', 23, 'Preconditions'), ('finite-spec-sets', 8, 'FiniteSets'), ('counterexamples', 10, 'Counterexamples'), ('lex-metrics', 12, 'LexMetrics'), ('lex-metrics', 31, 'LexDiamond'), ('source-shadowing', 24, 'Shadowing'), ('spec-hygiene', 12, 'SpecHygiene'), ('filtered-spec-sets', 10, 'FilteredSets')]
    for name, line, fixture in source_cases:
        source = 'scripts/' + name + '.test.mjs'
        target = 'tests/solc/' + fixture + '.sol'
        if not approved([lean_workflow, source, runner]): continue
        context = f'ci:source-matrix:{name}:{line}'
        ci(source, lean_workflow, 187, context, selected_call=f'{source}:{line}', source_argument=target)
        edge(source, runner, line, 'test callback calls runSolidityTests with selected committed source', context, True)
        edge(runner, target, 117, 'runSourceTests reads selected source bytes; source argument bound by selected_call', context)
