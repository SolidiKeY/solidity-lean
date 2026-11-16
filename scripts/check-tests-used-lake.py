"""Declared standalone Lake roots, with package-relative import resolution.

Only canonical TOML projects with adjacent committed toolchain pins become
entry points. Missing roots and absolute source directories never invent a use.
External dependencies and explicit globs remain outside this narrow resolver.
A declared target establishes a Lean root, not successful elaboration.
"""
import collections
import json
import posixpath
import re
import shlex
import tomllib


def add(graph, lex):
    repo = graph.repo
    projects = {}
    def relative(base, path):
        if not isinstance(path, str) or path.startswith('/'): return None
        value = posixpath.normpath(posixpath.join(base, path))
        return value if value != '..' and not value.startswith('../') else None
    def project(directory):
        if directory in projects: return projects[directory]
        config = posixpath.normpath(posixpath.join(directory, 'lakefile.toml'))
        if config not in repo.texts: return None
        data = tomllib.loads(repo.texts[config]); entries = []
        for kind in ('lean_lib', 'lean_exe'):
            for entry in data.get(kind, []):
                name = entry.get('name')
                if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.-]*', name): continue
                source = relative(directory, entry.get('srcDir', data.get('srcDir', '.')))
                roots = entry.get('roots', [name]) if kind == 'lean_lib' else [entry.get('root', name)]
                if source is None or not isinstance(roots, list) or not roots or not all(isinstance(r, str) and re.fullmatch(r'[\w.\u00ab\u00bb-]+', r) for r in roots): continue
                # Globs select/associate more modules; they are not expanded
                # into entry points by this resolver.
                if 'globs' in entry: continue
                entries.append((kind, name, source, roots))
        result = {'path': config, 'data': data, 'entries': entries, 'directory': directory}
        projects[directory] = result
        return result
    def closure(initial):
        found = {}; queue = collections.deque([initial]); unavailable = []
        while queue:
            current = queue.popleft()
            if current['directory'] in found: continue
            found[current['directory']] = current
            for requirement in current['data'].get('require', []):
                path = relative(current['directory'], requirement.get('path'))
                dependency = project(path) if path is not None else None
                if dependency is None: unavailable.append(str(requirement.get('name', 'unnamed')))
                else: queue.append(dependency)
        return list(found.values()), sorted(set(unavailable))
    def imports(path):
        cache = getattr(repo, 'package_imports', None)
        if cache is None: cache = repo.package_imports = {}
        if path in cache: return cache[path]
        code = getattr(repo, 'lean_lex_cache', {}).get(path)
        if code is None: code = lex(repo.texts[path])[0]
        depth = 0; result = []
        for line, text in enumerate(code.splitlines(), 1):
            if depth == 0:
                match = re.match(r'\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)', text)
                if match: result.extend((line, name) for name in match[1].split())
            depth += sum(text.count(c) for c in '([{') - sum(text.count(c) for c in ')]}')
        cache[path] = result
        return result
    def resolve(module, dependencies):
        # Quoted/macro-computed names are not guessed. Repository-root imports
        # are available only through a declared local dependency/source root.
        if not re.fullmatch(r'[\w.]+', module): return []
        matches = set()
        for dependency in dependencies:
            for kind, _, directory, roots in dependency['entries']:
                if not any(module == root or kind == 'lean_lib' and module.startswith(root + '.') for root in roots): continue
                candidate = posixpath.normpath(posixpath.join(directory, module.replace('.', '/') + '.lean'))
                if candidate in repo.texts: matches.add(candidate)
        return sorted(matches)
    for config in sorted(p for p in repo.texts if p.endswith('/lakefile.toml')):
        directory = posixpath.dirname(config)
        toolchain = directory + '/lean-toolchain'
        if toolchain not in repo.texts: continue
        current = project(directory)
        dependencies, unavailable = closure(current)
        for kind, name, source, roots in current['entries']:
            for module in roots:
                root = posixpath.normpath(posixpath.join(source, module.replace('.', '/') + '.lean'))
                if root not in repo.texts: continue
                context = 'lake-package:' + config + ':' + name + ':' + module
                line = 1; section = None
                for number, text in enumerate(repo.texts[config].splitlines(), 1):
                    stripped = text.strip()
                    if stripped.startswith('['): section = stripped
                    if section == '[[' + kind + ']]' and re.match(r'^name\s*=', stripped):
                        if tomllib.loads(stripped).get('name') == name: line = number; break
                graph.root(config, 'Lean root', 'LEAN_NUM_THREADS=1 lake build ' + shlex.quote(name), config, line, root_id=context)
                graph.roots[context].update({'cwd': directory, 'lake_package': config,
                    'declared_module': module, 'toolchain': {'path': toolchain, 'blob': repo.tree[toolchain][2], 'pin': repo.texts[toolchain].strip()},
                    'validation_scope': 'Declared target and understood imports only; elaboration not validated.',
                    'limitations': ['External packages, explicit globs and computed imports are not expanded.'],
                    'external_requirements': unavailable})
                graph.edge(config, root, line, 'Lake target declares this Lean root', validated_for=context, kind='executes')
                visited = set(); queue = collections.deque([root])
                while queue:
                    path = queue.popleft()
                    if path in visited: continue
                    visited.add(path)
                    for number, imported in imports(path):
                        matches = resolve(imported, dependencies)
                        if len(matches) != 1: continue
                        target = matches[0]
                        graph.edge(path, target, number, 'Package-relative Lean import', validated_for=context, kind='executes')
                        queue.append(target)
