"""Admit runtime cache aliases only for identical compiled import artifacts."""
import pathlib

def runtime_aliases(compiled, runtime, frozen):
    if set(compiled) != set(runtime):
        raise ValueError('native runtime import closure differs from compiled closure')
    def roles(paths):
        result = {}
        for file in paths:
            path = pathlib.Path(file).resolve()
            role = path.name.partition('.')[2]
            if not role or role in result:
                raise ValueError('ambiguous native import artifact role')
            result[role] = path
        return result
    admitted = {}
    for module, paths in compiled.items():
        expected, actual = roles(paths), roles(runtime[module])
        if set(expected) != set(actual):
            raise ValueError('native runtime artifact roles differ: ' + module)
        for role, path in actual.items():
            raw = path.read_bytes()
            if raw != frozen[str(expected[role])]:
                raise ValueError('native runtime artifact contents differ: ' + module + ':' + role)
            admitted[str(path)] = raw
    return admitted
