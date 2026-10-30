"""Local Lean header/dependency discovery, including declared library srcDir.
Build orchestration only; not a Solidity parser or semantic layer.
"""
import re, tomllib
from pathlib import Path
MODULE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')

def header_imports(text):
 imports, depth = [], 0
 for original in text.splitlines():
  clean, index = [], 0
  while index < len(original):
   if depth:
    if original.startswith('/-', index): depth += 1; index += 2
    elif original.startswith('-/', index): depth -= 1; index += 2
    else: index += 1
   elif original.startswith('--', index): break
   elif original.startswith('/-', index): depth = 1; index += 2
   else: clean.append(original[index]); index += 1
  line = ''.join(clean).strip()
  if not line or line == 'prelude': continue
  match = re.fullmatch(r'(?:public )?(?:meta )?import\s+(.+)', line)
  if not match: break
  for module in match.group(1).split():
   if not MODULE.fullmatch(module): raise ValueError('Unsupported import header token: ' + module)
   imports.append(module)
 return imports

class SourceGraph:
 def __init__(self, root):
  self.root = Path(root)
  settings = tomllib.loads((self.root/'lakefile.toml').read_text())
  package_source = self.root / settings.get('srcDir', '.')
  directories = [package_source] + [package_source / library.get('srcDir', '.')
   for library in settings.get('lean_lib', [])]
  self.directories = list(dict.fromkeys(path.resolve() for path in directories))
 def source(self, module):
  if not MODULE.fullmatch(module): raise ValueError('Invalid module: ' + module)
  relative = module.replace('.', '/') + '.lean'
  found = list(dict.fromkeys((directory/relative).resolve() for directory in self.directories
   if (directory/relative).is_file()))
  if len(found) > 1: raise ValueError('Ambiguous local source for ' + module)
  return found[0] if found else None
 def imports(self, module):
  source = self.source(module)
  return header_imports(source.read_text()) if source else []
 def closure(self, targets):
  ordered, seen = [], set()
  def visit(module):
   if module in seen: return
   seen.add(module)
   if self.source(module) is None: return  # Prebuilt toolchain modules.
   for dependency in self.imports(module): visit(dependency)
   ordered.append(module)
  for target in targets:
   if self.source(target) is None: raise ValueError('Missing explicit target: ' + target)
   visit(target)
  return ordered
