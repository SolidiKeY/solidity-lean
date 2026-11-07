"""Portable task locations. Overrides select directories, not a toolchain pin.
The official archive/pin checks remain acceptance prerequisites.
"""
import json, os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
def configured_path(variable,default):
    value=os.environ.get(variable)
    if value is not None and not value.strip():
        raise ValueError(variable+' must not be empty')
    path=Path(value if value is not None else default).expanduser()
    return (path if path.is_absolute() else ROOT/path).resolve()
EVIDENCE=configured_path('H62_GENERIC_PASSES_EVIDENCE',ROOT.parent/'h62-generic-passes-evidence')
INPUTS=configured_path('H62_GENERIC_PASSES_INPUTS',ROOT.parent/'h62-coordinator-inputs')

_OFFICIAL_PIN={
    'toolchain':'leanprover/lean4:v4.35.0',
    'asset':'lean-4.35.0-linux.tar.zst',
    'url':'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst',
    'sha256':'7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d',
}
def load_pin():
    pin=json.loads((INPUTS/'toolchain-pin.json').read_text())
    if pin!=_OFFICIAL_PIN:
        raise ValueError('toolchain pin differs from mandated official v4.35.0 release')
    return pin
