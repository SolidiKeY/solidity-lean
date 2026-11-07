"""Path guard for the isolated per-file diagnostic."""
from pathlib import Path

def validated_target(project: Path, requested: Path) -> Path:
    expected = project / "PanicBytes.lean"
    if expected.is_symlink():
        raise ValueError("project helper must not be a symlink")
    target = requested.resolve(strict=True)
    if target != expected:
        raise ValueError("diagnostic target is not the project helper")
    return target

def validate_fresh_project(project: Path) -> None:
    for name in (".lake", "lake-manifest.json"):
        artifact = project / name
        if artifact.exists() or artifact.is_symlink():
            raise ValueError(f"isolated project artifact already exists: {name}")
