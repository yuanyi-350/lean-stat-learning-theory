#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

from .strip_lean_comments import strip_lean_comments_from_file

__all__ = ["load_dependency_graph"]


def _parse_imports(file_path: Path) -> list[str]:
    imports: list[str] = []

    for line in strip_lean_comments_from_file(file_path).splitlines():
        tokens = line.split()
        if "import" in tokens and tokens[-1] != "import":
            imports.append(tokens[-1])

    return imports


def _module_name_from_path(path: str) -> str:
    return Path(path).with_suffix("").as_posix().replace("/", ".")


def _discover_lean_paths(root: Path, lean_root_dir: str | Path) -> list[str]:
    lean_root_dir = Path(lean_root_dir)
    if not lean_root_dir.is_absolute():
        lean_root_dir = root / lean_root_dir
    lean_root_dir = lean_root_dir.resolve()
    if not lean_root_dir.exists():
        raise FileNotFoundError(f"Lean root directory not found: {lean_root_dir}")
    return [
        file_path.relative_to(root).as_posix()
        for file_path in sorted(lean_root_dir.rglob("*.lean"))
    ]


def load_dependency_graph(
    root: Path | None = None, lean_root_dir: str | Path = "CombinatorialGames"
) -> tuple[list[str], dict[str, set[str]]]:
    if root is None:
        root = Path.cwd()
    root = root.resolve()
    paths = _discover_lean_paths(root, lean_root_dir)
    module_to_path = {_module_name_from_path(path): path for path in paths}

    deps_by_path: dict[str, set[str]] = {}
    for path in paths:
        file_path = root / path
        deps = set()
        for dep_module in _parse_imports(file_path):
            dep_path = module_to_path.get(dep_module)
            if dep_path and dep_path != path:
                deps.add(dep_path)
        deps_by_path[path] = deps

    return paths, deps_by_path
