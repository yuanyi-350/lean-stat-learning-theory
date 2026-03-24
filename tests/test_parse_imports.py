from pathlib import Path

import pytest

from tongwen.dependcy import _parse_imports


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        (
            """module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Ray.Manifold.Defs
import Ray.Dynamics.Multiple
import Ray.Manifold.Nontrivial -- This module is necessay
import Ray.Manifold.OpenMapping
import all Ray.Manifold.Inverse

/-!
## Global inverse functions theorems on 1D complex manifolds
-/

open Classical
""",
            [
                "Mathlib.Analysis.Complex.Basic",
                "Mathlib.Geometry.Manifold.ContMDiff.Defs",
                "Ray.Manifold.Defs",
                "Ray.Dynamics.Multiple",
                "Ray.Manifold.Nontrivial",
                "Ray.Manifold.OpenMapping",
                "Ray.Manifold.Inverse",
            ],
        ),
    ],
)
def test_parse_imports(tmp_path: Path, source: str, expected: list[str]) -> None:
    file_path = tmp_path / "Test.lean"
    file_path.write_text(source, encoding="utf-8")
    assert _parse_imports(file_path) == expected
