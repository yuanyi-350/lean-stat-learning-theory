from __future__ import annotations

import subprocess
from pathlib import Path

from .lean_file_processor import ProcessResult
from .send_email import (
    send_pipeline_codex_failure_email,
    send_pipeline_completion_email,
)


def send_codex_failure_report(
    lean_dir: str,
    run_log_dir: Path,
    failed: list[tuple[str, ProcessResult]],
) -> None:
    codex_failures = [
        (path, result)
        for path, result in failed
        if result.failure_kind == "codex_failed"
    ]
    if not codex_failures:
        return

    details = []
    for path, result in codex_failures:
        details.append(f"path: {path}")
        if result.message:
            details.append(f"message: {result.message}")
        if result.codex_log_path is not None:
            details.append(f"codex_log_path: {result.codex_log_path.resolve()}")
        details.append("")

    send_pipeline_codex_failure_email(
        f"{len(codex_failures)} path(s) failed because codex did not complete successfully",
        lean_dir=lean_dir,
        run_log_dir=run_log_dir,
        details="\n".join(details).strip(),
    )


def finalize_successful_pipeline(lean_dir: str, run_log_dir: Path) -> bool:
    try:
        result = subprocess.run(
            ["lake", "build"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception as exc:
        print(f"[pipeline] failed to invoke lake build: {exc}")
        build_ok = False
    else:
        build_ok = result.returncode == 0

    send_pipeline_completion_email(
        lean_dir=lean_dir,
        run_log_dir=run_log_dir,
        build_ok=build_ok,
    )
    return build_ok
