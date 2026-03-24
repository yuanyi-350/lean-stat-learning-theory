from __future__ import annotations

import re
import subprocess
import sys
import threading
from dataclasses import dataclass
from pathlib import Path

from .strip_lean_comments import strip_lean_comments_from_file

__all__ = ["FileProcessor", "ProcessResult"]


FORBIDDEN_PATTERN = re.compile(r"\b(?:axiom|admit)\b")


@dataclass(frozen=True)
class ProcessResult:
    ok: bool
    failure_kind: str | None = None
    message: str | None = None
    codex_log_path: Path | None = None


class FileProcessor:
    def __init__(
        self,
        run_log_dir: Path,
        max_retries: int = 3,
        placeholder: str = "__________________",
        tag: str = "[pipeline]",
        success_label: str = "success",
        fail_label: str = "fail",
    ) -> None:
        self.run_log_dir = run_log_dir
        self.max_retries = max_retries
        self.placeholder = placeholder
        self.tag = tag
        self.success_label = success_label
        self.fail_label = fail_label
        self.git_lock = threading.Lock()

    @staticmethod
    def _log_stem_from_path(path: str) -> str:
        return Path(path).with_suffix("").as_posix().replace("/", "__")

    def _codex_log_path(self, path: str, attempt: int) -> Path:
        return self.run_log_dir / f"{self._log_stem_from_path(path)}.attempt{attempt}.codex.log"

    def _make_prompt(self, prompt_template: str, path: str) -> str:
        return prompt_template.replace(self.placeholder, path)

    def _run_codex(self, prompt: str, log_path: Path) -> tuple[bool, str | None]:
        try:
            with open(log_path, "w", encoding="utf-8") as log_file:
                result = subprocess.run(
                    ["codex", "--search", "exec", "-", "--color", "never"],
                    input=prompt,
                    text=True,
                    stdout=log_file,
                    stderr=subprocess.STDOUT,
                )
        except Exception as exc:
            print(f"{self.tag} codex {self.fail_label}: {exc}", file=sys.stderr)
            return False, f"codex invocation error: {exc}"
        if result.returncode == 0:
            print(f"{self.tag} codex {self.success_label}: {log_path}")
            return True, None
        print(
            f"{self.tag} codex {self.fail_label} (code {result.returncode}): {log_path}",
            file=sys.stderr,
        )
        return False, f"codex exited with code {result.returncode}"

    @staticmethod
    def _run_lean(path: str) -> bool:
        result = subprocess.run(
            ["lake", "env", "lean", path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return result.returncode == 0

    @staticmethod
    def _has_forbidden_terms(path: str) -> bool:
        content = strip_lean_comments_from_file(path)
        return bool(FORBIDDEN_PATTERN.search(content))

    def _git_restore(self, path: str) -> bool:
        with self.git_lock:
            result = subprocess.run(
                ["git", "restore", "--", path],
                capture_output=True,
                text=True,
            )
        if result.returncode != 0:
            if result.stdout:
                print(result.stdout)
            if result.stderr:
                print(result.stderr, file=sys.stderr)
            print(f"{self.tag} git restore {path} {self.fail_label}.", file=sys.stderr)
            return False
        print(f"{self.tag} {path} contains forbidden terms, restored with git restore.")
        return True

    def _validate_no_forbidden_terms(self, path: str) -> bool:
        if not self._has_forbidden_terms(path):
            return True
        print(
            f"{self.tag} {path} compile {self.success_label} but found forbidden term(s): axiom/admit.",
            file=sys.stderr,
        )
        self._git_restore(path)
        return False

    def _git_commit(self, path: str) -> bool:
        with self.git_lock:
            result = subprocess.run(
                ["git", "add", path],
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                print(result.stderr, file=sys.stderr)
                return False

            staged_check = subprocess.run(
                ["git", "diff", "--cached", "--quiet", "--", path],
                capture_output=True,
                text=True,
            )
            if staged_check.returncode == 0:
                print(f"{self.tag} {path} has no staged changes, skipping commit.")
                return True
            if staged_check.returncode != 1:
                if staged_check.stderr:
                    print(staged_check.stderr, file=sys.stderr)
                return False

            result = subprocess.run(
                ["git", "commit", "-m", f"fix: {path}"],
                capture_output=True,
                text=True,
            )
            print(result.stdout)
            if result.stderr:
                print(result.stderr, file=sys.stderr)
            return result.returncode == 0

    def _git_push(self) -> bool:
        with self.git_lock:
            result = subprocess.run(
                ["git", "push"],
                capture_output=True,
                text=True,
            )
        print(result.stdout)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        if result.returncode != 0:
            print(f"{self.tag} git push failed with code {result.returncode}", file=sys.stderr)
        return result.returncode == 0

    def _commit_and_push(self, path: str) -> bool:
        if not self._git_commit(path):
            print(f"{self.tag} {path} git commit step {self.fail_label}.", file=sys.stderr)
            return False
        if not self._git_push():
            print(f"{self.tag} {path} git push step {self.fail_label}.", file=sys.stderr)
            return False
        print(f"{self.tag} {path} git push {self.success_label}.")
        return True

    def process_path(self, path: str, prompt_template: str) -> ProcessResult:
        print(f"\n{self.tag} {path} — pre-check compilation")
        if self._run_lean(path):
            if not self._validate_no_forbidden_terms(path):
                print(
                    f"{self.tag} {path} forbidden terms check {self.fail_label}, retrying with codex.",
                    file=sys.stderr,
                )
            else:
                print(f"{self.tag} {path} pre-check {self.success_label}, committing and pushing...")
                if self._commit_and_push(path):
                    return ProcessResult(ok=True)
                return ProcessResult(
                    ok=False,
                    failure_kind="git_failed",
                    message="git commit or push failed after pre-check success",
                )

        saw_successful_codex_run = False
        last_codex_error = None
        last_codex_log_path = None
        for attempt in range(1, self.max_retries + 1):
            print(f"\n{self.tag} {path} — attempt {attempt}/{self.max_retries}")

            prompt = self._make_prompt(prompt_template, path)
            log_path = self._codex_log_path(path, attempt)
            last_codex_log_path = log_path
            codex_ok, codex_error = self._run_codex(prompt, log_path)
            if not codex_ok:
                last_codex_error = codex_error
                print(f"{self.tag} {path} codex step {self.fail_label}.", file=sys.stderr)
                continue

            saw_successful_codex_run = True
            if self._run_lean(path):
                if not self._validate_no_forbidden_terms(path):
                    print(
                        f"{self.tag} {path} forbidden terms check {self.fail_label}.",
                        file=sys.stderr,
                    )
                    continue
                print(f"{self.tag} {path} compile {self.success_label}, committing and pushing...")
                if self._commit_and_push(path):
                    return ProcessResult(ok=True)
                return ProcessResult(
                    ok=False,
                    failure_kind="git_failed",
                    message="git commit or push failed after codex success",
                    codex_log_path=log_path,
                )

            print(f"{self.tag} {path} compile {self.fail_label}.", file=sys.stderr)

        print(
            f"{self.tag} {path} exceeded {self.max_retries} retries — {self.fail_label}.",
            file=sys.stderr,
        )
        if last_codex_error is not None and not saw_successful_codex_run:
            return ProcessResult(
                ok=False,
                failure_kind="codex_failed",
                message=last_codex_error,
                codex_log_path=last_codex_log_path,
            )
        return ProcessResult(
            ok=False,
            failure_kind="compile_failed",
            message="Lean compile or validation did not succeed within retry budget",
            codex_log_path=last_codex_log_path,
        )
