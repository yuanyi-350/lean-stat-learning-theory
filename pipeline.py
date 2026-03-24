import argparse
import sys
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime
from pathlib import Path

from tongwen.dependcy import load_dependency_graph
from tongwen.lean_file_processor import FileProcessor, ProcessResult
from tongwen.pipeline_outcome import (
    finalize_successful_pipeline,
    send_codex_failure_report,
)

PROMPT_FILE = "PROMPT.md"
PLACEHOLDER = "__________________"
MAX_RETRIES = 3
WORKERS = 4 # Do not increase to 8; it may crash the server.

GREEN = "\033[32m"
RED = "\033[31m"
RESET = "\033[0m"
SUCCESS = f"{GREEN}success{RESET}"
FAIL = f"{RED}fail{RESET}"

TAG = f"{GREEN}[pipeline]{RESET}"
LOG_ROOT = Path(".log")
RUN_LOG_DIR = LOG_ROOT / datetime.now().strftime("%Y%m%d-%H%M%S")


def read_prompt(prompt_file):
    with open(prompt_file, "r") as f:
        return f.read()


def ensure_log_dir():
    RUN_LOG_DIR.mkdir(parents=True, exist_ok=True)


def enqueue_ready_paths(remaining, deps_by_path, resolved, queued, ready_queue):
    newly_added = []
    for path in sorted(remaining):
        if path in queued:
            continue
        if deps_by_path[path].issubset(resolved):
            ready_queue.append(path)
            queued.add(path)
            newly_added.append(path)
    return newly_added


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dir",
        default="CombinatorialGames",
        help="Lean root directory to scan (relative to project root or absolute path)",
    )
    args = parser.parse_args()

    ensure_log_dir()
    print(f"{TAG} codex logs will be written to: {RUN_LOG_DIR}")

    paths, deps_by_path = load_dependency_graph(Path.cwd(), args.dir)
    print(f"{TAG} using Lean root directory: {args.dir}")
    print(f"{TAG} analyzed dependencies for {len(paths)} Lean files")
    prompt_template = read_prompt(PROMPT_FILE)
    file_processor = FileProcessor(
        run_log_dir=RUN_LOG_DIR,
        max_retries=MAX_RETRIES,
        placeholder=PLACEHOLDER,
        tag=TAG,
        success_label=SUCCESS,
        fail_label=FAIL,
    )
    remaining = set(paths)
    resolved = set()
    queued = set()
    ready_queue = deque()
    total = len(paths)

    enqueue_ready_paths(remaining, deps_by_path, resolved, queued, ready_queue)
    print(f"\n{TAG} initial ready queue ({len(ready_queue)}): {list(ready_queue)}")

    failed: list[tuple[str, ProcessResult]] = []
    with ThreadPoolExecutor(max_workers=WORKERS) as executor:
        running = {}
        while remaining or running:
            while ready_queue and len(running) < WORKERS:
                path = ready_queue.popleft()
                future = executor.submit(file_processor.process_path, path, prompt_template)
                running[future] = path
                print(
                    f"{TAG} scheduled {path}; running={len(running)}/{WORKERS}, "
                    f"queued={len(ready_queue)}"
                )

            if not running:
                unresolved = sorted(remaining)
                print(
                    f"\n{TAG} dependency deadlock, unresolved paths: {unresolved}",
                    file=sys.stderr,
                )
                sys.exit(1)

            completed_futures, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed_futures:
                path = running.pop(future)
                queued.discard(path)

                try:
                    result = future.result()
                except Exception as exc:
                    print(f"{TAG} {path} raised exception: {exc}", file=sys.stderr)
                    result = ProcessResult(
                        ok=False,
                        failure_kind="worker_exception",
                        message=str(exc),
                    )

                if not result.ok:
                    detail = f" ({result.failure_kind}: {result.message})" if result.message else ""
                    print(f"{TAG} {path} {FAIL}.{detail}", file=sys.stderr)
                    failed.append((path, result))
                    continue

                resolved.add(path)
                remaining.remove(path)
                print(f"{TAG} resolved {path} ({len(resolved)}/{total}) {SUCCESS}")
                unlocked = enqueue_ready_paths(
                    remaining, deps_by_path, resolved, queued, ready_queue
                )
                if unlocked:
                    print(
                        f"{TAG} unlocked {len(unlocked)} path(s), "
                        f"ready queue now {len(ready_queue)}"
                    )

            if failed:
                for pending in running:
                    pending.cancel()
                break

    if failed:
        failed_paths = [path for path, _ in failed]
        print(f"\n{TAG} {FAIL} paths: {failed_paths}", file=sys.stderr)
        send_codex_failure_report(args.dir, RUN_LOG_DIR, failed)
        sys.exit(1)

    print(f"\n{TAG} all paths processed {SUCCESS}, running final lake build...")
    if not finalize_successful_pipeline(args.dir, RUN_LOG_DIR):
        print(f"{TAG} final lake build {FAIL}.", file=sys.stderr)
        sys.exit(1)

    print(f"{TAG} final lake build {SUCCESS}.")


if __name__ == "__main__":
    main()
