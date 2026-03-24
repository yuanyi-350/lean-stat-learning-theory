#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

__all__ = ["strip_lean_comments", "strip_lean_comments_from_file"]


def strip_lean_comments(source: str) -> str:
    """Return Lean source with comments removed while preserving separator whitespace."""
    stripped, _ = _strip_code(source, 0, stop_on_closing_brace=False)
    return stripped


def strip_lean_comments_from_file(path: str | Path) -> str:
    """Read a Lean file and return the comment-stripped contents without modifying it."""
    return strip_lean_comments(Path(path).read_text(encoding="utf-8"))


def _strip_code(
    source: str, start: int, stop_on_closing_brace: bool
) -> tuple[str, int]:
    output: list[str] = []
    brace_depth = 0
    i = start
    length = len(source)

    while i < length:
        if stop_on_closing_brace:
            if source[i] == "{":
                brace_depth += 1
                output.append("{")
                i += 1
                continue
            if source[i] == "}":
                if brace_depth == 0:
                    break
                brace_depth -= 1
                output.append("}")
                i += 1
                continue

        if source.startswith("--", i):
            i = _skip_line_comment(source, i)
            continue

        if source.startswith("/-", i):
            i, replacement = _skip_block_comment(source, i)
            output.append(replacement)
            continue

        raw_string = _consume_raw_string(source, i)
        if raw_string is not None:
            raw_text, i = raw_string
            output.append(raw_text)
            continue

        if source[i] == '"':
            string_text, i = _consume_string(source, i)
            output.append(string_text)
            continue

        if source[i] == "«":
            quoted_ident, i = _consume_quoted_identifier(source, i)
            output.append(quoted_ident)
            continue

        output.append(source[i])
        i += 1

    return "".join(output), i


def _skip_line_comment(source: str, start: int) -> int:
    i = start + 2
    while i < len(source) and source[i] != "\n":
        i += 1
    return i


def _skip_block_comment(source: str, start: int) -> tuple[int, str]:
    depth = 1
    newline_count = 0
    i = start + 2
    length = len(source)

    while i < length and depth > 0:
        if source.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if source.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if source[i] == "\n":
            newline_count += 1
        i += 1

    replacement = "\n" * newline_count if newline_count else " "
    return i, replacement


def _consume_raw_string(source: str, start: int) -> tuple[str, int] | None:
    if source[start] != "r":
        return None

    i = start + 1
    while i < len(source) and source[i] == "#":
        i += 1

    if i >= len(source) or source[i] != '"':
        return None

    closing_delimiter = '"' + "#" * (i - start - 1)
    end = source.find(closing_delimiter, i + 1)
    if end == -1:
        return source[start:], len(source)
    end += len(closing_delimiter)
    return source[start:end], end


def _consume_string(source: str, start: int) -> tuple[str, int]:
    output = ['"']
    interpolated = start > 0 and source[start - 1] == "!"
    i = start + 1
    length = len(source)

    while i < length:
        if source[i] == "\\":
            output.append("\\")
            i += 1
            if i < length:
                output.append(source[i])
                i += 1
            continue

        if interpolated and source[i] == "{":
            if i + 1 < length and source[i + 1] == "{":
                output.append("{{")
                i += 2
                continue

            output.append("{")
            i += 1
            embedded, i = _strip_code(source, i, stop_on_closing_brace=True)
            output.append(embedded)
            if i < length and source[i] == "}":
                output.append("}")
                i += 1
            continue

        if interpolated and source[i] == "}" and i + 1 < length and source[i + 1] == "}":
            output.append("}}")
            i += 2
            continue

        output.append(source[i])
        if source[i] == '"':
            i += 1
            break
        i += 1

    return "".join(output), i


def _consume_quoted_identifier(source: str, start: int) -> tuple[str, int]:
    i = start + 1
    while i < len(source):
        if source[i] == "»":
            i += 1
            break
        i += 1
    return source[start:i], i
