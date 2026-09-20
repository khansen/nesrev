#!/usr/bin/env python3
"""Check local PDF/OCR dependencies for user-supplied game references."""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path


TOOLS = {
    "pdftotext": ("-v", "PDF text extraction; install Poppler (brew install poppler / apt install poppler-utils)"),
    "pdftoppm": ("-v", "PDF page rendering for OCR; install Poppler (brew install poppler / apt install poppler-utils)"),
    "tesseract": ("--version", "image OCR; install Tesseract (brew install tesseract / apt install tesseract-ocr)"),
}
IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".tif", ".tiff", ".bmp", ".pbm", ".pgm", ".ppm", ".pnm", ".webp", ".gif", ".jp2"}


def reference_files(directory: Path) -> list[Path]:
    return sorted(
        path for path in directory.rglob("*")
        if not any(part.startswith(".") for part in path.relative_to(directory).parts)
        and path.is_file() and path.stat().st_size > 0
    )


def project_reference_files(root: Path, project: str) -> list[Path]:
    references = root / "projects" / project / "docs" / "game_reference"
    return reference_files(references / "manuals") + reference_files(references / "faqs")


def required_tools(files: list[Path]) -> set[str]:
    suffixes = {path.suffix.lower() for path in files}
    if ".pdf" in suffixes:
        # A PDF can mix searchable text with scanned pages; prepare both paths.
        return set(TOOLS)
    return {"tesseract"} if suffixes & IMAGE_SUFFIXES else set()


def tool_status(tool: str) -> tuple[bool, str]:
    flag, hint = TOOLS[tool]
    binary = shutil.which(tool)
    if not binary:
        return False, hint
    try:
        version = subprocess.run([binary, flag], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=10)
        if version.returncode:
            return False, f"installed but version probe failed; repair {tool}. {hint}"
        banner = (version.stdout + version.stderr).strip().splitlines()
        detail = banner[0] if banner else "installed"
        if tool == "tesseract":
            languages = subprocess.run(
                [binary, "--list-langs"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=10,
            )
            usable = [line.strip() for line in languages.stdout.splitlines()
                      if re.fullmatch(r"[\w/+-]+", line.strip()) and line.strip() not in {"osd", "equ"}]
            if languages.returncode or not usable:
                return False, (
                    "no usable OCR language data; check TESSDATA_PREFIX and install the reference language "
                    "(brew install tesseract-lang / apt install tesseract-ocr-<language>)"
                )
            detail += f"; {len(usable)} recognition language(s) available"
        return True, detail
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, f"cannot run {tool}: {exc}. {hint}"


def reference_tool_issues(files: list[Path]) -> list[str]:
    needed = required_tools(files)
    issues = []
    for tool in TOOLS:
        if tool in needed:
            ok, detail = tool_status(tool)
            if not ok:
                issues.append(f"{tool}: {detail}")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project")
    args = parser.parse_args()
    if args.project and not re.fullmatch(r"[A-Za-z0-9_-]+", args.project):
        parser.error("invalid project slug")
    files = project_reference_files(Path.cwd(), args.project) if args.project else []
    needed = required_tools(files)
    failures = []
    for tool in TOOLS:
        ok, detail = tool_status(tool)
        status = "OK" if ok else "MISSING" if tool in needed else "OPTIONAL"
        print(f"{tool:<12} {status:<9} {detail}")
        if not ok and tool in needed:
            failures.append(tool)
    if failures:
        print(f"reference tools: required by supplied PDF/image files: {', '.join(failures)}", file=sys.stderr)
        return 1
    if needed:
        print("reference tools: PDF/image prerequisites ready; verify the document language and extraction quality during intake")
    else:
        print("reference tools: OCR is optional until PDF/image references are supplied; use project-doctor PROJECT=<slug> to check them")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except OSError as exc:
        print(f"reference tools: {exc}", file=sys.stderr)
        raise SystemExit(1)
