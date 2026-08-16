#!/usr/bin/env python3
"""Build every live paper and verify its standalone KaTeX HTML export."""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path


PAPERS = (
    "goldarf",
    "witt_realization",
    "excess",
    "linking_affine",
    "thermo_newton",
    "transfinite_arf",
)

CITATION = re.compile(
    r"\\(?:cite[a-zA-Z]*|nocite)(?:\s*\[[^\]]*\]){0,2}\s*\{([^}]*)\}"
)
BIB_ENTRY = re.compile(
    r"(?mi)^@(?!comment\b|string\b|preamble\b)\w+\s*\{\s*([^,\s]+)\s*,"
)
UNRESOLVED_LATEX = re.compile(
    r"(?:Citation .+ undefined|Reference .+ undefined|"
    r"There were undefined references|There were undefined citations)",
    re.IGNORECASE,
)
RAW_DOCUMENT_COMMAND = re.compile(
    r"\\(?:cite[a-zA-Z]*|ref|eqref|pageref|autoref|label|bibliography|"
    r"bibliographystyle)(?:\s*\[[^\]]*\]){0,2}\s*\{"
)
OVERFULL_BOX = re.compile(r"Overfull \\[hv]box")


def executable(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    local = Path.home() / ".local" / "bin" / name
    if local.is_file():
        return str(local)
    raise SystemExit(f"missing required executable: {name}")


def run(command: list[str], *, cwd: Path) -> None:
    print("+", " ".join(command), flush=True)
    completed = subprocess.run(command, cwd=cwd, text=True)
    if completed.returncode:
        raise SystemExit(completed.returncode)


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    writeups = root / "writeups"
    html_dir = root / "target" / "writeups" / "html"
    html_dir.mkdir(parents=True, exist_ok=True)

    tectonic = executable("tectonic")
    pandoc = executable("pandoc")
    node = executable("node")
    if not (root / "node_modules" / "katex").is_dir():
        raise SystemExit("missing KaTeX dependency: run `npm ci`")

    selected = tuple(sys.argv[1:]) or PAPERS
    unknown = set(selected) - set(PAPERS)
    if unknown:
        raise SystemExit(f"unknown paper names: {sorted(unknown)}")

    for stem in selected:
        tex = writeups / f"{stem}.tex"
        bib = writeups / f"{stem}.bib"
        if not tex.is_file() or not bib.is_file():
            raise SystemExit(f"paper source pair is incomplete: {stem}")

        source = tex.read_text(encoding="utf-8")
        if "\\begin{thebibliography}" in source:
            raise SystemExit(f"{tex.name}: inline bibliography is not allowed")
        bibliography = bib.read_text(encoding="utf-8")
        used = {
            key.strip()
            for group in CITATION.findall(source)
            for key in group.split(",")
            if key.strip()
        }
        entries = BIB_ENTRY.findall(bibliography)
        available = set(entries)
        if len(entries) != len(available):
            raise SystemExit(f"{bib.name}: duplicate bibliography key")
        if not used:
            raise SystemExit(f"{tex.name}: paper has no academic citations")
        if missing := used - available:
            raise SystemExit(f"{tex.name}: missing bibliography entries: {sorted(missing)}")
        if unused := available - used:
            raise SystemExit(f"{bib.name}: uncited bibliography entries: {sorted(unused)}")

        run(
            [
                tectonic,
                "-X",
                "compile",
                "--keep-logs",
                "--outdir",
                str(writeups),
                tex.name,
            ],
            cwd=writeups,
        )

        log = (writeups / f"{stem}.log").read_text(
            encoding="utf-8", errors="replace"
        )
        match = UNRESOLVED_LATEX.search(log)
        if match:
            raise SystemExit(f"{tex.name}: unresolved LaTeX cross-reference: {match.group(0)}")
        if match := OVERFULL_BOX.search(log):
            raise SystemExit(f"{tex.name}: overfull box in PDF build: {match.group(0)}")

        html = html_dir / f"{stem}.html"
        run(
            [
                pandoc,
                str(tex),
                "--from=latex",
                "--to=html5",
                "--standalone",
                "--citeproc",
                f"--bibliography={bib}",
                "--katex=https://cdn.jsdelivr.net/npm/katex@0.18.4/dist/katex.min.js",
                "--metadata=lang:en",
                "--metadata=link-citations:true",
                "--fail-if-warnings",
                f"--output={html}",
            ],
            cwd=root,
        )

        rendered = html.read_text(encoding="utf-8")
        raw = RAW_DOCUMENT_COMMAND.search(rendered)
        if raw:
            raise SystemExit(f"{tex.name}: raw document command leaked into HTML: {raw.group(0)}")
        if "katex" not in rendered.lower():
            raise SystemExit(f"{tex.name}: Pandoc output does not load KaTeX")
        run([node, str(root / "scripts" / "check_katex.cjs"), str(html)], cwd=root)

    print(f"validated {len(selected)} papers")


if __name__ == "__main__":
    main()
