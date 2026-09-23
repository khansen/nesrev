"""Reference review evidence, not an automated judgement of semantic coverage."""

from __future__ import annotations

import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from urllib.parse import unquote

from process_friction import structural_lines
from review_packet_evidence import PacketError, one_field, section


def planning_scope(doc_root: Path, project: str, pass_id: str) -> str:
    """Ignored planning metadata must never masquerade as committed evidence."""
    path = doc_root / "inventory/pass/current_pass_plan.json"
    try:
        plan = json.loads(path.read_text())
        if (not isinstance(plan, dict) or plan.get("project") != project
                or str(plan.get("intended_pass_id")) != str(pass_id)):
            return "Not recorded for this pass; reconstruct the reference scope from the reviewed changes."
        objective = plan.get("corridor_objective")
        value = objective.get("reference_scope") if isinstance(objective, dict) else None
        if isinstance(value, str) and value.strip():
            return value.strip()
    except (OSError, ValueError):
        pass
    return "Not recorded for this pass; reconstruct the reference scope from the reviewed changes."


def committed_text(root: Path, head: str, path: str) -> str:
    result = subprocess.run(["git", "show", f"{head}:{path}"], cwd=root,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise PacketError(f"reference evidence is not present at reviewed head: {path}")
    return result.stdout.decode("utf-8")


def inventory_path(crosswalk: Path) -> Path:
    """Canonical authored inventory shared by planning and review."""
    return crosswalk.parent / "MANUAL_TERMS.md"


def check_links(value: str, root: Path, head: str, project: str) -> None:
    links = re.findall(r"\[[^\]\n]+\]\(([^)\s]+)\)", value)
    if not links:
        raise PacketError("reference assessment needs repository-relative Markdown evidence links")
    for target in links:
        path, _, fragment = unquote(target).partition("#")
        parts = PurePosixPath(path).parts
        if (not path.startswith(f"projects/{project}/docs/") or ".." in parts
                or not path.endswith(".md")):
            raise PacketError(f"reference evidence must link to this project's authored docs: {target}")
        text = committed_text(root, head, path)
        if fragment:
            anchors, counts = set(), {}
            for _, line in structural_lines(text):
                anchors.update(re.findall(r'<a\s+id=["\']([^"\']+)["\']', line))
                match = re.match(r"^#{1,6}\s+(.+?)\s*#*\s*$", line)
                if match:
                    title = re.sub(r"[^\w\- ]", "", match[1].lower())
                    slug = title.replace(" ", "-")
                    count = counts.get(slug, 0)
                    anchors.add(f"{slug}-{count}" if count else slug)
                    counts[slug] = count + 1
            if fragment not in anchors:
                raise PacketError(f"missing reference evidence anchor: {target}")


def validate_gold_assessment(document: str, root: Path, head: str, project: str) -> None:
    body = section(document, "Reference Coverage", 2)
    for name in ("Sources", "Inventory", "Mappings", "Gaps"):
        value = one_field(body, rf"^(?:- )?{name}:[ \t]*([^\n]+)$", f"reference {name}").strip()
        if value.lower().strip("_.* ") in {"", "todo", "tbd", "pending", "not assessed"}:
            raise PacketError(f"reference {name} is not assessed")
        check_links(value, root, head, project)
    outcome = one_field(body, r"^(?:- )?Reference coverage:[ \t]*([^\n]+)$", "Reference coverage")
    if outcome not in {"COMPLETE", "EXPLICIT MANUAL WAIVER"}:
        raise PacketError("unresolved reference coverage blocks gold approval")
    if outcome == "EXPLICIT MANUAL WAIVER":
        waiver = one_field(body, r"^(?:- )?Waiver:[ \t]*([^\n]+)$", "manual Waiver")
        check_links(waiver, root, head, project)


def packet_context(root: Path, head: str, project: str, doc_root: Path, crosswalk: Path) -> str:
    from proof_debt import scorecard_rows

    rows = scorecard_rows(doc_root / "PROGRESS_SCORECARD.md")
    pass_id = str(max((int(row["pass_id"]) for row in rows), default=-1))
    lines = ["## Reference Coverage Context", "",
             "Operator reference scope (unversioned planning context; verify against the reviewed range):", "",
             # A code fence prevents operator prose becoming packet structure.
             "```text", planning_scope(doc_root, project, pass_id).replace("`", "'"), "```", "",
             "Read these authored sources at the reviewed head, then the supplied references they cite:", ""]
    for file in (inventory_path(crosswalk), crosswalk):
        path = file.absolute().relative_to(root.absolute()).as_posix()
        try:
            committed_text(root, head, path)
            lines.append(f"- `{path}` at `{head}`")
        except PacketError:
            lines.append(f"- `{path}`: not committed at reviewed head; complete reference intake or migrate existing authored docs to the canonical layout.")
    lines.extend(["", "Review source inventory completeness, term-to-code evidence, shared machinery,",
                  "and newly answerable identity gaps. Mapping counts do not establish coverage.", ""])
    return "\n".join(lines)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory-path", action="store_true")
    for name in ("doc-root", "crosswalk"):
        parser.add_argument("--" + name, required=True)
    for name in ("head", "project"):
        parser.add_argument("--" + name)
    args = parser.parse_args()
    if args.inventory_path:
        print(inventory_path(Path(args.crosswalk)))
    else:
        if not args.head or not args.project:
            parser.error("packet context requires --head and --project")
        print(packet_context(Path.cwd(), args.head, args.project, Path(args.doc_root), Path(args.crosswalk)))
