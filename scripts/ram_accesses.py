"""RAM operand sites and byte evidence from validated instruction records."""

import os
from pathlib import Path
import re


RAW_LITERAL = re.compile(r"\$[0-9a-fA-F]{1,4}")


def instruction_ram_sites(document, addr_symbols, asm_file, *, repo_root):
    """Return raw and canonical-equate accesses, marking explicit operand bases.

    Eligibility is consumer policy. Access kinds, pointer wrap, and lexical
    ownership come exclusively from xasm; a pointer's destination is not known.
    """
    canonical = {name for names in addr_symbols.values() for name in names}
    repo_root = Path(repo_root).resolve()
    root = (repo_root / asm_file).resolve()
    paths = [(repo_root / path).resolve() for path in document["files"]]
    files = [asm_file if path == root else os.path.relpath(path, repo_root)
             for path in paths]

    def span(value):
        return {**value, "file": files[value["file"]]}

    raw_sites, symbolized_sites = [], []
    for record in document["records"]:
        access = record["memory_access"]
        if access is None:
            continue
        expression = record["expression"]
        raw = (not record["immediate"] and expression is not None
               and expression["kind"] == "integer"
               and 0 <= expression["value"] <= 0x0FFF
               and RAW_LITERAL.fullmatch(expression["source"]["text"]) is not None)
        terms = record["additive_terms"]
        symbol = next((term["name"] for term in terms["terms"]
                       if term["kind"] == "symbol" and term["name"] in canonical), None) if terms else None
        if not raw and symbol is None:
            continue
        touched = []
        data, pointer = access["data"], access["pointer"]
        if data is not None and not data["via_pointer"]:
            touched.append((data["address"], data["kind"], True))
        if pointer is not None:
            touched.extend(((pointer["address"], "read", True),
                            (pointer["high_byte_address"], "read", False)))
        use = span(record["use"])
        source = {**record["source"], "span": span(record["source"]["span"])}
        provenance = {
            "origin_id": record["origin_id"],
            "operand": record["operand_source"]["text"],
            "mnemonic": record["mnemonic"],
            "file": use["file"],
            "line": use["line"],
            "owner_routine": record["lexical_owner"],
            "use": use,
            "source": source,
            "pointer": pointer,
        }
        for addr, kind, primary in touched:
            if not 0 <= addr <= 0x0FFF:
                continue
            site = {
                **provenance,
                "addr": addr,
                "addr_hex": f"0x{addr:04x}",
                "primary": primary,
                "access_kind": kind,
            }
            if raw:
                raw_sites.append({**site, "primary": primary and addr == expression["value"]})
            if symbol is not None:
                symbolized_sites.append({**site, "symbol": symbol})
        if raw and not any(addr == expression["value"] and primary for addr, _, primary in touched):
            # An out-of-range pointer may assemble with truncation. The literal
            # to rename remains at the written address; its reads do not.
            raw_sites.append({
                **provenance, "addr": expression["value"],
                "addr_hex": f"0x{expression['value']:04x}",
                "primary": True, "access_kind": None,
            })
    return raw_sites, symbolized_sites


def group_sites(sites):
    """Group per-byte evidence without merging expanded uses sharing a span."""
    by_addr = {}
    for site in sites:
        entries = by_addr.setdefault(site["addr_hex"], {})
        key = site["origin_id"]
        previous = entries.get(key)
        if previous is None or site["primary"]:
            entries[key] = site
    return {addr: sorted(entries.values(), key=lambda row: (
                row["file"], row["line"], row["origin_id"]))
            for addr, entries in by_addr.items()}


def access_facts(sites):
    owners = sorted({row["owner_routine"] for row in sites if row["owner_routine"]})
    return {
        "operand_count": len({row["origin_id"] for row in sites if row["primary"]}),
        "distinct_owner_routines": owners,
        "distinct_owner_count": len(owners),
        "read_count": sum(row["access_kind"] in {"read", "read_modify_write"} for row in sites),
        "write_count": sum(row["access_kind"] in {"write", "read_modify_write"} for row in sites),
        "sites": sites,
    }
