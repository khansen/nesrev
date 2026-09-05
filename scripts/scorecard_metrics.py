"""Current source measurements shared by intake snapshots and active-pass sync."""

import re
import subprocess
from pathlib import Path


def measure(asm_file, const_kpi_file, script_dir):
    text = Path(asm_file).read_text(encoding="utf-8")
    definitions = len(re.findall(r"^L[0-9A-F]{4,5}:", text, re.M))
    occurrences = len(re.findall(r"\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:", text, re.M))
    result = {
        "labels_remaining": f"{definitions} / {occurrences}",
        "raw_rom_calls_remaining": str(len(re.findall(r"^\s+(?:JSR|JMP)\s+\$[0-9A-F]{4}\b", text, re.M))),
        "raw_indirect_operands_remaining": str(len(re.findall(r"\[\$[0-9A-F]{1,4}(?:,[XY])?\](?:,[XY])?", text, re.I))),
    }
    process = subprocess.run(["bash", str(Path(script_dir) / "constant_kpi.sh"), str(asm_file), str(const_kpi_file)],
                             capture_output=True, text=True)
    if process.returncode != 0:
        raise ValueError("constant KPI calculation failed: " + (process.stderr or process.stdout).strip())
    matches = re.findall(r"^\[const-kpi\] strict_active_magic_immediates=(\d+)\s*$", process.stdout, re.M)
    if len(matches) != 1:
        raise ValueError("constant KPI calculation omitted its measurement")
    result["hardcoded_counter_sites_remaining"] = matches[0]
    return result
