"""Differential lexical-count tests; the pre-optimization shell loop is oracle."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "constant_usage_counts.py"
spec = importlib.util.spec_from_file_location("constant_usage_counts", SCRIPT)
counts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(counts)

ORACLE = r'''
set -euo pipefail
while IFS=$'\t' read -r name val; do
  [[ -z "$name" ]] && continue
  matches="$(rg -n "\\b${name}\\b" "$1" || true)"
  if [[ -n "$matches" ]]; then
    uses="$(printf '%s\n' "$matches" | wc -l | tr -d ' ')"
  else
    uses=0
  fi
  if [[ "$uses" -gt 0 ]]; then uses=$((uses - 1)); fi
  printf '%s\t%s\t%s\n' "$name" "$uses" "$val"
done < "$2"
'''

DISCOVERY = r'''
/^[A-Za-z_][A-Za-z0-9_]*[ \t]+\.EQU[ \t]+/ {
  name=$1
  val=$3
  gsub(/[,;]/, "", val)
  print name "\t" val
}
'''

CATALOG_ORACLE = ORACLE.replace("while IFS=", 'echo "constant_name,value,domain,usage_sites"\nwhile IFS=').replace(
    "  printf '%s\\t%s\\t%s\\n' \"$name\" \"$uses\" \"$val\"",
    r'''  domain="misc"
  case "$name" in
    ZP_*) domain="zp" ;;
    RAM_*) domain="ram" ;;
    PPU*|PPU_*) domain="ppu" ;;
    APU*|IO_RAW_40*) domain="apu" ;;
    OAM*|RAM_OAM*) domain="oam" ;;
    JOYPAD*|PAD_*|BTN_*) domain="input" ;;
    AUDIO_*|SFX_*|MUSIC_*) domain="audio" ;;
  esac
  printf '%s,%s,%s,%s\n' "$name" "$val" "$domain" "$uses"''')


class ConstantUsageTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.asm = Path(self.tmp.name) / "source with spaces.asm"
        self.rows = Path(self.tmp.name) / "constants.tsv"
        self.environment = patch.dict(os.environ)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        os.environ.pop("RIPGREP_CONFIG_PATH", None)

    def compare(self, source, rows):
        self.asm.write_bytes(source)
        self.rows.write_bytes(rows)
        old = subprocess.run(["bash", "-c", ORACLE, "_", str(self.asm), str(self.rows)],
                             capture_output=True, check=True)
        new = subprocess.run(["python3", "-B", str(SCRIPT), str(self.asm), str(self.rows)],
                             capture_output=True, check=True)
        self.assertEqual(new.stdout, old.stdout)
        return new.stdout

    def test_comments_case_boundaries_and_repeated_tokens(self):
        result = self.compare(
            b"COUNT .EQU 2\nOTHER .EQU 3\nUNUSED .EQU 4\n"
            b"COUNT+COUNT ; COUNT and OTHER\n; COUNT\n"
            b"count COUNTER _COUNT COUNT_ COUNT2 2COUNT\n",
            b"COUNT\t2\nOTHER\t3\nUNUSED\t4\n")
        self.assertEqual(result, b"COUNT\t2\t2\nOTHER\t1\t3\nUNUSED\t0\t4\n")

    def test_duplicate_name_distinct_values_retain_both_rows(self):
        result = self.compare(b"VALUE .EQU $01\nVALUE .EQU %00000010\nVALUE+VALUE\n",
                              b"VALUE\t$01\nVALUE\t%00000010\n")
        self.assertEqual(result, b"VALUE\t2\t$01\nVALUE\t2\t%00000010\n")

    def test_unicode_word_boundaries_include_combining_and_join_characters(self):
        source = "TOKEN .EQU 1\n"
        for char in ("é", "中", "\u0301", "\u0903", "\u200c", "\u200d", "\u203f", "🙂", "\u2160"):
            source += f"{char}TOKEN TOKEN{char}\n"
        self.compare(source.encode(), b"TOKEN\t1\n")

    def test_only_lf_is_a_physical_line_boundary(self):
        self.compare("TOKEN .EQU 1\r\nTOKEN\rTOKEN\vTOKEN\fTOKEN\u0085TOKEN\u2028TOKEN\u2029TOKEN\nTOKEN".encode(),
                     b"TOKEN\t1\n")

    def test_empty_and_missing_value_rows(self):
        self.assertEqual(self.compare(b"", b""), b"")
        self.compare(b"EMPTY .EQU \nVALUE .EQU \"a,b\"\r\n", b"EMPTY\t\nVALUE\t\"ab\"\r\n")

    def test_binary_input_retains_per_pattern_notice_behavior(self):
        self.compare(b"FIRST .EQU 1\nSECOND .EQU 2\nFIRST\n\0SECOND\nFIRST\n",
                     b"FIRST\t1\nSECOND\t2\n")

    def test_invalid_utf8_retains_legacy_matching(self):
        self.compare(b"TOKEN .EQU 1\n\xffTOKEN\nTOKEN\xff\n", b"TOKEN\t1\n")

    def test_custom_rg_options_retain_legacy_policy(self):
        config = Path(self.tmp.name) / "rg.conf"
        config.write_text("--ignore-case\n")
        os.environ["RIPGREP_CONFIG_PATH"] = str(config)
        self.compare(b"TOKEN .EQU 1\ntoken TOKEN\n", b"TOKEN\t1\n")

    def test_one_search_process_independent_of_constant_count(self):
        for size in (1, 1000):
            names = {f"CONST_{i}" for i in range(size)}
            self.asm.write_text("".join(f"{name} .EQU 1\n{name}+{name}\n" for name in sorted(names)))
            with patch.object(counts.subprocess, "run", wraps=subprocess.run) as run:
                actual = counts.count_lines(str(self.asm), names)
            self.assertEqual(run.call_count, 1)
            self.assertEqual(actual, dict.fromkeys(names, 2))

    def test_missing_source_matches_legacy_zero_counts_and_diagnostic(self):
        self.rows.write_bytes(b"TOKEN\t1\n")
        old = subprocess.run(["bash", "-c", ORACLE, "_", str(self.asm), str(self.rows)], capture_output=True)
        new = subprocess.run(["python3", "-B", str(SCRIPT), str(self.asm), str(self.rows)], capture_output=True)
        self.assertEqual((new.returncode, new.stdout, new.stderr), (old.returncode, old.stdout, old.stderr))

    def test_missing_rows_and_bad_cli_refuse(self):
        result = subprocess.run(["python3", "-B", str(SCRIPT), str(self.asm), str(self.rows)], capture_output=True)
        self.assertEqual(result.returncode, 65)
        self.assertIn(b"cannot count constant usage", result.stderr)
        self.assertEqual(subprocess.run(["python3", "-B", str(SCRIPT)], capture_output=True).returncode, 64)

    def test_complete_refresh_catalog_matches_legacy_discovery_and_rendering(self):
        self.asm.write_bytes(
            b".ORG $C000\nZP_Item .EQU $10\nRAM_OAM_BASE .EQU $0200\n"
            b"PPUCTRL .EQU $2000\nAPU_STATE .EQU 1\nIO_RAW_4015 .EQU $4015\n"
            b"OAM_BYTES .EQU 4\nJOYPAD_MASK .EQU %00000001\nPAD_BIT .EQU 2\nBTN_BIT .EQU 4\n"
            b"AUDIO_RATE .EQU 1\nSFX_ID .EQU 2\nMUSIC_ID .EQU 3\n"
            b"VALUE .EQU $01\nVALUE .EQU %00000010\nVALUE .EQU $01\n"
            b"EMPTY .EQU ; empty value\nTEXT .EQU \"a,b\";comment\nCR_VALUE .EQU 4\r\n"
            b" Indented .EQU 1\nlowercase .equ 1\n"
            b"Reset:\n  LDA #VALUE ; VALUE ZP_Item RAM_OAM_BASE\n  RTS\n")
        project = Path(self.tmp.name) / "projects" / "demo"
        docs = project / "docs"
        (docs / "inventory").mkdir(parents=True)
        (project / "project.conf").write_text(
            f'ASM_FILE="{self.asm}"\nREF_NES="{project}/reference.nes"\n'
            f'DOC_ROOT="{docs}"\nSYSTEMS_DOC="{docs}/Systems.md"\n'
            f'WARN_BASELINE_FILE="{docs}/warnings.txt"\nNESREV_RECOVERY_STATUS="none"\n')
        xref = Path(self.tmp.name) / "xref.json"
        xref.write_text(json.dumps({"version": "2", "symbols": [], "data_directive_references": []}))
        env = {**os.environ, "NESREV_XREF_FILE": str(xref), "NESREV_INVENTORY_OUT_DIR": str(docs / "inventory")}
        discovered = subprocess.check_output(["awk", DISCOVERY, str(self.asm)])
        self.rows.write_bytes(subprocess.check_output(["sort", "-u"], input=discovered))
        expected = subprocess.check_output(["bash", "-c", CATALOG_ORACLE, "_", str(self.asm), str(self.rows)])
        subprocess.run(["bash", str(ROOT / "scripts/refresh_inventory.sh"), "demo"],
                       cwd=self.tmp.name, env=env, capture_output=True, check=True)
        catalog = docs / "inventory" / "constants_catalog.csv"
        self.assertEqual(catalog.read_bytes(), expected)
        self.assertIn(b"RAM_OAM_BASE,$0200,ram,1\n", expected)
        self.assertEqual(sum(line.startswith(b"VALUE,") for line in expected.split(b"\n")), 2)
        self.assertNotIn(b"Indented,", expected)
        self.assertNotIn(b"lowercase,", expected)

        check = ["python3", str(ROOT / "scripts/inventory_sync_check.py"), "demo", str(self.asm),
                 str(docs), str(ROOT / "scripts/refresh_inventory.sh")]
        subprocess.run(check, cwd=self.tmp.name, env=env, capture_output=True, check=True)
        catalog.write_bytes(expected.replace(b"ZP_Item,$10,zp,1", b"ZP_Item,$10,zp,99"))
        result = subprocess.run(check, cwd=self.tmp.name, env=env, capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"generated inventory is out of sync", result.stderr)
        self.assertIn(b"constants_catalog.csv", result.stderr)

        catalog.write_bytes(expected)
        self.asm.write_bytes(self.asm.read_bytes() + b"; ZP_Item\n")
        result = subprocess.run(check, cwd=self.tmp.name, env=env, capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"constants_catalog.csv", result.stderr)


if __name__ == "__main__":
    unittest.main()
