"""Exercise the shared NES graphics helpers with synthetic ROM, CHR and GD data."""

from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
import zlib

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import nes_graphics as g  # noqa: E402

SCRIPT = ROOT / "scripts/nes_graphics.py"


def chr_with_tile(tile, low, high, table=0):
    """8 KiB CHR with one tile whose rows all use the given plane bytes."""
    data = bytearray(0x2000)
    start = table * 0x1000 + tile * 16
    data[start:start + 8] = bytes([low]) * 8
    data[start + 8:start + 16] = bytes([high]) * 8
    return bytes(data)


def ines(prg_units=1, chr_bytes=b"", trainer=False):
    header = bytearray(b"NES\x1a" + bytes([prg_units, len(chr_bytes) // 0x2000]) + bytes(10))
    if trainer:
        header[6] |= 0x04
    return bytes(header) + (bytes(512) if trainer else b"") + bytes(prg_units * 0x4000) + chr_bytes


def read_png(path):
    data = Path(path).read_bytes()
    assert data[:8] == b"\x89PNG\r\n\x1a\n"
    pos, chunks = 8, {}
    while pos < len(data):
        length = struct.unpack(">I", data[pos:pos + 4])[0]
        kind = data[pos + 4:pos + 8]
        chunks.setdefault(kind, b"")
        chunks[kind] += data[pos + 8:pos + 8 + length]
        pos += 12 + length
    width, height, depth, color = struct.unpack(">IIBB", chunks[b"IHDR"][:10])
    channels = 1 if color == 0 else 3
    raw = zlib.decompress(chunks[b"IDAT"])
    stride = width * channels + 1
    rows = [raw[i * stride + 1:(i + 1) * stride] for i in range(height)]
    return width, height, channels, rows


def cli(*args):
    return subprocess.run([sys.executable, str(SCRIPT), *map(str, args)], capture_output=True, text=True)


class NesGraphicsTest(unittest.TestCase):
    def test_tile_pixels_combines_both_planes(self):
        data = chr_with_tile(1, 0b10100000, 0b11000000)
        self.assertEqual(g.tile_pixels(data, 0, 1)[0][:4], [3, 2, 1, 0])

    def test_read_ines_skips_trainer_and_splits_chr(self):
        chr_data = chr_with_tile(0, 0xFF, 0x00)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "t.nes"
            path.write_bytes(ines(chr_bytes=chr_data, trainer=True))
            prg, chr_out = g.read_ines(path)
        self.assertEqual(len(prg), 0x4000)
        self.assertEqual(chr_out, chr_data)

    def test_read_ines_rejects_truncated_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "t.nes"
            path.write_bytes(ines(chr_bytes=bytes(0x2000))[:-1])
            with self.assertRaises(g.GraphicsError):
                g.read_ines(path)

    def test_attribute_quadrants_select_background_palettes(self):
        nametable = bytearray(1024)
        nametable[960] = 0b11100100  # top-left 0, top-right 1, bottom-left 2, bottom-right 3
        self.assertEqual([g.attribute_palette(nametable, c, r) for c, r in ((0, 0), (2, 0), (0, 2), (2, 2))],
                         [0, 1, 2, 3])

    def test_render_nametable_uses_backdrop_for_zero_and_attribute_palette_otherwise(self):
        data = chr_with_tile(1, 0xFF, 0x00, table=1)  # tile 1 in the $1000 table: every pixel value 1
        nametable = bytearray(1024)
        nametable[2] = 1  # row 0, column 2 lies in the top-right attribute quadrant
        nametable[960] = 0b00000100  # top-right quadrant uses palette 1
        palette = bytes([0x0F, 0, 0, 0, 0x0F, 0x16, 0, 0]) + bytes(24)
        rows = g.render_nametable(bytes(nametable), data, 0x1000, palette)
        self.assertEqual(len(rows), 240)
        self.assertEqual(rows[0][2 * 8 * 3:2 * 8 * 3 + 3], bytes(g.rgb(0x16)))
        self.assertEqual(rows[0][0:3], bytes(g.rgb(0x0F)))

    def test_render_nametable_rejects_short_dump(self):
        with self.assertRaises(g.GraphicsError):
            g.render_nametable(bytes(10), bytes(0x2000), 0, bytes(32))

    def test_gd2png_converts_argb_pixels(self):
        with tempfile.TemporaryDirectory() as tmp:
            gd = Path(tmp) / "shot.gd"
            png = Path(tmp) / "shot.png"
            pixels = bytes([0, 10, 20, 30, 0, 40, 50, 60])
            gd.write_bytes(b"\xff\xfe" + struct.pack(">HH", 2, 1) + b"\x01" + bytes(4) + pixels)
            result = subprocess.run([sys.executable, str(SCRIPT), "gd2png", str(gd), str(png)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            width, height, channels, rows = read_png(png)
        self.assertEqual((width, height, channels), (2, 1, 3))
        self.assertEqual(rows[0], bytes([10, 20, 30, 40, 50, 60]))

    def test_chr_sheet_cli_scales_both_pattern_tables(self):
        with tempfile.TemporaryDirectory() as tmp:
            rom = Path(tmp) / "t.nes"
            rom.write_bytes(ines(chr_bytes=chr_with_tile(0, 0xFF, 0xFF)))
            png = Path(tmp) / "sheet.png"
            result = subprocess.run([sys.executable, str(SCRIPT), "chr-sheet", "--rom", str(rom),
                                     "--output", str(png), "--scale", "2"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            width, height, channels, rows = read_png(png)
        self.assertEqual((width, height, channels), (512, 256, 1))
        self.assertEqual(rows[0][0], g.GRAY_SHADES[3])
        self.assertEqual(rows[0][16], g.GRAY_SHADES[0])

    def test_chr_ram_rom_requires_a_chr_dump(self):
        with tempfile.TemporaryDirectory() as tmp:
            rom = Path(tmp) / "t.nes"
            rom.write_bytes(ines())
            result = subprocess.run([sys.executable, str(SCRIPT), "chr-sheet", "--rom", str(rom),
                                     "--output", str(Path(tmp) / "x.png")], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("pass --chr with a captured pattern-table dump", result.stderr)

    def test_chr_dump_reads_the_capture_templates_hex_text(self):
        with tempfile.TemporaryDirectory() as tmp:
            dump = Path(tmp) / "chr.hex"
            dump.write_text(chr_with_tile(0, 0xFF, 0xFF).hex().upper())
            png = Path(tmp) / "sheet.png"
            result = cli("chr-sheet", "--chr", f"@{dump}", "--output", png, "--scale", 1)
            self.assertEqual(result.returncode, 0, result.stderr)
            _, _, _, rows = read_png(png)
        self.assertEqual(rows[0][0], g.GRAY_SHADES[3])
        self.assertEqual(rows[0][8], g.GRAY_SHADES[0])

    def test_chr_dump_must_be_8_kib_of_hex(self):
        with tempfile.TemporaryDirectory() as tmp:
            short = Path(tmp) / "short.hex"
            short.write_text(bytes(0x1000).hex())
            binary = Path(tmp) / "chr.bin"
            binary.write_bytes(bytes(range(256)) * 32)
            too_short = cli("chr-sheet", "--chr", f"@{short}", "--output", Path(tmp) / "a.png")
            not_hex = cli("chr-sheet", "--chr", f"@{binary}", "--output", Path(tmp) / "b.png")
        self.assertEqual(too_short.returncode, 1)
        self.assertIn("--chr needs 8192 bytes, got 4096", too_short.stderr)
        self.assertEqual(not_hex.returncode, 1)
        self.assertIn("--chr is not hex", not_hex.stderr)

    def test_banked_chr_rom_requires_a_bank(self):
        with tempfile.TemporaryDirectory() as tmp:
            rom = Path(tmp) / "banked.nes"
            rom.write_bytes(ines(chr_bytes=bytes(0x2000) + chr_with_tile(0, 0xFF, 0xFF)))
            png = Path(tmp) / "bank1.png"
            unbanked = cli("chr-sheet", "--rom", rom, "--output", Path(tmp) / "x.png")
            outside = cli("chr-sheet", "--rom", rom, "--chr-bank", 2, "--output", Path(tmp) / "y.png")
            bank1 = cli("chr-sheet", "--rom", rom, "--chr-bank", 1, "--output", png, "--scale", 1)
            self.assertEqual(bank1.returncode, 0, bank1.stderr)
            _, _, _, rows = read_png(png)
        self.assertEqual(unbanked.returncode, 1)
        self.assertIn("2 8 KiB CHR banks; pass --chr-bank", unbanked.stderr)
        self.assertEqual(outside.returncode, 1)
        self.assertIn("outside the ROM's 2 CHR banks", outside.stderr)
        self.assertEqual(rows[0][0], g.GRAY_SHADES[3])

    def test_nametable_dump_must_be_one_nametable(self):
        with tempfile.TemporaryDirectory() as tmp:
            rom = Path(tmp) / "t.nes"
            rom.write_bytes(ines(chr_bytes=bytes(0x2000)))
            result = cli("nametable", "--rom", rom, "--nametable", bytes(0x1000).hex(),
                         "--palette", bytes(32).hex(), "--output", Path(tmp) / "nt.png")
        self.assertEqual(result.returncode, 1)
        self.assertIn("--nametable needs 1024 bytes, got 4096", result.stderr)


if __name__ == "__main__":
    unittest.main()
