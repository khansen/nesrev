#!/usr/bin/env python3
"""Shared NES graphics helpers for visual identity evidence.

The library decodes iNES CHR data and 2-bit tiles, renders pattern tables and
captured nametables with an NES display palette, converts FCEUX
``gui.gdscreenshot()`` output, and writes PNG files without third-party
packages. Project renderers import it and implement only their own draw-data
walk (metasprite, descriptor or column streams).

Commands:
  chr-sheet  render both pattern tables as a 16x16 tile grid each
  nametable  render one 1 KiB nametable dump with a 32-byte palette dump
  gd2png     convert an FCEUX truecolor GD screenshot to PNG

Pattern-table, nametable and palette dumps are hex text, inline or as @file,
exactly as the screen-capture template records them.

Colors come from a common approximation of the NTSC 2C02 palette. Renders are
for identifying art, not for exact color reproduction.
"""
import argparse
from pathlib import Path
import struct
import sys
import zlib

INES_MAGIC = b"NES\x1a"
HEADER_SIZE = 16
TRAINER_SIZE = 512
PRG_UNIT = 16384
CHR_UNIT = 8192
TILE_BYTES = 16
PATTERN_TABLE_BYTES = 0x1000
NAMETABLE_COLUMNS = 32
NAMETABLE_ROWS = 30
NAMETABLE_BYTES = 1024
ATTRIBUTE_OFFSET = NAMETABLE_COLUMNS * NAMETABLE_ROWS
PALETTE_BYTES = 32

NES_PALETTE = [
    0x7C7C7C, 0x0000FC, 0x0000BC, 0x4428BC, 0x940084, 0xA80020, 0xA81000, 0x881400,
    0x503000, 0x007800, 0x006800, 0x005800, 0x004058, 0x000000, 0x000000, 0x000000,
    0xBCBCBC, 0x0078F8, 0x0058F8, 0x6844FC, 0xD800CC, 0xE40058, 0xF83800, 0xE45C10,
    0xAC7C00, 0x00B800, 0x00A800, 0x00A844, 0x008888, 0x000000, 0x000000, 0x000000,
    0xF8F8F8, 0x3CBCFC, 0x6888FC, 0x9878F8, 0xF878F8, 0xF85898, 0xF87858, 0xFCA044,
    0xF8B800, 0xB8F818, 0x58D854, 0x58F898, 0x00E8D8, 0x787878, 0x000000, 0x000000,
    0xFCFCFC, 0xA4E4FC, 0xB8B8F8, 0xD8B8F8, 0xF8B8F8, 0xF8A4C0, 0xF0D0B0, 0xFCE0A8,
    0xF8D878, 0xD8F878, 0xB8F8B8, 0xB8F8D8, 0x00FCFC, 0xF8D8F8, 0x000000, 0x000000,
]
GRAY_SHADES = (255, 170, 85, 0)


class GraphicsError(Exception):
    pass


def read_ines(path):
    """Return (prg, chr) bytes from an iNES or NES 2.0 file."""
    data = Path(path).read_bytes()
    if len(data) < HEADER_SIZE or data[:4] != INES_MAGIC:
        raise GraphicsError(f"not an iNES file: {path}")
    prg_units, chr_units = data[4], data[5]
    if data[7] & 0x0C == 0x08:
        if data[9] & 0x0F == 0x0F or data[9] >> 4 == 0x0F:
            raise GraphicsError("NES 2.0 exponent-multiplier sizes are not supported")
        prg_units |= (data[9] & 0x0F) << 8
        chr_units |= (data[9] >> 4) << 8
    offset = HEADER_SIZE + (TRAINER_SIZE if data[6] & 0x04 else 0)
    prg_size, chr_size = prg_units * PRG_UNIT, chr_units * CHR_UNIT
    if len(data) < offset + prg_size + chr_size:
        raise GraphicsError(f"truncated iNES file: {path}")
    prg = data[offset:offset + prg_size]
    return prg, data[offset + prg_size:offset + prg_size + chr_size]


def tile_pixels(chr_data, pattern_base, tile):
    """Return an 8x8 list of 2-bit pixel values for one tile."""
    start = pattern_base + tile * TILE_BYTES
    planes = chr_data[start:start + TILE_BYTES]
    if len(planes) != TILE_BYTES:
        raise GraphicsError(f"tile ${tile:02X} at ${pattern_base:04X} is outside the CHR data")
    return [[((planes[row] >> (7 - col)) & 1) | (((planes[row + 8] >> (7 - col)) & 1) << 1)
             for col in range(8)] for row in range(8)]


def rgb(color_index):
    value = NES_PALETTE[color_index & 0x3F]
    return value >> 16, (value >> 8) & 0xFF, value & 0xFF


def attribute_palette(nametable, column, row):
    """Background palette number (0-3) for one tile from the attribute bytes."""
    byte = nametable[ATTRIBUTE_OFFSET + (row // 4) * 8 + column // 4]
    shift = ((row % 4) // 2) * 4 + ((column % 4) // 2) * 2
    return (byte >> shift) & 0x03


def render_nametable(nametable, chr_data, pattern_base, palette):
    """Render a 256x240 RGB image (rows of bytes) from nametable and palette dumps."""
    if len(nametable) < NAMETABLE_BYTES:
        raise GraphicsError(f"nametable dump needs {NAMETABLE_BYTES} bytes, got {len(nametable)}")
    if len(palette) < 16:
        raise GraphicsError(f"palette dump needs at least 16 bytes, got {len(palette)}")
    rows = [bytearray(NAMETABLE_COLUMNS * 8 * 3) for _ in range(NAMETABLE_ROWS * 8)]
    for row in range(NAMETABLE_ROWS):
        for column in range(NAMETABLE_COLUMNS):
            pixels = tile_pixels(chr_data, pattern_base, nametable[row * NAMETABLE_COLUMNS + column])
            base = attribute_palette(nametable, column, row) * 4
            for y in range(8):
                line = rows[row * 8 + y]
                for x in range(8):
                    value = pixels[y][x]
                    color = rgb(palette[0] if value == 0 else palette[base + value])
                    line[(column * 8 + x) * 3:(column * 8 + x) * 3 + 3] = bytes(color)
    return [bytes(line) for line in rows]


def render_pattern_tables(chr_data):
    """Render both pattern tables side by side as a 256x128 grayscale image."""
    rows = [bytearray(256) for _ in range(128)]
    for table in range(2):
        for tile in range(256):
            pixels = tile_pixels(chr_data, table * PATTERN_TABLE_BYTES, tile)
            x0, y0 = table * 128 + (tile % 16) * 8, (tile // 16) * 8
            for y in range(8):
                for x in range(8):
                    rows[y0 + y][x0 + x] = GRAY_SHADES[pixels[y][x]]
    return [bytes(line) for line in rows]


def scale_rows(rows, factor, channels):
    if factor == 1:
        return rows
    out = []
    for line in rows:
        wide = bytearray()
        for i in range(0, len(line), channels):
            wide += line[i:i + channels] * factor
        out.extend([bytes(wide)] * factor)
    return out


def write_png(path, rows, channels):
    """Write 8-bit grayscale (channels=1) or RGB (channels=3) rows as PNG."""
    if channels not in (1, 3):
        raise GraphicsError("channels must be 1 or 3")
    height = len(rows)
    width = len(rows[0]) // channels if rows else 0
    if any(len(line) != width * channels for line in rows):
        raise GraphicsError("all PNG rows must have the same width")

    def chunk(kind, body):
        return struct.pack(">I", len(body)) + kind + body + struct.pack(">I", zlib.crc32(kind + body) & 0xFFFFFFFF)

    color_type = 0 if channels == 1 else 2
    header = struct.pack(">IIBBBBB", width, height, 8, color_type, 0, 0, 0)
    raw = b"".join(b"\x00" + line for line in rows)
    Path(path).write_bytes(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", header)
                           + chunk(b"IDAT", zlib.compress(raw)) + chunk(b"IEND", b""))


def read_gd(path):
    """Read an FCEUX truecolor GD screenshot as (RGB rows)."""
    data = Path(path).read_bytes()
    if data[:2] != b"\xff\xfe" or len(data) < 11:
        raise GraphicsError(f"not a truecolor GD image: {path}")
    width, height = struct.unpack(">HH", data[2:6])
    pixels = data[11:]
    if len(pixels) != width * height * 4:
        raise GraphicsError(f"GD image has {len(pixels)} pixel bytes, expected {width * height * 4}: {path}")
    rows = []
    for y in range(height):
        line = bytearray()
        for i in range(y * width * 4, (y + 1) * width * 4, 4):
            line += pixels[i + 1:i + 4]
        rows.append(bytes(line))
    return rows


def hex_argument(value, name, size):
    """Decode hex text given inline or as @file; it must hold exactly size bytes."""
    try:
        text = Path(value[1:]).read_text() if value.startswith("@") else value
        data = bytes.fromhex("".join(text.split()))
    except ValueError as exc:
        raise GraphicsError(f"{name} is not hex: {exc}") from exc
    if len(data) != size:
        raise GraphicsError(f"{name} needs {size} bytes, got {len(data)}")
    return data


def load_chr(args):
    """Return the 8 KiB of pattern tables to render."""
    if args.chr:
        if args.chr_bank is not None:
            raise GraphicsError("--chr-bank selects a CHR ROM bank and needs --rom")
        return hex_argument(args.chr, "--chr", CHR_UNIT)
    _, chr_data = read_ines(args.rom)
    if not chr_data:
        raise GraphicsError("the ROM has CHR RAM; pass --chr with a captured pattern-table dump")
    banks = len(chr_data) // CHR_UNIT
    bank = args.chr_bank
    if bank is None:
        if banks > 1:
            raise GraphicsError(f"the ROM has {banks} 8 KiB CHR banks; pass --chr-bank, "
                                "or --chr with a captured pattern-table dump")
        bank = 0
    if not 0 <= bank < banks:
        raise GraphicsError(f"--chr-bank {bank} is outside the ROM's {banks} CHR banks")
    return chr_data[bank * CHR_UNIT:(bank + 1) * CHR_UNIT]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sheet = sub.add_parser("chr-sheet", help="render both pattern tables")
    table = sub.add_parser("nametable", help="render a nametable dump with a palette dump")
    for command in (sheet, table):
        source = command.add_mutually_exclusive_group(required=True)
        source.add_argument("--rom", help="iNES file supplying CHR ROM")
        source.add_argument("--chr", help="8 KiB pattern-table dump as hex, or @file (CHR-RAM or banked CHR)")
        command.add_argument("--chr-bank", type=int, help="8 KiB CHR ROM bank, required when --rom has several")
        command.add_argument("--output", required=True)
        command.add_argument("--scale", type=int, default=2)
    table.add_argument("--nametable", required=True, help="1 KiB nametable as hex, or @file")
    table.add_argument("--palette", required=True, help="32-byte palette as hex, or @file")
    table.add_argument("--pattern-table", type=int, choices=(0, 1), default=0,
                       help="background pattern table selected by PPUCTRL bit 4")
    gd = sub.add_parser("gd2png", help="convert an FCEUX gui.gdscreenshot() file")
    gd.add_argument("input")
    gd.add_argument("output")
    gd.add_argument("--scale", type=int, default=1)
    args = parser.parse_args(argv)
    if args.scale < 1:
        parser.error("--scale must be at least 1")
    try:
        if args.command == "chr-sheet":
            rows, channels = render_pattern_tables(load_chr(args)), 1
        elif args.command == "nametable":
            rows = render_nametable(hex_argument(args.nametable, "--nametable", NAMETABLE_BYTES), load_chr(args),
                                    args.pattern_table * PATTERN_TABLE_BYTES,
                                    hex_argument(args.palette, "--palette", PALETTE_BYTES))
            channels = 3
        else:
            rows, channels = read_gd(args.input), 3
        write_png(args.output, scale_rows(rows, args.scale, channels), channels)
    except (GraphicsError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
