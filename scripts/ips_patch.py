#!/usr/bin/env python3
"""Minimal IPS patch create/apply utility for ROM mod workflow."""

from __future__ import annotations

import pathlib
import sys


IPS_HEADER = b"PATCH"
IPS_EOF = b"EOF"
MAX_OFFSET = 0xFFFFFF
MAX_RECORD_SIZE = 0xFFFF


def _read(path: pathlib.Path) -> bytes:
    return path.read_bytes()


def _write(path: pathlib.Path, data: bytes) -> None:
    path.write_bytes(data)


def create_patch(base_path: pathlib.Path, target_path: pathlib.Path, out_path: pathlib.Path) -> int:
    base = _read(base_path)
    target = _read(target_path)
    max_len = max(len(base), len(target))

    out = bytearray()
    out.extend(IPS_HEADER)

    i = 0
    while i < max_len:
        b = base[i] if i < len(base) else None
        t = target[i] if i < len(target) else None
        if b == t:
            i += 1
            continue

        start = i
        buf = bytearray()
        while i < max_len:
            b = base[i] if i < len(base) else None
            t = target[i] if i < len(target) else None
            if b == t:
                break
            if t is None:
                # Pure truncation is encoded via EOF size.
                break
            buf.append(t)
            i += 1
            if len(buf) == MAX_RECORD_SIZE:
                break

        if buf:
            if start > MAX_OFFSET:
                raise ValueError(f"offset out of IPS range: 0x{start:06X}")
            # IPS reserves offset 0x454F46 ("EOF") as the stream terminator.
            # This creator is intended for NES ROM-scale patches, where that
            # offset is unreachable; reject it instead of emitting ambiguous IPS.
            if start == int.from_bytes(IPS_EOF, "big"):
                raise ValueError("offset 0x454F46 is reserved as the IPS EOF marker")
            out.extend(start.to_bytes(3, "big"))
            out.extend(len(buf).to_bytes(2, "big"))
            out.extend(buf)

        if i == start:
            i += 1

    out.extend(IPS_EOF)
    if len(target) != len(base):
        if len(target) > MAX_OFFSET:
            raise ValueError(f"target size out of IPS EOF range: {len(target)}")
        out.extend(len(target).to_bytes(3, "big"))

    _write(out_path, bytes(out))
    return 0


def apply_patch(base_path: pathlib.Path, patch_path: pathlib.Path, out_path: pathlib.Path) -> int:
    data = bytearray(_read(base_path))
    patch = _read(patch_path)

    if len(patch) < 8 or not patch.startswith(IPS_HEADER):
        raise ValueError("invalid IPS header")

    i = len(IPS_HEADER)
    truncate_size = None

    while True:
        if i + 3 > len(patch):
            raise ValueError("unexpected EOF while reading IPS record offset")
        off_bytes = patch[i : i + 3]
        i += 3
        if off_bytes == IPS_EOF:
            break

        offset = int.from_bytes(off_bytes, "big")
        if i + 2 > len(patch):
            raise ValueError("unexpected EOF while reading IPS record size")
        size = int.from_bytes(patch[i : i + 2], "big")
        i += 2

        if size == 0:
            if i + 3 > len(patch):
                raise ValueError("unexpected EOF while reading IPS RLE record")
            rle_size = int.from_bytes(patch[i : i + 2], "big")
            value = patch[i + 2]
            i += 3
            end = offset + rle_size
            if end > len(data):
                data.extend(b"\x00" * (end - len(data)))
            data[offset:end] = bytes([value]) * rle_size
            continue

        if i + size > len(patch):
            raise ValueError("unexpected EOF while reading IPS payload")
        payload = patch[i : i + size]
        i += size
        end = offset + size
        if end > len(data):
            data.extend(b"\x00" * (end - len(data)))
        data[offset:end] = payload

    remaining = len(patch) - i
    if remaining == 3:
        truncate_size = int.from_bytes(patch[i : i + 3], "big")
    elif remaining != 0:
        raise ValueError("invalid trailing data after IPS EOF marker")

    if truncate_size is not None:
        if truncate_size < len(data):
            del data[truncate_size:]
        elif truncate_size > len(data):
            data.extend(b"\x00" * (truncate_size - len(data)))

    _write(out_path, bytes(data))
    return 0


def main(argv: list[str]) -> int:
    if len(argv) != 5 or argv[1] not in {"create", "apply"}:
        print(
            "usage: ips_patch.py <create|apply> <base.bin> <target_or_patch.bin> <out.bin>",
            file=sys.stderr,
        )
        return 2

    cmd = argv[1]
    base = pathlib.Path(argv[2])
    arg = pathlib.Path(argv[3])
    out = pathlib.Path(argv[4])

    try:
        if cmd == "create":
            return create_patch(base, arg, out)
        return apply_patch(base, arg, out)
    except FileNotFoundError as exc:
        print(f"error: file not found: {exc.filename}", file=sys.stderr)
        return 3
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 5


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
