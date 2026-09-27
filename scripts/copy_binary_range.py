#!/usr/bin/env python3
"""Copy an exact byte range with bounded, buffered reads."""

import argparse
import os
import sys

CHUNK_SIZE = 1024 * 1024


def copy_range(source, destination, offset, length):
    if offset < 0 or length < 0:
        raise ValueError("offset and length must be nonnegative")
    source.seek(offset)
    remaining = length
    while remaining:
        block = source.read(min(CHUNK_SIZE, remaining))
        if not block:
            raise ValueError(f"source ended with {remaining} requested byte(s) still missing")
        destination.write(block)
        remaining -= len(block)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("destination")
    parser.add_argument("offset", type=int)
    parser.add_argument("length", type=int)
    args = parser.parse_args()
    try:
        if args.offset < 0 or args.length < 0:
            raise ValueError("offset and length must be nonnegative")
        if os.path.exists(args.destination) and os.path.samefile(args.source, args.destination):
            raise ValueError("source and destination are the same file")
        with open(args.source, "rb") as source, open(args.destination, "wb") as destination:
            copy_range(source, destination, args.offset, args.length)
    except (OSError, ValueError) as error:
        print(f"error: binary range copy failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
