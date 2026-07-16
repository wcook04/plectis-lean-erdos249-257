#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build or check the bounded machine-readable publication entry packet."""

from __future__ import annotations

import argparse
from pathlib import Path

from publication_contract import (
    ENTRY_PACKET_PATH,
    RepositoryReader,
    build_publication_entry_packet,
    canonical_json_bytes,
    validate_publication_entry_packet,
)


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed or staged packet is stale",
    )
    parser.add_argument(
        "--git-ref",
        help="read canonical owners from a committed Git ref, or ':' for the index",
    )
    args = parser.parse_args()

    reader = RepositoryReader(ROOT, args.git_ref)
    try:
        expected = canonical_json_bytes(build_publication_entry_packet(reader))
    except (FileNotFoundError, KeyError, UnicodeError, ValueError) as error:
        print(f"build_publication_entry_packet: unable to build: {error}")
        return 1

    if args.check:
        try:
            actual = reader.read_bytes(ENTRY_PACKET_PATH)
        except (FileNotFoundError, OSError, UnicodeError) as error:
            print(f"build_publication_entry_packet: packet missing: {error}")
            return 1
        errors = validate_publication_entry_packet(reader)
        if actual != expected and not errors:
            errors.append("packet bytes are not canonical")
        if errors:
            print(
                "build_publication_entry_packet: "
                f"{len(errors)} failure(s)"
            )
            for error in errors:
                print(f"  FAIL {error}")
            return 1
        print(
            "build_publication_entry_packet: packet fresh at "
            f"{args.git_ref or 'worktree'} ({len(actual)} bytes)"
        )
        return 0

    output = ROOT / ENTRY_PACKET_PATH
    output.write_bytes(expected)
    print(
        "build_publication_entry_packet: wrote "
        f"{ENTRY_PACKET_PATH} ({len(expected)} bytes)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
