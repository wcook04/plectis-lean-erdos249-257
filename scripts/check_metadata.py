#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validate release citation metadata with the CI-pinned command."""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    cffconvert = shutil.which("cffconvert")
    if cffconvert is None:
        print(
            "cffconvert is required; install it with: python3 -m pip install cffconvert",
            file=sys.stderr,
        )
        return 2
    return subprocess.run([cffconvert, "--validate"], cwd=ROOT, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
