<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->
# Erdos257 Period Noncollapse Lean Snapshot

This repository is a clean Lean/Lake export generated from a Plectis source manifest.
It is intended to build independently from the private Plectis workspace.

## Build

```sh
lake exe cache get
lake build
```

## Boundary

The export is a pinned snapshot. A newer private frontier does not change this repo until a new export is built, validated, and tagged.
This snapshot does not claim to solve Erdos #249 or Erdos #257.

See `PLECTIS_INTEGRATION.json` for source hashes and Plectis integration metadata.
