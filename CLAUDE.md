<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Claude Code entry

@AGENTS.md

`AGENTS.md` is the shared project instruction and authority-routing surface.
This file carries Claude-specific deltas only.

- Start with the bounded `docs/orientation.json` capsule named by the imported
  instructions; expand one claim or route at a time.
- Treat auto-memory, plans, subagents, and model output as working aids, never
  as proof, claim, source-identity, or publication authority.
- Keep verification loops scoped to the selected change class. Use the public
  checks in `AGENTS.md`, and run `lake build` after Lean changes.
- This is a self-contained public repository, not an entrypoint into any
  private development system. Do not infer private paths, claims, or machinery.
