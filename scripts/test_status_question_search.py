#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for ordinary-language open-problem status questions."""

from __future__ import annotations

from query_corpus import search_packet


CASES = (
    (
        "is Erdos 257 solved",
        "erdos257_half_story",
        "remaining_open.universal_257_all_infinite_supports",
    ),
    (
        "has Erdős 249 been settled",
        "erdos249_certificate_story",
        "remaining_open.erdos_249_irrationality",
    ),
)


def main() -> int:
    failures: list[str] = []
    for query, route_id, open_id in CASES:
        results = search_packet(query, 10)["results"]
        handles = [(row["kind"], row.get("id")) for row in results]
        expected_route = ("reading_route", route_id)
        expected_open = ("open_proposition", open_id)
        if not handles or handles[0] != expected_route:
            failures.append(
                f"{query!r}: first result {handles[:1]} is not {expected_route}"
            )
        if expected_open not in handles[:3]:
            failures.append(
                f"{query!r}: exact open proposition is absent from top three: "
                f"{handles[:3]}"
            )
    if failures:
        print(f"test_status_question_search: {len(failures)} failure(s)")
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_status_question_search: ordinary #249/#257 solved questions "
        "route to the exact programme and open proposition"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
