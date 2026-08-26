# Documentation map

The public reading path is:

1. [repository overview](../README.md) — scope and main theorem;
2. [blueprint and dependency graph](../BLUEPRINT.md) — proof architecture;
3. [paper → Lean index](PAPER_TO_LEAN.md) — exact numbered-result lookup;
4. the linked Lean declaration and its imports.

## Reader references

| Document | Purpose |
|---|---|
| [PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) | exact paper number ↔ checked public Lean declaration |
| [PAPER_MAP.md](PAPER_MAP.md) | stable blueprint node IDs and direct dependencies |
| [R324_PAPER_PROOF.md](R324_PAPER_PROOF.md) | detailed correspondence for paper §4.2 and bound (3.24) |

## Mathematical and implementation references

| Document | Purpose |
|---|---|
| [DESIGN.md](DESIGN.md) | formalization scope, normalization, architecture, and trust policy |
| [PAPER_NOTES.md](PAPER_NOTES.md) | explicit formalization conventions for a few local arXiv v1 passages |

## Generated reference

[PAPER_INDEX.md](PAPER_INDEX.md) is a generated coarse inventory of modules
carrying a `Paper:` tag. It is useful for reverse lookup, but
[PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) is the exact public crosswalk.
