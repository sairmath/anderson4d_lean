# Contributing

Thank you for your interest in `anderson4d`.

This repository is a research formalization. Issues reporting reproducible
build failures, broken documentation links, statement-fidelity questions, or
small improvements are welcome. For a substantial mathematical or
architectural change, please open an issue before preparing a pull request so
that its scope and paper correspondence can be agreed first.

## Development setup

Use the Lean and mathlib versions pinned by `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`:

```sh
lake exe cache get
lake build
```

Before submitting a pull request, run the complete project gate:

```sh
bash scripts/release_gate.sh
```

## Contribution requirements

- Keep the advertised theorem conditional on `Anderson4D.Prop36Family`.
  The cited Gabriel--Rosati proposition is outside this repository and must
  remain an explicit premise rather than a project axiom.
- Do not add `sorry`, `admit`, project-specific axioms, or `native_decide`.
- Preserve the normalizations and public interfaces documented in
  `docs/DESIGN.md`.
- For a result corresponding to the paper, identify its paper number and
  update `docs/PAPER_TO_LEAN.md`, the blueprint source, and
  `blueprint/lean_decls` when applicable.
- Add the new Lean module to `Anderson4D.lean`; the release gate rejects
  tracked orphan modules.
- Keep generated files such as `.lake/` and `blueprint/web/` out of commits.

Pull requests should explain the mathematical change, list the declarations
affected, and include the verification commands that passed.

Unless explicitly stated otherwise, submitted contributions are licensed
under the repository's Apache License 2.0.
