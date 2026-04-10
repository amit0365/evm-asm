# Contributing to EvmAsm

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview
- [`AGENTS.md`](AGENTS.md) for build instructions, project structure, and proof guidance
- [`PLAN.md`](PLAN.md) for the current roadmap and task status

Before sending work for review:

- Run `lake build` and confirm it succeeds with no errors and no `sorry`.
- Avoid leaving `sorry` in finished work unless the change is explicitly meant to preserve partial progress.
- Do not add `set_option maxHeartbeats` or `set_option maxRecDepth` to files. These are configured globally in `lakefile.toml`. If a proof times out, restructure it (split into smaller lemmas, add intermediate `have` bindings) instead of raising limits.
- Do not use `native_decide` or `bv_decide`. All proofs must be kernel-checkable. Use `decide` for concrete decidable propositions, or `omega`/`simp`/`ext` for bitvector reasoning.

## Style Notes

- Keep imports at the top of the file.
- Follow the naming conventions and proof patterns documented in [`AGENTS.md`](AGENTS.md).
- Use `bv_addr` (not `bv_omega`) for address offset equalities — see the Build Performance section of `AGENTS.md`.

## Git Workflow

- Main branch: `main`
- Create feature branches for new work.
- Use meaningful commit messages.

## Licensing

This project is licensed under the MIT License. By contributing, you agree that your contributions are licensed under the same terms.
