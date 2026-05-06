# aleph

Testing the [Aleph Prover](https://alephprover.logicalintelligence.com) on
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval).

## Plan

1. **Sanity #1** — prove `1 + 1 = 2` on a one-file Lean project. Confirms API key,
   project upload, and `git apply` of the returned diff all work.
2. **Sanity #2** — solve the `two_plus_two` problem from `lean-eval` end-to-end,
   including `lake exe lean-eval run-eval` accepting the submission.
3. **Full sweep** — Python harness iterates every problem in
   `manifests/problems.toml`, generates each workspace, calls `alephprover prove`
   on the holes, and records pass/fail + cost in `results/`.

## Setup

```bash
# Aleph CLI
uv tool install alephprover     # or: pipx install alephprover

# Secrets
cp .env.example .env             # then edit; .env is gitignored
set -a; . ./.env; set +a         # export PROVER_API_KEY for the CLI

# lean-eval (cloned as a sibling submodule on first run)
git submodule update --init --recursive
```

`elan` / `lake` / `lean` must be on `$PATH`.

## Layout

```
tests/one_plus_one/   tiny Lean project for sanity #1
lean-eval/            git submodule of leanprover/lean-eval (sanity #2 + full)
harness/              Python harness driving alephprover over lean-eval
results/              CSV + per-problem logs (gitignored raw/, JSON summary tracked)
```

## Notes on budgets

`alephprover prove` defaults to 900 min and 50 credits. We pass small budgets
for the sanity tests (`--time-budget 5 --cost-budget 1`) and tune for the full
sweep based on what the smoke test shows.
