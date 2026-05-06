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

## Running the harness

```bash
# load API key
set -a; . ./.env; set +a

# sanity: re-prove 1+1=2 in tests/one_plus_one
( cd tests/one_plus_one && alephprover prove OnePlusOne.lean one_plus_one --time-budget 5 --cost-budget 1 )

# smoke set: 5 test=true + 5 sampled main problems
python -m harness.run_eval --smoke --time-budget 10 --cost-budget 2

# one problem
python -m harness.run_eval --problem two_plus_two

# everything (after smoke + go-ahead)
python -m harness.run_eval --all --time-budget 30 --cost-budget 5

# show progress
python -m harness.status
```

Results land in `results/results.csv` (one row per hole). Per-problem raw logs
go to `results/raw/<problem-id>.json`. Re-runs skip already-succeeded problems
unless `--retry` is given.

## Scoring

lean-eval's official scorer (`comparator` + `landrun`) is **Linux-only**.
On macOS we use a relaxed local check:

1. Aleph's diff applied cleanly (`Proof applied successfully`)
2. `lake build` succeeds in `workspaces/<id>/` with no `declaration uses sorry` warning
3. `#print axioms Submission.<hole>` shows no `sorry` in the axiom list

A problem counts as solved iff all three pass for every hole. To run the
comparator-backed verdict, run the harness inside a Linux environment
(Docker/CI) with `landrun`, `lean4export`, and `comparator` on PATH, then
use `lake exe lean-eval run-eval --json` from inside `lean-eval/`.

## Budgets

`alephprover prove` defaults to 900 min and 50 credits per call. We use much
smaller budgets:

- sanity tests: `--time-budget 5 --cost-budget 1`
- smoke: `--time-budget 10 --cost-budget 2`
- full sweep: tuned after smoke results
