# Aleph × lean-eval results

Final tally over the lean-eval benchmark (57 problems total, 4 mixed-hole excluded
upstream → 53 theorem-only attempts + 2 mixed-hole problems left at sorry).

## Score

**14 / 55 problems solved end-to-end (25%).**

A "solved" problem means: Aleph's diff applied cleanly, `lake build` succeeded
in the workspace, no `declaration uses sorry` warning came from `Submission.lean`
or `Submission/`, and `#print axioms Submission.<hole>` listed only the standard
Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).

`comparator` (lean-eval's official sandboxed scorer) is Linux-only and
unavailable on this Mac, so this is a relaxed but axiom-aware local verdict.

## Wins (in chronological order)

### Sanity tests
- `1 + 1 = 2` (out-of-tree, `tests/one_plus_one`) — `rfl`
- `two_plus_two_eq_four` — `rfl`

### Smoke run (`harness/run_eval.py --smoke`)
| problem | budget | wall | request |
|---|---|---|---|
| `ci_regenerate_main_check` | 10m / 2c | 7 min | `4cec49bb-a6ac-40ac-af92-a019378e185a` |
| `list_append_singleton_length` | 10m / 2c | 9 min | `bc33faaa-4dd7-495f-86d5-ba677971bb39` |

### Hard problems (smoke at default budget)
| problem | cost | wall | request |
|---|---|---|---|
| `finite_graph_ramsey_theorem` | 14.3c | 71 min | `093a5d1e-1856-4ee8-b0ff-3451855d3c00` |
| `oppenheim_inequality` | 27.9c | 67 min | `d05df5d3-0e05-4819-bf3a-f4e59f225ed3` |
| `cyclotomic_integer_house_le_two` | 34.9c | 82 min | `54910e96-3152-40d1-b56b-41970f43da2a` |

### Full sweep (`harness/run_full.py`, 45 theorem-only problems)
| problem | cost | wall | request |
|---|---|---|---|
| `bvp_comparison` | 1.4c | 25 min | `3da936bb` |
| `sturm_separation` | 5.1c | 30 min | `d2905796` |
| `posSemidef_map_exp` | 13.3c | 35 min | `df460175` |
| `brauer_character_in_cyclotomic` | 6.4c | 34 min | `18468cd7` |
| `dirichlet_eigenvalues_eq_nat_sq` | — | 66 min | `3733515c` |
| `cubic_decay_asymptotic` | — | 77 min | `0d588799` |
| `vonNeumann_doubleCommutant_tfae` | — | 82 min | `7471869e` |
| `mulCayley_connected_iff_closure_eq_top` | — | 19 min | `85bbf699` |

## Failure modes (43 fails)

| mode | count | meaning |
|---|---|---|
| `no patch applied` | 16 | Aleph server reported `failed` cleanly without sending a patch |
| `partial sorry` | 14 | Patch applied, build OK, but a `sorry` remained somewhere in `Submission` |
| `build failed` | 13 | Patch applied but the resulting `Submission.lean` doesn't typecheck — typically a hallucinated identifier or a name collision (e.g. `_root_.gleason_theorem_finite` resolving to the trusted-but-sorry stub) |

## Notable observations

- **Aleph is meaningfully faster than Mathlib search alone**: it solved several
  problems by chaining 5–15 sub-lemmas, not just looking up named results.
- **It hallucinates plausible-looking reuses**: `gleason_theorem_finite`
  produced `exact _root_.gleason_theorem_finite hdim f`, which typechecks
  because Challenge.lean has a same-named stub-with-sorry — yielding a proof
  that depends transitively on `sorry`. Build catches this; comparator
  presumably catches it via the axiom check too.
- **Server-side budget is soft**: the 10-min budget runs were closer to 7-15
  min wall.
- **CLI hardcoded poll timeout (~28 min)** is independent of `--time-budget`
  and bites long requests. The harness recovers via `alephprover status` +
  `download` (`harness/recover.py`).
- **Active-job cap**: ~43 simultaneous active requests appears to be the
  per-account cap. We hit HTTP 429 on submit #44/45 and again on retries
  until existing jobs cleared.
- **Per-workspace mathlib clones are huge.** Switched to a shared
  `lean-eval/.shared-lake/packages` symlinked into each workspace's
  `.lake/packages` — saves ~7 GB per problem, makes `lake build` ~20 s instead
  of ~5 min.

## Reproducing

```bash
# CLI + auth
uv tool install alephprover
cp .env.example .env  # fill in PROVER_API_KEY
set -a; . ./.env; set +a

# lean-eval (submodule)
git submodule update --init --recursive

# (one-time) populate the shared mathlib donor
cd lean-eval
lake exe lean-eval start-problem two_plus_two
cd workspaces/two_plus_two
lake update
lake exe cache get
lake build  # forces deps to build
mv .lake/packages ../../.shared-lake/packages
ln -s "$PWD/../../.shared-lake/packages" .lake/packages

# smoke (5 trivial + 5 sampled main)
python -m harness.run_eval --smoke

# the rest
python -m harness.run_full

# show progress
python -m harness.status
```
