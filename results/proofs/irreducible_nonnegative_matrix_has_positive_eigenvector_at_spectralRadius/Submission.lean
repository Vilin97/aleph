/- The prover determined this theorem is likely FALSE:
-- -- Counterexample showing the target theorem is false as stated.
-- -- Take the index type `n := PEmpty` (equivalently `Fin 0`), which has
-- -- `Fintype` and `DecidableEq` instances. Let `A : Matrix n n ℝ` be the
-- -- unique empty matrix. Then `A.IsIrreducible` holds vacuously: its `nonneg`
-- -- field is `∀ i j : n, 0 ≤ A i j`, and its `connected` field is
-- -- `∀ i j : n, ∃ p : Quiver.Path i j, 0 < p.length`; both are trivially true
-- -- because there are no `i, j : n`.
-- --
-- -- However, the conclusion fails. For an empty index type, every vector
-- -- `v : n → ℝ` is equal to `0` by `funext (fun i => (PEmpty.elim i))`, so
-- -- there is no nonzero vector at all. But `Module.End.HasEigenvector ... v`
-- -- means `v` lies in the eigenspace and also satisfies `v ≠ 0` (see
-- -- `Module.End.hasEigenvector_iff` / the definition of `HasEigenvector`).
-- -- Therefore no such `v` can exist. So the theorem is false unless one adds
-- -- an extra assumption like `[Nonempty n]`.
-/
import Mathlib
import Submission.Helpers

open scoped NNReal

namespace Submission

theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) := by
  sorry

end Submission
