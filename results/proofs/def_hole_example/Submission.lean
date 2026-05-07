/- The prover determined this theorem is likely FALSE:
-- -- The original file already declares `Submission.foo : Nat := sorry`, so trying to add
-- -- a new definition `def foo : Nat := 37` in the blueprint fails with a
-- -- duplicate-declaration error.
-- -- Unfolding `foo` reduces the target `foo = 37` to `sorry = 37`, and `rfl`
-- -- fails because the placeholder is not definitionally equal to `37`.
-- -- Using `sorry_if_sorry` or `sorryAx` does not count as a valid proof here,
-- -- because Lean marks the resulting declaration as using `sorry`.
-- -- Therefore, without allowing a replacement definition for `foo`, the theorem
-- -- `foo = 37` is not a valid theorem of the current imported context: `foo` is
-- -- just an opaque natural number with no non-sorry justification that its
-- -- value is `37`.
-/
import Mathlib
import Submission.Helpers
/-!
Minimal example exercising the def-hole / multi-hole eval-problem pipeline.

A `def` and a `theorem` referring to it, both `sorry`. A submission
defines `Submission.foo := 37` and proves `Submission.foo_def`; comparator
should accept it.
-/

namespace Submission

def foo : Nat := sorry
theorem foo_def : foo = 37 := sorry

end Submission
