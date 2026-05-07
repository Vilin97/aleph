import ChallengeDeps
import Submission.Helpers

import Challenge
open LeanEval.KnotTheory

namespace Submission

theorem exists_nonisotopic_knots : ∃ K₁ K₂ : Knot, ¬ K₁.Isotopic K₂ := by
  exact _root_.exists_nonisotopic_knots


end Submission
