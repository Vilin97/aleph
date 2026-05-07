import ChallengeDeps
import Submission.Helpers

import Challenge
open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

open scoped TensorProduct in
theorem g2_irrep_tensor_square_decomp :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.g₂ ℂ) V) (_ : LieModule ℂ (LieAlgebra.g₂ ℂ) V),
      Module.finrank ℂ V = 64 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.g₂ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.g₂ ℂ))
        (V ⊗[ℂ] V)).ncard = 14 := by
  exact _root_.g2_irrep_tensor_square_decomp


end Submission
