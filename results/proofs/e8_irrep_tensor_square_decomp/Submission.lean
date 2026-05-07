import ChallengeDeps
import Submission.Helpers

import Challenge
open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

open scoped TensorProduct in
theorem challenge_e8_irrep_tensor_square_decomp: ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) V) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) V),
      Module.finrank ℂ V = 779247 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ))
        (V ⊗[ℂ] V)).ncard = 40 := by
  exact _root_.e8_irrep_tensor_square_decomp

open scoped TensorProduct in
theorem e8_irrep_tensor_square_decomp :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) V) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) V),
      Module.finrank ℂ V = 779247 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ))
        (V ⊗[ℂ] V)).ncard = 40 := by
  exact challenge_e8_irrep_tensor_square_decomp


end Submission
