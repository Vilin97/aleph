import ChallengeDeps
import Submission.Helpers

import Challenge
open Complex

namespace Submission

theorem bw_imported_challenge {n : ℕ} (hn : 0 < n) {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B) (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) : Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ ≥ -(BakerWustholz.C n (Module.finrank ℚ K) * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) * ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  exact _root_.bakerWustholz_linearForms_logs hn φ α hα b hB hbB hΛ_ne_zero

theorem bakerWustholz_linearForms_logs {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  exact bw_imported_challenge hn φ α hα b hB hbB hΛ_ne_zero


end Submission
