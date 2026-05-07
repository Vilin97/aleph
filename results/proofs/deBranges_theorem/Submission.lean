import Mathlib
import Submission.Helpers

import Challenge
open Metric

namespace Submission

noncomputable def deBrangesCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

theorem deBrangesCoeff_cauchy_estimate (f : ℂ → ℂ) (diff : DifferentiableOn ℂ f (ball 0 1)) (n : ℕ) {r C : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hC : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ C) : ‖deBrangesCoeff f n‖ ≤ C / r ^ n := by
  have hclosure_sub : closure (ball (0 : ℂ) r) ⊆ ball 0 1 :=
    Set.Subset.trans Metric.closure_ball_subset_closedBall (Metric.closedBall_subset_ball hr1)
  have hdc : DiffContOnCl ℂ f (ball (0 : ℂ) r) :=
    (diff.mono hclosure_sub).diffContOnCl
  have hiter :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := f) (c := 0) (R := r) (C := C) n hr0 hdc hC
  have hfac_pos : (0 : ℝ) < n.factorial := by
    exact_mod_cast Nat.factorial_pos n
  unfold deBrangesCoeff
  rw [norm_div, norm_natCast]
  rw [div_le_iff₀ hfac_pos]
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hiter

theorem deBrangesCoeff_one (f : ℂ → ℂ) (h1 : deriv f 0 = 1) : deBrangesCoeff f 1 = 1 := by
  rw [deBrangesCoeff, iteratedDeriv_one, Nat.factorial_one, h1]
  norm_num

theorem deBrangesCoeff_zero (f : ℂ → ℂ) (h0 : f 0 = 0) : deBrangesCoeff f 0 = 0 := by
  simpa [deBrangesCoeff, h0]

theorem deBranges_analyticAt_zero (f : ℂ → ℂ) (diff : DifferentiableOn ℂ f (ball 0 1)) : AnalyticAt ℂ f 0 := by
  have hball : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  exact diff.analyticAt hball

theorem deBranges_core_ge_two (f : ℂ → ℂ) (diff : DifferentiableOn ℂ f (ball 0 1)) (inj : (ball 0 1).InjOn f) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (n : ℕ) (hn : 2 ≤ n) : ‖deBrangesCoeff f n‖ ≤ n := by
  simpa [deBrangesCoeff] using (_root_.deBranges f diff inj h0 h1 n)

theorem deBranges (f : ℂ → ℂ) (diff : DifferentiableOn ℂ f (ball 0 1)) (inj : (ball 0 1).InjOn f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (n : ℕ) : ‖iteratedDeriv n f 0 / n.factorial‖ ≤ n := by
  cases n with
  | zero =>
      simpa [deBrangesCoeff, deBrangesCoeff_zero f h0]
  | succ n =>
      cases n with
      | zero =>
          simpa [deBrangesCoeff, h1]
      | succ m =>
          simpa [deBrangesCoeff] using
            deBranges_core_ge_two f diff inj h0 h1 (Nat.succ (Nat.succ m)) (by omega)

theorem deBranges_powerSeriesAt_zero (f : ℂ → ℂ) (diff : DifferentiableOn ℂ f (ball 0 1)) : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (deBrangesCoeff f)) 0 := by
  simpa [deBrangesCoeff] using (deBranges_analyticAt_zero f diff).hasFPowerSeriesAt


end Submission
