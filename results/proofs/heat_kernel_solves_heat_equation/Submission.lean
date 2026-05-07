import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.ODE
open Real MeasureTheory

namespace Submission

theorem gaussianExpectation_eq_standardGaussian (f : ℝ → ℝ) (x t : ℝ) (ht : 0 < t) :
  (∫ y : ℝ, f y ∂(ProbabilityTheory.gaussianReal x (Real.toNNReal (2 * t)))) =
    ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt (2 * t)
  let v : NNReal := ⟨c ^ 2, sq_nonneg c⟩
  have h2t_pos : 0 < 2 * t := by
    nlinarith
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 h2t_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hsq : c ^ 2 = 2 * t := by
    dsimp [c]
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ 2 * t by nlinarith))
  have hv : v = Real.toNNReal (2 * t) := by
    apply NNReal.eq
    dsimp [v]
    change c ^ 2 = max (2 * t) 0
    rw [max_eq_left (by nlinarith)]
    exact hsq
  have hmap_mul : Measure.map (fun z : ℝ => c * z) (ProbabilityTheory.gaussianReal 0 1) =
      ProbabilityTheory.gaussianReal 0 v := by
    dsimp [v]
    simpa only [mul_zero, mul_one] using
      (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) c)
  have hmap_add : Measure.map (fun z : ℝ => x + z) (ProbabilityTheory.gaussianReal 0 v) =
      ProbabilityTheory.gaussianReal x v := by
    simpa only [zero_add] using
      (ProbabilityTheory.gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) x)
  have hmap_affine : Measure.map (fun z : ℝ => x + c * z) (ProbabilityTheory.gaussianReal 0 1) =
      ProbabilityTheory.gaussianReal x v := by
    calc
      Measure.map (fun z : ℝ => x + c * z) (ProbabilityTheory.gaussianReal 0 1)
          = Measure.map (fun z : ℝ => x + z) (Measure.map (fun z : ℝ => c * z) (ProbabilityTheory.gaussianReal 0 1)) := by
              symm
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_const.add measurable_id
              · exact measurable_const.mul measurable_id
      _ = Measure.map (fun z : ℝ => x + z) (ProbabilityTheory.gaussianReal 0 v) := by
            rw [hmap_mul]
      _ = ProbabilityTheory.gaussianReal x v := hmap_add
  have h_emb : MeasurableEmbedding (fun z : ℝ => x + c * z) := by
    refine Measurable.measurableEmbedding ?_ ?_
    · exact measurable_const.add (measurable_const.mul measurable_id)
    · intro z₁ z₂ h
      have h' := congrArg (fun w : ℝ => w - x) h
      simp only [add_sub_cancel_left] at h'
      exact mul_left_cancel₀ hc_ne h'
  calc
    ∫ y : ℝ, f y ∂(ProbabilityTheory.gaussianReal x (Real.toNNReal (2 * t)))
        = ∫ y : ℝ, f y ∂(ProbabilityTheory.gaussianReal x v) := by rw [← hv]
    _ = ∫ y : ℝ, f y ∂(Measure.map (fun z : ℝ => x + c * z) (ProbabilityTheory.gaussianReal 0 1)) := by
          rw [← hmap_affine]
    _ = ∫ z : ℝ, f (x + c * z) ∂(ProbabilityTheory.gaussianReal 0 1) := by
          simpa using MeasurableEmbedding.integral_map h_emb f (μ := ProbabilityTheory.gaussianReal 0 1)
    _ = ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1) := by
          dsimp [c]

noncomputable def heatKernel (t x y : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-((x - y) ^ 2) / (4 * t))

theorem heatKernelExpArg_hasDerivAt_t (t x y : ℝ) (ht : 0 < t) :
  HasDerivAt (fun s => -((x - y) ^ 2) / (4 * s))
    (((x - y) ^ 2) / (4 * t ^ 2)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  convert ((hasDerivAt_inv ht0).const_mul (-((x - y) ^ 2 / 4))) using 1
  · ext s
    ring_nf
  · ring_nf

theorem heatKernelPrefactor_hasDerivAt_t (t : ℝ) (ht : 0 < t) :
  HasDerivAt (fun s => (Real.sqrt (4 * Real.pi * s))⁻¹)
    ((-(1 / (2 * t))) * (Real.sqrt (4 * Real.pi * t))⁻¹) t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have harg : 0 < 4 * Real.pi * t := by
    positivity
  have hsqrt : HasDerivAt (fun s => Real.sqrt (4 * Real.pi * s))
      (((1 / (2 * Real.sqrt (4 * Real.pi * t))) * (4 * Real.pi))) t := by
    have hlin : HasDerivAt (fun s => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id t).const_mul (4 * Real.pi))
    simpa [harg.ne'] using (Real.hasDerivAt_sqrt harg.ne').comp t hlin
  have hne : Real.sqrt (4 * Real.pi * t) ≠ 0 := by
    exact (Real.sqrt_pos.2 harg).ne'
  have hinv := hsqrt.inv hne
  convert hinv using 1
  field_simp [hne, Real.pi_ne_zero, ht.ne']
  have hnonneg' : 0 ≤ t * 4 * Real.pi := by
    positivity
  rw [Real.sq_sqrt hnonneg']

theorem heatKernel_hasDerivAt_t (t x y : ℝ) (ht : 0 < t) :
  HasDerivAt (fun s => heatKernel s x y)
    ((((x - y) ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t x y) t := by
  have h_pref := heatKernelPrefactor_hasDerivAt_t t ht
  have h_exp_arg := heatKernelExpArg_hasDerivAt_t t x y ht
  have h_exp : HasDerivAt (fun s => Real.exp (-((x - y) ^ 2) / (4 * s)))
      (Real.exp (-((x - y) ^ 2) / (4 * t)) * (((x - y) ^ 2) / (4 * t ^ 2))) t := by
    simpa using h_exp_arg.exp
  convert h_exp.mul h_pref using 1
  · funext s
    simp [heatKernel]
    rw [mul_comm]
  · simp [heatKernel]
    ring_nf

theorem heatKernel_hasDerivAt_x (t x y : ℝ) (ht : 0 < t) :
  HasDerivAt (fun z => heatKernel t z y) (((y - x) / (2 * t)) * heatKernel t x y) x := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hsub : HasDerivAt (fun z : ℝ => z - y) 1 x := by
    simpa using (hasDerivAt_id x).sub_const y
  have hsq : HasDerivAt (fun z : ℝ => (z - y) ^ 2) ((x - y) + (x - y)) x := by
    simpa [pow_two] using hsub.mul hsub
  have hsqneg : HasDerivAt (fun z : ℝ => -((z - y) ^ 2)) (-((x - y) + (x - y))) x := by
    simpa using hsq.neg
  have hexpArg : HasDerivAt (fun z : ℝ => -((z - y) ^ 2) / (4 * t)) (-(x - y) / (2 * t)) x := by
    convert hsqneg.mul_const ((4 * t)⁻¹) using 1
    field_simp [ht']
    ring_nf
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-((z - y) ^ 2) / (4 * t)))
      (Real.exp (-((x - y) ^ 2) / (4 * t)) * (-(x - y) / (2 * t))) x := by
    simpa using hexpArg.exp
  have hconst : HasDerivAt (fun z : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹) 0 x :=
    hasDerivAt_const x ((Real.sqrt (4 * Real.pi * t))⁻¹)
  simpa [heatKernel, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, div_eq_mul_inv] using hconst.mul hexp

theorem heatKernelXDeriv_hasDerivAt_x (t x y : ℝ) (ht : 0 < t) :
  HasDerivAt (fun z => ((y - z) / (2 * t)) * heatKernel t z y)
    ((((x - y) ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t x y) x := by
  have hfac : HasDerivAt (fun z => (y - z) / (2 * t)) (-(1 / (2 * t))) x := by
    simpa [div_eq_mul_inv, sub_eq_add_neg, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_const x y).sub (hasDerivAt_id x)).mul_const ((2 * t)⁻¹))
  have hk : HasDerivAt (fun z => heatKernel t z y) (((y - x) / (2 * t)) * heatKernel t x y) x := by
    simpa using heatKernel_hasDerivAt_x t x y ht
  have hprod := hfac.mul hk
  convert hprod using 1 <;> ring_nf


noncomputable def heatSolutionXDeriv (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ y : ℝ, (((y - x) / (2 * t)) * heatKernel t x y) * f y

noncomputable def heatSolutionXXDeriv (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ y : ℝ, ((((x - y) ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t x y) * f y

theorem heatSolution_eq_heatKernelIntegral (f : ℝ → ℝ) (t x : ℝ) (ht : 0 < t) :
  heatSolution f t x = ∫ y : ℝ, heatKernel t x y * f y := by
  unfold heatSolution
  rw [if_pos ht]
  have ha : 0 ≤ 4 * Real.pi * t := by
    positivity
  have hcoef : (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) = (Real.sqrt (4 * Real.pi * t))⁻¹ := by
    rw [Real.inv_rpow ha]
    rw [← Real.sqrt_eq_rpow]
  rw [hcoef]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with y
  simp [heatKernel, mul_assoc, mul_left_comm, mul_comm]

theorem heatSolution_eq_gaussianExpectation (f : ℝ → ℝ) (t x : ℝ) (ht : 0 < t) :
  heatSolution f t x = ∫ y : ℝ, f y ∂(ProbabilityTheory.gaussianReal x (Real.toNNReal (2 * t))) := by
  have hnonneg : 0 ≤ 2 * t := by
    positivity
  have hvar_ne : Real.toNNReal (2 * t) ≠ 0 := by
    exact ne_of_gt (by positivity)
  rw [heatSolution_eq_heatKernelIntegral f t x ht]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hvar_ne]
  refine integral_congr_ae ?_
  filter_upwards [] with y
  rw [ProbabilityTheory.gaussianPDFReal_def, Real.toNNReal_of_nonneg hnonneg]
  simp only [heatKernel, smul_eq_mul, NNReal.coe_mk]
  have hsq : (y - x) ^ 2 = (x - y) ^ 2 := by
    ring
  have harg : 2 * Real.pi * (2 * t) = 4 * Real.pi * t := by
    ring
  have hden : 2 * (2 * t) = 4 * t := by
    ring
  rw [hsq, harg, hden]


theorem heatSolution_t_domination_data (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t x : ℝ) (ht : 0 < t) :
  Integrable (fun y : ℝ => heatKernel t x y * f y) ∧
  ∃ bound : ℝ → ℝ, Integrable bound ∧
    (∀ᵐ y ∂volume, ∀ s ∈ Set.Icc (t / 2) (3 * t / 2),
      ‖(((((x - y) ^ 2) / (4 * s ^ 2) - 1 / (2 * s)) * heatKernel s x y) * f y)‖ ≤ bound y) := by
  -- This helper isolates the time-variable analytic data: base integrability at `t`, and a single integrable envelope for the time-derivative integrand on the compact positive-time neighborhood `Set.Icc (t / 2) (3 * t / 2)`.
  -- 
  -- Suggested proof.
  -- 1. Reuse exactly the same base integrability proof as in `heatSolution_x_domination_data`: identify the kernel with `ProbabilityTheory.gaussianPDFReal x (Real.toNNReal (2 * t))`, use `ProbabilityTheory.integrable_gaussianPDFReal`, and then `MeasureTheory.Integrable.mul_bdd` with `hf_cont.aestronglyMeasurable` and `hf_bdd`.
  -- 2. For `s ∈ Set.Icc (t / 2) (3 * t / 2)`, positivity of `ht` gives uniform bounds on `1 / (2 * s)` and `1 / (4 * s ^ 2)` in terms of constants depending only on `t`.
  -- 3. Since `s ≤ 3 * t / 2`, we have `1 / (4 * s) ≥ 1 / (6 * t)`, hence
  --    `Real.exp (-((x - y)^2) / (4 * s)) ≤ Real.exp (-((x - y)^2) / (6 * t))`.
  --    Combine this with `y^2 / 2 - x^2 ≤ (x - y)^2` to obtain a fixed Gaussian envelope in `y`, for example of the form `C0 * Real.exp (-(1 / (12 * t)) * y ^ 2)`; any smaller positive decay constant such as `1 / (16 * t)` is also fine.
  -- 4. The polynomial coefficient is at most `C1 * (y^2 + 1)`, so the whole integrand is bounded by `C * (y^2 + 1) * Real.exp (-(1 / (12 * t)) * y ^ 2)`.
  -- 5. Use `integrable_rpow_mul_exp_neg_mul_sq` with `s = 2` and `integrable_exp_neg_mul_sq` to prove integrability of that envelope.
  -- 
  -- Alternative route: it is fine to prove a slightly weaker but still integrable envelope; do not over-optimize the constants.
  -- 
  -- Disproof check: the compact positive-time neighborhood is essential. A global statement in `s` would be false because the coefficients blow up as `s ↓ 0`.
  sorry

theorem heatSolution_hasDerivAt_t (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) :
  ∀ x : ℝ, HasDerivAt (fun s => heatSolution f s x) (heatSolutionXXDeriv f t x) t := by
  -- Do **not** try to prove a global identity `(fun s => heatSolution f s x) = fun s => ∫ y, heatKernel s x y * f y`; it is false for `s ≤ 0`. Instead, prove the derivative of the integral map near the positive point `t`, and then transfer it to `heatSolution` using eventual equality.
  -- 
  -- Set `F s y := heatKernel s x y * f y` and `F' s y := (((((x - y) ^ 2) / (4 * s ^ 2) - 1 / (2 * s)) * heatKernel s x y) * f y)`. Use the neighborhood `Set.Icc (t / 2) (3 * t / 2)` and `Icc_mem_nhds (by linarith [ht]) (by linarith [ht])` to get `Set.Icc (t / 2) (3 * t / 2) ∈ nhds t`.
  -- 
  -- Unpack `heatSolution_t_domination_data f hf_cont hf_bdd t x ht` to obtain `Integrable (F t)` and an integrable dominating function `bound` valid on that interval. The measurability hypotheses are again by continuity in `y` for fixed `s`.
  -- 
  -- For the pointwise derivative hypothesis, if `s ∈ Set.Icc (t / 2) (3 * t / 2)` then `0 < s`, so apply `heatKernel_hasDerivAt_t s x y hspos` and multiply by the constant `f y`.
  -- 
  -- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to obtain a derivative for `fun s => ∫ y, F s y`. Then use `HasDerivAt.congr_of_eventuallyEq`: near `t`, we have `0 < s`, so `heatSolution_eq_heatKernelIntegral f s x hspos` gives eventual equality between `fun s => heatSolution f s x` and `fun s => ∫ y, F s y`. Finish with `simpa [heatSolutionXXDeriv, F']`.
  sorry

theorem heatSolution_x_domination_data (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t x : ℝ) (ht : 0 < t) :
  Integrable (fun y : ℝ => heatKernel t x y * f y) ∧
  ∃ bound : ℝ → ℝ, Integrable bound ∧
    (∀ᵐ y ∂volume, ∀ z ∈ Metric.closedBall x 1,
      ‖((((y - z) / (2 * t)) * heatKernel t z y) * f y)‖ ≤ bound y) := by
  -- This helper isolates exactly the analytic input needed for `heatSolution_hasDerivAt_x`: base integrability of the kernel product at `x`, and one neighborhood-uniform integrable bound for the `x`-derivative integrand on `Metric.closedBall x 1`.
  -- 
  -- Suggested proof.
  -- 1. Choose `M` from `hf_bdd`.
  -- 2. For the base integrability, first identify `fun y => heatKernel t x y` with `ProbabilityTheory.gaussianPDFReal x (Real.toNNReal (2 * t))` using `ProbabilityTheory.gaussianPDFReal_def`, `Real.toNNReal_of_nonneg`, and `(y - x)^2 = (x - y)^2`. Then use `ProbabilityTheory.integrable_gaussianPDFReal`. Finally apply `MeasureTheory.Integrable.mul_bdd` with `hf_cont.aestronglyMeasurable` and the a.e. bound coming from `hf_bdd` to obtain `Integrable (fun y => heatKernel t x y * f y)`.
  -- 3. For the domination, work with `z ∈ Metric.closedBall x 1`. Then `|z| ≤ |x| + 1` and `|y - z| ≤ |y| + |x| + 1`. Also use the quadratic estimate `y^2 / 2 - z^2 ≤ (y - z)^2`; after dividing by the positive quantity `4 * t`, this gives an exponential comparison of the form
  --    `Real.exp (-((z - y)^2) / (4 * t)) ≤ C0 * Real.exp (-(y^2) / (8 * t))`
  --    for a constant `C0` depending only on `x` and `t`.
  -- 4. Combine the polynomial factor `|(y - z) / (2 * t)|`, the kernel prefactor, and `|f y| ≤ M` to get an explicit envelope `bound y = C * (|y| + 1) * Real.exp (-(1 / (8 * t)) * y ^ 2)` (or any comparable envelope).
  -- 5. Show this `bound` is integrable by expanding `( |y| + 1 ) * exp (...)` and using `integrable_mul_exp_neg_mul_sq` and `integrable_exp_neg_mul_sq`.
  -- 
  -- Alternative route: prove the base integrability through Gaussian-measure moment facts and `ProbabilityTheory.integral_gaussianReal_eq_integral_smul`, but the explicit pdf rewrite is usually simpler.
  -- 
  -- Disproof check: boundedness of `f` is genuinely needed here; without it, the base integrability can fail.
  sorry

theorem heatSolution_hasDerivAt_x (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) :
  ∀ x : ℝ, HasDerivAt (fun z => heatSolution f t z) (heatSolutionXDeriv f t x) x := by
  -- Set `F z y := heatKernel t z y * f y` and `F' z y := (((y - z) / (2 * t)) * heatKernel t z y) * f y`. Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the neighborhood `Metric.closedBall x 1`; in code, use `Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)` and the filter `nhds x` (do not use the notation `𝓝` if the parser rejects it).
  -- 
  -- Unpack `heatSolution_x_domination_data f hf_cont hf_bdd t x ht` to obtain the needed `Integrable (F x)` and an integrable dominating function `bound` with the required a.e. bound on `Metric.closedBall x 1`. The measurability hypotheses are straightforward: for fixed `z`, both `y ↦ F z y` and `y ↦ F' x y` are continuous in `y`, hence `AEStronglyMeasurable` via `Continuous.aestronglyMeasurable`.
  -- 
  -- For the pointwise derivative hypothesis, use `heatKernel_hasDerivAt_x t z y ht` and then multiply by the constant `f y`; i.e. `HasDerivAt (fun z => heatKernel t z y * f y) ((((y - z) / (2 * t)) * heatKernel t z y) * f y) z` comes from `.mul_const (f y)`.
  -- 
  -- After applying `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, rewrite the integral map using `funext z; simpa [F] using heatSolution_eq_heatKernelIntegral f t z ht`, and rewrite the derivative value with `simpa [heatSolutionXDeriv, F']`.
  sorry

theorem heatSolution_xx_domination_data (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t x : ℝ) (ht : 0 < t) :
  Integrable (fun y : ℝ => (((y - x) / (2 * t)) * heatKernel t x y) * f y) ∧
  ∃ bound : ℝ → ℝ, Integrable bound ∧
    (∀ᵐ y ∂volume, ∀ z ∈ Metric.closedBall x 1,
      ‖(((((z - y) ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t z y) * f y)‖ ≤ bound y) := by
  -- This helper packages the two analytic facts needed for `heatSolutionXDeriv_hasDerivAt`: integrability of the first `x`-derivative integrand at the base point, and a neighborhood-uniform integrable envelope for the second `x`-derivative integrand.
  -- 
  -- Suggested proof.
  -- 1. Choose `M` from `hf_bdd`.
  -- 2. For the base integrability, bound
  --    `|(((y - x) / (2 * t)) * heatKernel t x y) * f y|`
  --    by `C * (|y| + 1) * Real.exp (-(1 / (8 * t)) * y ^ 2)` using the same closed-form Gaussian estimate as in `heatSolution_x_domination_data` together with `|y - x| ≤ |y| + |x|`.
  -- 3. For the neighborhood-uniform second-derivative bound, let `z ∈ Metric.closedBall x 1`. The polynomial coefficient
  --    `|((z - y)^2 / (4 * t^2) - 1 / (2 * t))|`
  --    is bounded by `C1 * (y^2 + 1)`. Combine this with the same exponential comparison
  --    `Real.exp (-((z - y)^2) / (4 * t)) ≤ C0 * Real.exp (-(y^2) / (8 * t))`
  --    to get an envelope of the form `C * (y^2 + 1) * Real.exp (-(1 / (8 * t)) * y ^ 2)`.
  -- 4. Show integrability of the `y^2` term using `integrable_rpow_mul_exp_neg_mul_sq` with `s = 2`, and of the constant term using `integrable_exp_neg_mul_sq`.
  -- 
  -- Alternative route: express the moments with respect to `ProbabilityTheory.gaussianReal x (Real.toNNReal (2 * t))`; `ProbabilityTheory.memLp_id_gaussianReal` plus `MeasureTheory.MemLp.integrable` can supply the first and second moments, and then `ProbabilityTheory.integral_gaussianReal_eq_integral_smul` converts back to volume. Use this only if the direct Gaussian estimate becomes algebraically annoying.
  -- 
  -- Disproof check: no derivative assumption on `f` is needed; the smoothing comes entirely from the kernel, so the statement remains plausible under mere bounded continuity.
  sorry

theorem heatSolutionXDeriv_hasDerivAt (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) :
  ∀ x : ℝ, HasDerivAt (fun z => heatSolutionXDeriv f t z) (heatSolutionXXDeriv f t x) x := by
  -- Use the integral definition of `heatSolutionXDeriv`. Set
  -- `F z y := (((y - z) / (2 * t)) * heatKernel t z y) * f y`
  -- and
  -- `F' z y := (((((z - y) ^ 2) / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t z y) * f y)`.
  -- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `Metric.closedBall x 1`, again using `Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)`.
  -- 
  -- Unpack `heatSolution_xx_domination_data f hf_cont hf_bdd t x ht` to obtain both the base integrability `Integrable (F x)` and an integrable dominating function `bound` valid for all `z ∈ Metric.closedBall x 1`. For the measurability hypotheses, note that for fixed `z`, the `y`-integrands are continuous, hence a.e. strongly measurable.
  -- 
  -- For the derivative hypothesis, use `heatKernelXDeriv_hasDerivAt_x t z y ht` and multiply the result by the constant `f y`. This matches the derivative integrand `F'` up to the harmless identity `(z - y)^2 = (y - z)^2`; if `simpa` does not close it immediately, finish with `ring_nf`.
  -- 
  -- After the dominated-differentiation theorem, the resulting derivative is exactly `heatSolutionXXDeriv f t x`; conclude with `simpa [heatSolutionXDeriv, heatSolutionXXDeriv, F, F']`.
  sorry

theorem heat_kernel_pde_part (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) : ∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t := by
  intro t ht x
  refine ⟨heatSolutionXDeriv f t, heatSolutionXXDeriv f t x, ?_⟩
  constructor
  · intro y
    exact heatSolution_hasDerivAt_x f hf_cont hf_bdd t ht y
  · constructor
    · exact heatSolutionXDeriv_hasDerivAt f hf_cont hf_bdd t ht x
    · exact heatSolution_hasDerivAt_t f hf_cont hf_bdd t ht x

theorem standardGaussian_tendsto_eval (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (x : ℝ) :
  Filter.Tendsto
    (fun t : ℝ => ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  let μ : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  rcases hf_bdd with ⟨M, hM⟩
  have hmeas :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        AEStronglyMeasurable (fun z : ℝ => f (x + Real.sqrt (2 * t) * z)) μ := by
    filter_upwards with t
    have hcont : Continuous (fun z : ℝ => f (x + Real.sqrt (2 * t) * z)) := by
      convert hf_cont.comp (continuous_const.add (continuous_const.mul continuous_id)) using 1
    exact hcont.aestronglyMeasurable
  have hbound :
      ∃ C, ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∀ᵐ z : ℝ ∂μ, ‖f (x + Real.sqrt (2 * t) * z)‖ ≤ C) := by
    refine ⟨M, ?_⟩
    filter_upwards with t
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hM (x + Real.sqrt (2 * t) * z)
  have hlim :
      ∀ᵐ z : ℝ ∂μ,
        Filter.Tendsto (fun t : ℝ => f (x + Real.sqrt (2 * t) * z))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
    filter_upwards with z
    have hsqrt : Continuous (fun t : ℝ => Real.sqrt (2 * t)) := by
      convert (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)) using 1
    have hcont_inner : Continuous (fun t : ℝ => x + Real.sqrt (2 * t) * z) := by
      convert (continuous_const.add (hsqrt.mul continuous_const)) using 1
    have hs :
        Filter.Tendsto (fun t : ℝ => x + Real.sqrt (2 * t) * z)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
      have hs0 :
          Filter.Tendsto (fun t : ℝ => x + Real.sqrt (2 * t) * z)
            (nhds (0 : ℝ)) (nhds (x + Real.sqrt (2 * 0) * z)) :=
        hcont_inner.continuousAt.tendsto
      exact (by simpa using hs0.mono_left nhdsWithin_le_nhds)
    exact (hf_cont.tendsto x).comp hs
  simpa [μ] using
    (MeasureTheory.tendsto_integral_filter_of_norm_le_const (μ := μ)
      (F := fun t z => f (x + Real.sqrt (2 * t) * z))
      (f := fun _ : ℝ => f x)
      hmeas hbound hlim)

theorem heat_kernel_initial_condition_part (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) : ∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  intro x
  have hEq :
      (fun t : ℝ => heatSolution f t x) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun t : ℝ => ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1)) := by
    change
      {t : ℝ |
          heatSolution f t x = ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1)} ∈
        nhdsWithin (0 : ℝ) (Set.Ioi 0)
    refine Filter.mem_of_superset (x := Set.Ioi (0 : ℝ)) ?_ ?_
    · show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)
      rw [nhdsWithin, Filter.mem_inf_iff]
      refine ⟨Set.univ, Filter.univ_mem, Set.Ioi 0, ?_, by ext t; simp⟩
      simp
    · intro t ht
      show heatSolution f t x = ∫ z : ℝ, f (x + Real.sqrt (2 * t) * z) ∂(ProbabilityTheory.gaussianReal 0 1)
      rw [heatSolution_eq_gaussianExpectation (f := f) (t := t) (x := x) ht,
        gaussianExpectation_eq_standardGaussian (f := f) (x := x) (t := t) ht]
  exact Filter.Tendsto.congr' hEq.symm (standardGaussian_tendsto_eval f hf_cont hf_bdd x)

theorem heat_kernel_solves_heat_equation (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x))) := by
  have hpde := heat_kernel_pde_part f hf_cont hf_bdd
  have hinit := heat_kernel_initial_condition_part f hf_cont hf_bdd
  exact ⟨hpde, hinit⟩


end Submission
