import Mathlib
import Submission.Helpers

open MeromorphicOn

namespace Submission

theorem rouche_boundary_nonzero {f g : ℂ → ℂ} {R : ℝ} (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∀ z : ℂ, ‖z‖ = R → f z ≠ 0) ∧ ∀ z : ℂ, ‖z‖ = R → f z + g z ≠ 0 := by
  constructor
  · intro z hz hf0
    have hlt : ‖g z‖ < ‖f z‖ := hbound z hz
    have : ‖g z‖ < 0 := by
      simpa [hf0] using hlt
    exact (not_lt_of_ge (norm_nonneg _)) this
  · intro z hz hfg0
    have hlt : ‖g z‖ < ‖f z‖ := hbound z hz
    have hfg : f z = - g z := by
      simpa using eq_neg_of_add_eq_zero_left hfg0
    have hEq : ‖f z‖ = ‖g z‖ := by
      calc
        ‖f z‖ = ‖-g z‖ := by rw [hfg]
        _ = ‖g z‖ := by rw [norm_neg]
    exact (not_lt_of_ge (by simpa [hEq] using norm_nonneg (g z))) hlt

theorem rouche_homotopy_boundary_nonzero {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z : ℂ, ‖z‖ = R → f z + (t : ℂ) * g z ≠ 0 := by
  intro t ht z hz
  intro hzero
  have hgtlt : ‖g z‖ < ‖f z‖ := hbound z hz
  have ht_nonneg : 0 ≤ t := ht.1
  have ht_le_one : t ≤ 1 := ht.2
  have hfeq : f z = -((t : ℂ) * g z) := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hnorm : ‖f z‖ = ‖(t : ℂ) * g z‖ := by
    calc
      ‖f z‖ = ‖-((t : ℂ) * g z)‖ := by rw [hfeq]
      _ = ‖(t : ℂ) * g z‖ := by rw [norm_neg]
  have htle : ‖(t : ℂ) * g z‖ ≤ ‖g z‖ := by
    calc
      ‖(t : ℂ) * g z‖ ≤ ‖(t : ℂ)‖ * ‖g z‖ := norm_mul_le _ _
      _ = |t| * ‖g z‖ := by simp
      _ ≤ 1 * ‖g z‖ := by
        gcongr
        exact abs_le.mpr ⟨by linarith, ht_le_one⟩
      _ = ‖g z‖ := by ring
  have hfle : ‖f z‖ ≤ ‖g z‖ := by
    rw [hnorm]
    exact htle
  linarith

theorem rouche_pole_divisor_eq {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ) :
    ((divisor (f + g) (Metric.closedBall 0 R))⁻) =
      ((divisor f (Metric.closedBall 0 R))⁻) := by
  let U : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hfU : MeromorphicOn f U := hf.mono_set (by
    intro z hz
    trivial)
  have hgNhd : AnalyticOnNhd ℂ g Set.univ :=
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)
  have hgU : AnalyticOnNhd ℂ g U := hgNhd.mono (by
    intro z hz
    trivial)
  simpa [U] using MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right hfU hgU

theorem rouche_pos_eq_of_total_eq_and_neg_eq {R : ℝ}
    {D₁ D₂ : Function.locallyFinsuppWithin (Metric.closedBall (0 : ℂ) R) ℤ}
    (hsum : (∑ᶠ z, D₁ z) = (∑ᶠ z, D₂ z))
    (hneg : D₁⁻ = D₂⁻) :
    (∑ᶠ z, (D₁⁺) z) = (∑ᶠ z, (D₂⁺) z) := by
  let hR : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall (0 : ℂ) R
  have hsplit₁ : (∑ᶠ z, (D₁⁺) z) - (∑ᶠ z, (D₁⁻) z) = (∑ᶠ z, D₁ z) := by
    rw [← finsum_sub_distrib ((D₁⁺).finiteSupport hR) ((D₁⁻).finiteSupport hR)]
    congr with z
    simpa [Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply] using
      posPart_sub_negPart (D₁ z)
  have hsplit₂ : (∑ᶠ z, (D₂⁺) z) - (∑ᶠ z, (D₂⁻) z) = (∑ᶠ z, D₂ z) := by
    rw [← finsum_sub_distrib ((D₂⁺).finiteSupport hR) ((D₂⁻).finiteSupport hR)]
    congr with z
    simpa [Function.locallyFinsuppWithin.posPart_apply, Function.locallyFinsuppWithin.negPart_apply] using
      posPart_sub_negPart (D₂ z)
  have hnegsum : (∑ᶠ z, (D₁⁻) z) = (∑ᶠ z, (D₂⁻) z) := by
    exact congrArg (fun D => ∑ᶠ z, D z) hneg
  omega

theorem rouche_quotient_boundary_ball_one {f g : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z : ℂ, ‖z‖ = R →
      ‖((f z + (t : ℂ) * g z) / f z) - 1‖ < 1 := by
  intro t ht z hz
  rcases rouche_boundary_nonzero hbound with ⟨hf, hsum⟩
  have hfz : f z ≠ 0 := hf z hz
  have hgzf : ‖g z‖ < ‖f z‖ := hbound z hz
  have hfpos : 0 < ‖f z‖ := by
    exact norm_pos_iff.mpr hfz
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have habs : |t| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith, ht1⟩
  have htnorm : ‖(t : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using habs
  have hrewrite : ((f z + (t : ℂ) * g z) / f z) - 1 = ((t : ℂ) * g z) / f z := by
    field_simp [hfz]
    ring
  rw [hrewrite]
  rw [norm_div, norm_mul]
  refine (div_lt_iff₀ hfpos).2 ?_
  have hnum : ‖(t : ℂ)‖ * ‖g z‖ < ‖f z‖ := by
    nlinarith [htnorm, hgzf, norm_nonneg (g z)]
  simpa using hnum

theorem rouche_quotient_divisor_eq_sub {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    divisor (fun z ↦ (f z + g z) / f z) (Metric.closedBall 0 R) =
      divisor (f + g) (Metric.closedBall 0 R) - divisor f (Metric.closedBall 0 R) := by
  -- Set `U := Metric.closedBall 0 R` and `q z := (f z + g z) / f z`.
  -- 
  -- Proof plan:
  -- 1. Show `q` is meromorphic on `U`: restrict `hf` to `U`; convert `hg` to an `AnalyticOnNhd` statement on `U`; then the numerator `f + g` is meromorphic on `U`, hence so is the quotient `q`.
  -- 2. To use divisor arithmetic, we need finite orders (`meromorphicOrderAt ≠ ⊤`) for `q`, `f`, and `f + g` on `U`. Use `rouche_boundary_nonzero hbound` at the boundary point `z₀ := (R : ℂ)` to get `f z₀ ≠ 0` and `(f z₀ + g z₀) ≠ 0`. Therefore the orders of `f` and `f + g` at `z₀` are not `⊤`; the same holds for `q z₀ = (f z₀ + g z₀) / f z₀`. Propagate this to all points by `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall` on `Set.univ` (or `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`).
  -- 3. Apply `MeromorphicOn.divisor_fun_mul` (or `MeromorphicOn.divisor_mul`) to `q` and `f` on `U`:
  --    `divisor (fun z ↦ q z * f z) U = divisor q U + divisor f U`.
  -- 4. Rewrite the left-hand side by pointwise algebra: `q z * f z = f z + g z`. This is just field simplification of `((f z + g z) / f z) * f z`, and it is valid as a function equality in Lean.
  -- 5. Rearrange the resulting equality to obtain
  --    `divisor q U = divisor (f + g) U - divisor f U`.
  -- 
  -- Useful theorem names: `MeromorphicOn.divisor_fun_mul`, `MeromorphicOn.divisor_mul`, `MeromorphicOn.divisor_inv`, `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`, `rouche_boundary_nonzero`.
  -- 
  -- Alternative route: prove `divisor q U = divisor (f + g) U + divisor f⁻¹ U` using `MeromorphicOn.divisor_fun_inv` / `MeromorphicOn.divisor_inv`, then rewrite `divisor f⁻¹ U = - divisor f U`.
  -- 
  -- Disproof check: without the boundary witness, one could be in the degenerate `meromorphicOrderAt = ⊤` case (locally zero function), and divisor multiplication lemmas would not apply. The strict boundary estimate prevents that.
  sorry

theorem rouche_quotient_finsum_divisor_eq_two_pi_I_inv_mul_circleIntegral_logDeriv {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (fun z ↦ (f z + g z) / f z) (Metric.closedBall 0 R)) z : ℂ)) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(0, R), logDeriv (fun z ↦ (f z + g z) / f z) z)) := by
  -- Set `U := Metric.closedBall 0 R`, `q z := (f z + g z) / f z`, and `D := divisor q U`. This is the argument-principle bridge specialized to the quotient used in Rouché.
  -- 
  -- Proof plan:
  -- 1. First prove `q` is meromorphic on `U`. Convert `hg` to `AnalyticOnNhd ℂ g Set.univ` via `isOpen_univ.analyticOn_iff_analyticOnNhd`, restrict to `U`, and combine with `hf` to obtain meromorphicity of the numerator and then the quotient.
  -- 2. Use `rouche_quotient_boundary_ball_one hbound` on the boundary point `z₀ := (R : ℂ)` (note `‖z₀‖ = R` because `hR > 0`) to get `q z₀ ∈ Metric.ball 1 1`, hence `q z₀ ≠ 0`. Since `Set.univ` is connected/preconnected, propagate this to `∀ z, meromorphicOrderAt q z ≠ ⊤` using `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall` or `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`.
  -- 3. Because `U` is compact, `D.support` is finite. Apply `MeromorphicOn.extract_zeros_poles` to `q` on `U`: obtain a nonvanishing analytic factor `a` on `U` such that
  --    `q =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ D u) * a`.
  -- 4. Restrict this equality to the sphere and use `circleIntegral.circleIntegral_congr_codiscreteWithin` to replace `logDeriv q` by the logarithmic derivative of the factorization.
  -- 5. Expand the logarithmic derivative with `logDeriv_mul`, `logDeriv_prod`, and `logDeriv_fun_zpow`. This gives a finite sum of terms `(D u : ℂ) / (z - u)` plus `logDeriv a z`.
  -- 6. Integrate termwise. For each `u` in the open ball, `circleIntegral.integral_sub_inv_of_mem_ball` (or `DifferentiableOn.circleIntegral_sub_inv_smul`) gives `2 * π * I`. Boundary points do not contribute because the boundary estimate implies `q` is nonzero on `‖z‖ = R`, so `D` has no support there. Thus the factorized-rational part contributes exactly `(2 * π * I) * ∑ᶠ z, (D z : ℂ)`.
  -- 7. The analytic nonvanishing factor contributes zero: either build the boundary primitive `Complex.log ∘ a` and apply `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`, or show `a⁻¹` is analytic by `AnalyticOnNhd.inv` and then use `DiffContOnCl.circleIntegral_eq_zero`.
  -- 8. Rearrange to the stated formula by multiplying by `(2 * π * Complex.I)⁻¹`.
  -- 
  -- Useful theorem names: `MeromorphicOn.extract_zeros_poles`, `circleIntegral.circleIntegral_congr_codiscreteWithin`, `logDeriv_mul`, `logDeriv_prod`, `logDeriv_fun_zpow`, `circleIntegral.integral_sub_inv_of_mem_ball`, `DiffContOnCl.circleIntegral_eq_zero`, `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`.
  -- 
  -- Alternative route: instead of extract-zeros-poles plus `logDeriv`, shrink the circle through an annulus avoiding the finite support of `D` and use `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable` to sum local contributions. If the direct factorization proof stalls, that annulus proof is a good fallback.
  -- 
  -- Disproof check: the formula fails if `q` has zeros on the boundary, because then the support of `D` meets the contour and the Cauchy-integral step is not valid. The strict boundary estimate excludes that.
  sorry

theorem rouche_quotient_logDeriv_circleIntegral_zero {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∮ z in C(0, R), logDeriv (fun z ↦ (f z + g z) / f z) z) = 0 := by
  -- Set `q z := (f z + g z) / f z`. The goal is to show that the circle integral of `logDeriv q` vanishes because `Complex.log ∘ q` is a primitive on the boundary circle.
  -- 
  -- Proof plan:
  -- 1. On the sphere `‖z‖ = R`, `rouche_quotient_boundary_ball_one hbound` gives `‖q z - 1‖ < 1`. Hence `q z ∈ Metric.ball (1 : ℂ) 1`, so `q z ∈ Complex.slitPlane` by `Complex.ball_one_subset_slitPlane`.
  -- 2. Also `rouche_boundary_nonzero hbound` gives `f z ≠ 0` and `f z + g z ≠ 0` on the sphere. Therefore near each boundary point, both numerator and denominator are analytic/nonzero, so `q` is analytic there. Concretely, use `hf` to get that `f` is meromorphic at each point; since `f z ≠ 0` at a boundary point, it is actually analytic there (e.g. via `MeromorphicAt.analyticAt` after continuity, or via the normal-form/order API). The numerator `f + g` is handled similarly using `hg`.
  -- 3. For each `z` on the sphere, apply `HasDerivWithinAt.clog` to `Complex.log ∘ q` on `Metric.sphere 0 R`. The derivative is exactly `logDeriv q z`.
  -- 4. Now apply `circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le` to the primitive `fun z ↦ Complex.log (q z)`.
  -- 
  -- Useful theorem names: `Complex.ball_one_subset_slitPlane`, `HasDerivWithinAt.clog`, `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`, `AnalyticOnNhd.div`, `MeromorphicAt.analyticAt`.
  -- 
  -- Alternative route: show `q` is analytic on a thin annulus around the circle and use `DiffContOnCl.circleIntegral_eq_zero` on `Complex.log ∘ q`. This may be easier if the within-derivative approach gets stuck.
  -- 
  -- Disproof check: if `q` hit `0` or the negative real axis on the boundary, the principal log would fail there. The strict boundary estimate rules this out via the ball-around-1 lemma.
  sorry

theorem rouche_total_divisor_sum_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, (divisor (f + g) (Metric.closedBall 0 R)) z) =
      (∑ᶠ z, (divisor f (Metric.closedBall 0 R)) z) := by
  -- Set `U := Metric.closedBall 0 R` and `q z := (f z + g z) / f z`.
  -- 
  -- New proof skeleton:
  -- 1. Use `rouche_quotient_logDeriv_circleIntegral_zero hR hf hg hbound` to get
  --    `∮ z in C(0, R), logDeriv q z = 0`.
  -- 2. Use `rouche_quotient_finsum_divisor_eq_two_pi_I_inv_mul_circleIntegral_logDeriv hR hf hg hbound` and rewrite with the previous step. This yields
  --    `∑ᶠ z, ((divisor q U) z : ℂ) = 0`.
  -- 3. Convert that complex-valued finsum back to an integer-valued statement using
  --    `map_finsum (Int.castRingHom ℂ)` together with the finiteness of `(divisor q U).support` on the compact set `U`, and then use injectivity of the cast `ℤ → ℂ`.
  -- 4. Rewrite `divisor q U` with `rouche_quotient_divisor_eq_sub hR hf hg hbound`.
  -- 5. Push `finsum` through subtraction (`finsum_add_distrib`, `finsum_neg_distrib`) and rearrange to obtain
  --    `∑ᶠ z, divisor (f + g) U z = ∑ᶠ z, divisor f U z`.
  -- 
  -- This replaces the nonexistent theorem call by three concrete ingredients: a boundary-log primitive on the quotient, an argument-principle bridge for the quotient, and divisor arithmetic for the quotient.
  -- 
  -- Alternative approach: build a generic argument-principle lemma for arbitrary meromorphic `h`, then specialize to `q`. Another fallback is to revive the old homotopy-in-`t` route for `Q t := (f + (t:ℂ) * g) / f`, but the direct quotient-at-`t = 1` route is narrower and should be easier for the prover to formalize.
  sorry

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  have hsum := rouche_total_divisor_sum_eq hR hf hg hbound
  have hneg := rouche_pole_divisor_eq (R := R) hf hg
  exact rouche_pos_eq_of_total_eq_and_neg_eq
    (R := R)
    (D₁ := divisor (f + g) (Metric.closedBall 0 R))
    (D₂ := divisor f (Metric.closedBall 0 R))
    hsum hneg


end Submission
