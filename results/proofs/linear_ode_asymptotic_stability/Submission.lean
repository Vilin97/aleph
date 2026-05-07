import Mathlib
import Submission.Helpers

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
open scoped Matrix

namespace Submission

theorem complex_exp_mul_natPow_tendsto_zero_of_re_lt_zero (μ : ℂ) (k : ℕ) (hμ : μ.re < 0) : Filter.Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ k) Filter.atTop (nhds 0) := by
  -- Prove the complex-valued limit through the norm. Start with `rw [tendsto_zero_iff_norm_tendsto_zero]`. Set `b : ℝ := -μ.re`; then `hb : 0 < b` follows from `hμ`. Use `hlin : Filter.Tendsto (fun t : ℝ => b * t) Filter.atTop Filter.atTop`, and here the exact theorem name you want is `Filter.Tendsto.const_mul_atTop hb tendsto_id` (or the primed variant / `atTop_mul_const` if you rewrite the multiplication on the other side). Compose `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k` with `hlin`. For the norm identity, simplify to `Real.exp (μ.re * t) * |t| ^ k`; along `atTop`, restrict to `t ≥ 0` so that `|t| = t`. Then rewrite the expression as a constant multiple of `((b * t) ^ k) * Real.exp (-(b * t))` and apply `Filter.Tendsto.const_mul`. Do not use guessed theorem names like `tendsto_atTop_mono_mul_right`; the `Filter.Tendsto.const_mul_atTop` family is the right one.
  sorry

open scoped Matrix.Norms.L2Operator in
theorem complex_matrix_exp_mulVec_eq_exp_mul_polynomial_of_mem_maxGenEigenspace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ) (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) μ) : ∃ N : ℕ, ∃ coeff : Fin N → (Fin n → ℂ), ∀ t : ℝ, Matrix.mulVec (NormedSpace.exp (t • A)) v = Complex.exp ((t : ℂ) * μ) • ∑ i : Fin N, ((t : ℂ) ^ (i : ℕ)) • coeff i := by
  -- Let `f := Matrix.toLin' A` and `M := A - Matrix.scalar (Fin n) μ`. From `hv`, use `Module.End.mem_maxGenEigenspace` to obtain `k : ℕ` with `((f - μ • 1)^k) v = 0`. Rewrite this via `Matrix.toLin'_pow`, `Matrix.toLin'_apply`, and the explicit formula for `Matrix.scalar` to get `(M ^ k) *ᵥ v = 0`. Now `A = Matrix.scalar (Fin n) μ + M`, and the scalar matrix commutes with `M`, so for every real `t`, `Matrix.exp_add_of_commute` gives `exp (t • A) = exp (t • Matrix.scalar (Fin n) μ) * exp (t • M)`. Rewrite the scalar-matrix exponential using `Matrix.exp_diagonal` (after identifying `Matrix.scalar` with a constant diagonal matrix) to obtain a scalar factor `Complex.exp ((t : ℂ) * μ)`. For the nilpotent part on this single vector, avoid spectral-radius arguments: use `NormedSpace.exp_eq_tsum` on matrices, apply `Matrix.mulVec` to the series, and truncate the `tsum` to a finite `Finset.range k` sum because `(t • M)^i *ᵥ v = 0` for all `i ≥ k`. Collect the finitely many vectors into `coeff : Fin N → (Fin n → ℂ)` for some `N` (taking `N = k` is fine). Alternative route: restrict `f - μ • 1` to `Module.End.maxGenEigenspace f μ`, use `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` together with `IsNilpotent.exp_smul_eq_sum`, and then convert back to matrices via `Matrix.toLinAlgEquiv'` and `NormedSpace.map_exp`; but the direct series truncation on `v` is likely shorter.
  sorry

open scoped Matrix.Norms.L2Operator in
theorem complex_matrix_exp_mulVec_tendsto_zero_of_mem_maxGenEigenspace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ) (hv : v ∈ Module.End.maxGenEigenspace (Matrix.toLin' A) μ) (hμ : μ.re < 0) : Filter.Tendsto (fun t : ℝ => Matrix.mulVec (NormedSpace.exp (t • A)) v) Filter.atTop (nhds 0) := by
  rcases complex_matrix_exp_mulVec_eq_exp_mul_polynomial_of_mem_maxGenEigenspace n A μ v hv with ⟨N, coeff, hcoeff⟩
  have hsum : Filter.Tendsto
      (fun t : ℝ =>
        ∑ i ∈ (Finset.univ : Finset (Fin N)),
          (Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ (i : ℕ)) • coeff i)
      Filter.atTop (nhds 0) := by
    have hsum_finset :
        ∀ s : Finset (Fin N),
          Filter.Tendsto
            (fun t : ℝ =>
              ∑ i ∈ s,
                (Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ (i : ℕ)) • coeff i)
            Filter.atTop (nhds 0) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha hs
        have ha' : Filter.Tendsto
            (fun t : ℝ =>
              (Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ (a : ℕ)) • coeff a)
            Filter.atTop (nhds 0) := by
          simpa using
            (complex_exp_mul_natPow_tendsto_zero_of_re_lt_zero μ (a : ℕ) hμ).smul_const (coeff a)
        simpa [Finset.sum_insert, ha] using ha'.add hs
    exact hsum_finset Finset.univ
  simpa [hcoeff, Finset.smul_sum, smul_smul] using hsum

open scoped Matrix.Norms.L2Operator in
theorem complex_matrix_exp_mulVec_tendsto_zero_of_negative_real_part_eigenvalues (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0) (v : Fin n → ℂ) : Filter.Tendsto (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • A)) v‖) Filter.atTop (nhds 0) := by
  let f := Matrix.toLin' A
  have hv_top : v ∈ ⨆ μ : ℂ, Module.End.maxGenEigenspace f μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    simp only [Submodule.mem_top]
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hv_top
  rcases hv_top with ⟨g, hg_mem, hg_sum⟩
  have hcomp_tendsto : ∀ μ ∈ g.support,
      Filter.Tendsto (fun t : ℝ => Matrix.mulVec (NormedSpace.exp (t • A)) (g μ)) Filter.atTop (nhds 0) := by
    intro μ hμ
    have hgμ_nonzero : g μ ≠ 0 := by
      exact Finsupp.mem_support_iff.mp hμ
    have hgμ_mem_max : g μ ∈ Module.End.maxGenEigenspace f μ := hg_mem μ
    have hgμ_mem_gen : g μ ∈ Module.End.genEigenspace f μ (Module.finrank ℂ (Fin n → ℂ)) := by
      simpa [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] using hgμ_mem_max
    have hgeig : Module.End.HasGenEigenvalue f μ (Module.finrank ℂ (Fin n → ℂ)) := by
      rw [Module.End.hasGenEigenvalue_iff]
      rw [Submodule.ne_bot_iff]
      exact ⟨g μ, hgμ_mem_gen, hgμ_nonzero⟩
    have heig : Module.End.HasEigenvalue f μ :=
      Module.End.hasEigenvalue_of_hasGenEigenvalue hgeig
    have hμneg : μ.re < 0 := hA μ heig
    simpa [f] using
      complex_matrix_exp_mulVec_tendsto_zero_of_mem_maxGenEigenspace n A μ (g μ) hgμ_mem_max hμneg
  have hsum_tendsto_aux :
      ∀ s : Finset ℂ, s ⊆ g.support →
        Filter.Tendsto (fun t : ℝ => ∑ μ ∈ s, Matrix.mulVec (NormedSpace.exp (t • A)) (g μ))
          Filter.atTop (nhds 0) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        simpa using (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (0 : Fin n → ℂ)) Filter.atTop (nhds 0))
    | @insert μ s hμs ih =>
        have hs_insert : insert μ s ⊆ g.support := hs
        have hμ_in : μ ∈ g.support := hs_insert (by simp [hμs])
        have hs_sub : s ⊆ g.support := by
          intro ν hν
          exact hs_insert (by simp [hν, hμs])
        have hμt : Filter.Tendsto
            (fun t : ℝ => Matrix.mulVec (NormedSpace.exp (t • A)) (g μ))
            Filter.atTop (nhds 0) :=
          hcomp_tendsto μ hμ_in
        have hst : Filter.Tendsto
            (fun t : ℝ => ∑ ν ∈ s, Matrix.mulVec (NormedSpace.exp (t • A)) (g ν))
            Filter.atTop (nhds 0) := ih hs_sub
        simpa [Finset.sum_insert, hμs] using hμt.add hst
  have hsum_tendsto : Filter.Tendsto
      (fun t : ℝ => ∑ μ ∈ g.support, Matrix.mulVec (NormedSpace.exp (t • A)) (g μ))
      Filter.atTop (nhds 0) :=
    hsum_tendsto_aux g.support (by intro μ hμ; exact hμ)
  have hrewrite : (fun t : ℝ => Matrix.mulVec (NormedSpace.exp (t • A)) v)
      = fun t : ℝ => ∑ μ ∈ g.support, Matrix.mulVec (NormedSpace.exp (t • A)) (g μ) := by
    funext t
    rw [← hg_sum]
    simpa [Finsupp.sum, Matrix.mulVec_sum]
  have hvec : Filter.Tendsto (fun t : ℝ => Matrix.mulVec (NormedSpace.exp (t • A)) v) Filter.atTop (nhds 0) := by
    rw [hrewrite]
    exact hsum_tendsto
  simpa using hvec.norm

open scoped Matrix.Norms.L2Operator in
theorem matrix_powers_norm_tendsto_zero_of_spectralRadius_lt_one (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : spectralRadius ℂ B < 1) : Filter.Tendsto (fun k : ℕ => ‖B ^ k‖) Filter.atTop (nhds 0) := by
  have hgf := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius B
  have hlt1 : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (‖B ^ n‖ ^ (1 / n : ℝ)) < 1 := by
    exact hgf.eventually (Iio_mem_nhds hB)
  rcases Filter.eventually_atTop.1 hlt1 with ⟨N, hN⟩
  let N0 : ℕ := N + 1
  have hN0pos : 0 < N0 := by
    dsimp [N0]
    exact Nat.succ_pos _
  have hN0ne : N0 ≠ 0 := Nat.ne_of_gt hN0pos
  have hNpow : ‖B ^ N0‖ ^ (1 / N0 : ℝ) < 1 := by
    have : ENNReal.ofReal (‖B ^ N0‖ ^ (1 / N0 : ℝ)) < 1 := hN N0 (by
      dsimp [N0]
      exact Nat.le_succ N)
    simpa using this
  have hNnorm : ‖B ^ N0‖ < 1 := by
    have hN0posR : 0 < (N0 : ℝ) := by
      exact_mod_cast hN0pos
    exact (Real.rpow_lt_one_iff' (norm_nonneg _) (one_div_pos.mpr hN0posR)).mp hNpow
  let C : ℝ :=
    (Finset.range N0).sup' (by
      refine ⟨0, Finset.mem_range.mpr hN0pos⟩) (fun r => ‖B ^ r‖)
  have hbound : ∀ k : ℕ, ‖B ^ k‖ ≤ ‖(B ^ N0) ^ (k / N0)‖ * C := by
    intro k
    have hkmod : k % N0 ∈ Finset.range N0 := Finset.mem_range.mpr (Nat.mod_lt _ hN0pos)
    have hrem : ‖B ^ (k % N0)‖ ≤ C := by
      simpa [C] using
        (Finset.le_sup' (s := Finset.range N0) (f := fun r => ‖B ^ r‖) hkmod)
    calc
      ‖B ^ k‖ = ‖B ^ ((k / N0) * N0 + k % N0)‖ := by rw [Nat.div_add_mod']
      _ = ‖(B ^ N0) ^ (k / N0) * B ^ (k % N0)‖ := by
        rw [pow_add, Nat.mul_comm, pow_mul]
      _ ≤ ‖(B ^ N0) ^ (k / N0)‖ * ‖B ^ (k % N0)‖ := norm_mul_le _ _
      _ ≤ ‖(B ^ N0) ^ (k / N0)‖ * C := by
        exact mul_le_mul le_rfl hrem (norm_nonneg _) (norm_nonneg _)
  have hpow0 : Filter.Tendsto (fun q : ℕ => (B ^ N0) ^ q) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hNnorm
  have hnorm0 : Filter.Tendsto (fun q : ℕ => ‖(B ^ N0) ^ q‖) Filter.atTop (nhds 0) := by
    exact (tendsto_zero_iff_norm_tendsto_zero).mp hpow0
  have hpowdiv : Filter.Tendsto (fun k : ℕ => ‖(B ^ N0) ^ (k / N0)‖) Filter.atTop (nhds 0) := by
    exact hnorm0.comp (Nat.tendsto_div_const_atTop hN0ne)
  have hmajor : Filter.Tendsto (fun k : ℕ => ‖(B ^ N0) ^ (k / N0)‖ * C) Filter.atTop (nhds 0) := by
    simpa [C, zero_mul] using hpowdiv.mul tendsto_const_nhds
  exact squeeze_zero (fun k => norm_nonneg _) hbound hmajor

open scoped Matrix.Norms.L2Operator in
theorem real_matrix_exp_mulVec_tendsto_zero_of_negative_real_part_eigenvalues (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0) (v : Fin n → ℝ) : Filter.Tendsto (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • A)) v‖) Filter.atTop (nhds 0) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let Aℂ : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
  let vℂ : Fin n → ℂ := fun i => (v i : ℂ)
  have hnorm : ∀ w : Fin n → ℝ, ‖(fun i => (w i : ℂ))‖ = ‖w‖ := by
    intro w
    rw [Pi.norm_def (f := fun i => (w i : ℂ)), Pi.norm_def (f := w)]
    congr
    ext i
    simp
  have hcomplex : Filter.Tendsto (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • Aℂ)) vℂ‖) Filter.atTop (nhds 0) :=
    complex_matrix_exp_mulVec_tendsto_zero_of_negative_real_part_eigenvalues n Aℂ hA vℂ
  have hcont : Continuous (RingHom.mapMatrix (algebraMap ℝ ℂ) :
      Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℂ) := by
    simpa using (Continuous.matrix_map (A := fun M : Matrix (Fin n) (Fin n) ℝ => M) continuous_id Complex.continuous_ofReal)
  have hsmul_map : ∀ t : ℝ, (t • A).map (algebraMap ℝ ℂ) = t • Aℂ := by
    intro t
    ext i j
    simp [Aℂ]
  have hmap_exp : ∀ t : ℝ,
      (NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ) = NormedSpace.exp (t • Aℂ) := by
    intro t
    have h0 : (NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ) =
        NormedSpace.exp ((t • A).map (algebraMap ℝ ℂ)) := by
      simpa using (NormedSpace.map_exp (RingHom.mapMatrix (algebraMap ℝ ℂ)) hcont (t • A))
    have h1 : NormedSpace.exp ((t • A).map (algebraMap ℝ ℂ)) = NormedSpace.exp (t • Aℂ) := by
      congr
      exact hsmul_map t
    exact h0.trans h1
  have hvec : ∀ t : ℝ,
      Matrix.mulVec (NormedSpace.exp (t • Aℂ)) vℂ = fun i => ((Matrix.mulVec (NormedSpace.exp (t • A)) v) i : ℂ) := by
    intro t
    ext i
    calc
      (Matrix.mulVec (NormedSpace.exp (t • Aℂ)) vℂ) i
          = (Matrix.mulVec ((NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ)) (Complex.ofReal ∘ v)) i := by
              rw [← hmap_exp t]
              rfl
      _ = ((Matrix.mulVec (NormedSpace.exp (t • A)) v) i : ℂ) := by
            simpa [vℂ] using (RingHom.map_mulVec (algebraMap ℝ ℂ) (NormedSpace.exp (t • A)) v i).symm
  have hEq : (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • Aℂ)) vℂ‖)
      = (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • A)) v‖) := by
    funext t
    rw [hvec t]
    exact hnorm _
  simpa [hEq] using hcomplex

open scoped Matrix.Norms.L2Operator in
theorem shifted_matrix_exp_mulVec_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) (v : Fin n → ℝ) : HasDerivAt (fun u : ℝ => Matrix.mulVec (NormedSpace.exp ((u - s) • A)) v) (A.mulVec (Matrix.mulVec (NormedSpace.exp ((t - s) • A)) v)) t := by
  let B : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
    LinearMap.toContinuousLinearMap
      (((LinearMap.toContinuousLinearMap :
          ((Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] Fin n → ℝ)).toLinearMap).comp
        (Matrix.mulVecBilin (R := ℝ) (S := ℝ)))
  have h_shift : HasDerivAt (fun u : ℝ => u - s) 1 t := by
    simpa using ((hasDerivAt_id t).sub_const s)
  have h_exp : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u - s) • A))
      (A * NormedSpace.exp ((t - s) • A)) t := by
    simpa using
      (HasFDerivAt.comp_hasDerivAt_of_eq t
        ((hasDerivAt_exp_smul_const' A (t - s)).hasFDerivAt)
        h_shift rfl)
  have h :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (B := B)
      (fun _ => h_exp)
      (fun _ => (show HasDerivAt (fun _ : ℝ => v) 0 t by simpa using (hasDerivAt_const (x := t) (c := v))) )
  simpa [B, Matrix.mulVecBilin_apply, Matrix.mulVec_mulVec] using h

open scoped Matrix.Norms.L2Operator in
theorem linear_ode_eq_shifted_matrix_exp (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝ → (Fin n → ℝ)) (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) (s : ℝ) (hs : 0 < s) : Set.EqOn x (fun t : ℝ => Matrix.mulVec (NormedSpace.exp ((t - s) • A)) (x s)) (Set.Ici s) := by
  intro t ht
  let y : ℝ → (Fin n → ℝ) := fun u => Matrix.mulVec (NormedSpace.exp ((u - s) • A)) (x s)
  have hyderiv : ∀ u : ℝ, HasDerivAt y (A.mulVec (y u)) u := by
    intro u
    simpa only [y] using shifted_matrix_exp_mulVec_hasDerivAt n A s u (x s)
  have hLip : ∀ _ : ℝ, LipschitzWith ‖LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖₊ fun z : Fin n → ℝ => A.mulVec z := by
    intro τ
    simpa only [Matrix.toLin'_apply] using (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).lipschitz
  have hxcont : ContinuousOn x (Set.Icc s t) := by
    refine HasDerivAt.continuousOn (s := Set.Icc s t) (f' := fun u => A.mulVec (x u)) ?_
    intro u hu
    exact hx u (lt_of_lt_of_le hs hu.1)
  have hycont : ContinuousOn y (Set.Icc s t) := by
    refine HasDerivAt.continuousOn (s := Set.Icc s t) (f' := fun u => A.mulVec (y u)) ?_
    intro u hu
    exact hyderiv u
  have hxwithin : ∀ u ∈ Set.Ico s t, HasDerivWithinAt x (A.mulVec (x u)) (Set.Ici u) u := by
    intro u hu
    exact (hx u (lt_of_lt_of_le hs hu.1)).hasDerivWithinAt
  have hywithin : ∀ u ∈ Set.Ico s t, HasDerivWithinAt y (A.mulVec (y u)) (Set.Ici u) u := by
    intro u hu
    exact (hyderiv u).hasDerivWithinAt
  have hinit : x s = y s := by
    simp only [y, sub_self, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
  have hEq : Set.EqOn x y (Set.Icc s t) := by
    refine ODE_solution_unique (a := s) (b := t) (v := fun (_ : ℝ) (z : Fin n → ℝ) => A.mulVec z) (K := ‖LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖₊) hLip hxcont hxwithin hycont hywithin hinit
  exact hEq ⟨ht, le_rfl⟩

theorem linear_ode_asymptotic_stability (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  let y : ℝ → ℝ := fun t => ‖Matrix.mulVec (NormedSpace.exp ((t - 1) • A)) (x 1)‖
  have hEqOn := linear_ode_eq_shifted_matrix_exp n A x hx 1 (by norm_num)
  have hy0 : Filter.Tendsto y Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun t : ℝ => ‖Matrix.mulVec (NormedSpace.exp (t • A)) (x 1)‖) Filter.atTop (nhds 0) :=
      real_matrix_exp_mulVec_tendsto_zero_of_negative_real_part_eigenvalues n A hA (x 1)
    have hshift : Filter.Tendsto (fun t : ℝ => t - 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      exact Filter.mem_atTop_sets.mpr ⟨b + 1, by
        intro t ht
        show b ≤ t - 1
        linarith⟩
    simpa [y] using hbase.comp hshift
  have hEvent : y =ᶠ[Filter.atTop] (fun t : ℝ => ‖x t‖) := by
    filter_upwards [Filter.mem_atTop_sets.mpr ⟨1, by
      intro t ht
      exact ht⟩] with t ht
    have hxEq := hEqOn ht
    simp [y, hxEq]
  exact Filter.Tendsto.congr' hEvent hy0


end Submission
