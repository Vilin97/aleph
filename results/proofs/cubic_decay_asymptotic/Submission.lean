import Mathlib
import Submission.Helpers

open Filter Topology

namespace Submission

theorem cubic_initially_positive (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1) :
    ∃ a > 0, ∀ t ∈ Set.Icc 0 a, 0 < y t := by
  have hy_tendsto : Tendsto y (𝓝[Set.Ici 0] 0) (𝓝 1) := by
    simpa only [hy0] using hy_cont.tendsto
  have hpre : y ⁻¹' Set.Ioi (1 / 2 : ℝ) ∈ 𝓝[Set.Ici 0] 0 := by
    exact hy_tendsto (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  rcases Metric.mem_nhdsWithin_iff.mp hpre with ⟨ε, hεpos, hεsub⟩
  let a : ℝ := ε / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  refine ⟨a, ha_pos, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht_le_a : t ≤ a := ht.2
  have ht_lt_ε : t < ε := by
    dsimp [a] at ht_le_a
    linarith
  have ht_mem_ball : t ∈ Metric.ball 0 ε := by
    show dist t 0 < ε
    simpa [Real.dist_eq, abs_of_nonneg ht0] using ht_lt_ε
  have hy_half : (1 / 2 : ℝ) < y t := hεsub ⟨ht_mem_ball, ht0⟩
  linarith

noncomputable def cubic_invariant (y : ℝ → ℝ) (t : ℝ) : ℝ := 1 / (y t) ^ 2 - 2 * t

theorem cubic_invariant_eq_one_on_nonvanishing_interval (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1)
    (a t : ℝ) (ha : 0 < a) (ht : t ∈ Set.Ioo 0 a)
    (hnz : ∀ u ∈ Set.Ioo 0 a, y u ≠ 0) :
    cubic_invariant y t = 1 := by
  let f : ℝ → ℝ := fun u => cubic_invariant y u
  have hderiv : ∀ u ∈ Set.Ioo 0 a, HasDerivAt f 0 u := by
    intro u hu
    have hyu : HasDerivAt y (-(y u) ^ 3) u := hy_diff u hu.1
    have hynz : y u ≠ 0 := hnz u hu
    have hpow : HasDerivAt (fun x => (y x) ^ (2 : ℕ)) (2 * y u * (-(y u) ^ 3)) u := by
      simpa using (hyu.pow 2)
    have hinv : HasDerivAt (fun x => 1 / (y x) ^ (2 : ℕ)) (2 * y u * y u ^ 3 / (y u ^ 2) ^ 2) u := by
      simpa [one_div] using (hpow.inv (pow_ne_zero 2 hynz))
    have hlin : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 u := by
      simpa using ((hasDerivAt_id u).const_mul (2 : ℝ))
    have hsub : HasDerivAt (fun x => 1 / (y x) ^ (2 : ℕ) - (2 : ℝ) * x) (2 * y u * y u ^ 3 / (y u ^ 2) ^ 2 - 2) u :=
      hinv.sub hlin
    have hz : 2 * y u * y u ^ 3 / (y u ^ 2) ^ 2 - 2 = 0 := by
      field_simp [hynz]
      ring
    simpa [f, cubic_invariant, hz] using hsub
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 a) := by
    intro u hu
    exact (hderiv u hu).differentiableAt.differentiableWithinAt
  have hderiv_zero : Set.EqOn (deriv f) 0 (Set.Ioo 0 a) := by
    intro u hu
    simpa [(hderiv u hu).deriv] using rfl
  have hopen : IsOpen (Set.Ioo 0 a) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo 0 a) := (convex_Ioo 0 a).isPreconnected
  have hconst : ∀ u ∈ Set.Ioo 0 a, f u = f t := by
    intro u hu
    exact hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv_zero hu ht
  have hcont_right : Tendsto y (𝓝[>] 0) (𝓝 1) := by
    simpa [hy0] using (((continuousWithinAt_Ioi_iff_Ici).2 hy_cont).tendsto)
  have hlim_inv : Tendsto (fun u => 1 / (y u) ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 1) := by
    have hpow_lim : Tendsto (fun u => (y u) ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 ((1 : ℝ) ^ (2 : ℕ))) :=
      hcont_right.pow 2
    have h_inv : Tendsto (fun u => ((y u) ^ (2 : ℕ))⁻¹) (𝓝[>] 0) (𝓝 (((1 : ℝ) ^ (2 : ℕ))⁻¹)) :=
      Filter.Tendsto.inv₀ hpow_lim (by norm_num)
    simpa [one_div] using h_inv
  have hlim_lin : Tendsto (fun u : ℝ => (2 : ℝ) * u) (𝓝[>] 0) (𝓝 0) := by
    simpa using
      (((continuous_const.mul continuous_id).continuousAt.continuousWithinAt :
        ContinuousWithinAt (fun u : ℝ => (2 : ℝ) * u) (Set.Ioi 0) 0).tendsto)
  have hlim_f : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    have hsub_lim := hlim_inv.sub hlim_lin
    simpa [f, cubic_invariant] using hsub_lim
  have hconst_eventually : f =ᶠ[𝓝[>] 0] fun _ => f t := by
    filter_upwards [Ioo_mem_nhdsGT ha] with u hu
    exact hconst u hu
  have huniq : f t = 1 := by
    exact tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds hlim_f hconst_eventually.symm
  simpa [f] using huniq

theorem cubic_no_zero (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1)
    (t : ℝ) (ht : 0 < t) : y t ≠ 0 := by
  by_contra hzero
  obtain ⟨a, ha, hapos⟩ := cubic_initially_positive y hy_diff hy_cont hy0
  have hat : a ≤ t := by
    by_contra hat
    have hta : t < a := lt_of_not_ge hat
    have htIcc : t ∈ Set.Icc 0 a := ⟨le_of_lt ht, le_of_lt hta⟩
    exact (hapos t htIcc).ne' hzero
  let Z : Set ℝ := Set.Ici a ∩ y ⁻¹' ({0} : Set ℝ)
  have hZnonempty : Z.Nonempty := by
    refine ⟨t, ?_⟩
    refine ⟨hat, ?_⟩
    simpa [hzero]
  have hZbdd : BddBelow Z := ⟨a, by intro z hz; exact hz.1⟩
  have hcontOn : ContinuousOn y (Set.Ici a) := by
    intro s hs
    exact (hy_diff s (lt_of_lt_of_le ha hs)).continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z := by
    simpa [Z] using (hcontOn.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton)
  let c : ℝ := sInf Z
  have hcZ : c ∈ Z := by
    exact hZclosed.csInf_mem hZnonempty hZbdd
  have hca : a ≤ c := hcZ.1
  have hyc0 : y c = 0 := by
    simpa [Z] using hcZ.2
  have hca_lt : a < c := by
    by_contra hnot
    have hcle : c ≤ a := le_of_not_gt hnot
    have hceq : c = a := le_antisymm hcle hca
    have haIcc : a ∈ Set.Icc 0 a := ⟨le_of_lt ha, le_rfl⟩
    have hya_pos : 0 < y a := hapos a haIcc
    rw [hceq] at hyc0
    exact hya_pos.ne' hyc0
  have hc : 0 < c := lt_trans ha hca_lt
  have hczero_free : ∀ u ∈ Set.Ioo 0 c, y u ≠ 0 := by
    intro u hu
    by_cases hua : u < a
    · have huIcc : u ∈ Set.Icc 0 a := ⟨le_of_lt hu.1, le_of_lt hua⟩
      exact (hapos u huIcc).ne'
    · have hau : a ≤ u := le_of_not_gt hua
      intro huy0
      have huZ : u ∈ Z := by
        refine ⟨hau, ?_⟩
        simpa [huy0]
      have hcle : c ≤ u := csInf_le hZbdd huZ
      exact not_lt_of_ge hcle hu.2
  have hformula : ∀ u ∈ Set.Ioo 0 c, 1 / (y u) ^ 2 - 2 * u = 1 := by
    intro u hu
    simpa [cubic_invariant] using
      cubic_invariant_eq_one_on_nonvanishing_interval y hy_diff hy_cont hy0 c u hc hu hczero_free
  have hEq : ∀ u ∈ Set.Ioo 0 c, (y u) ^ 2 = 1 / (2 * u + 1) := by
    intro u hu
    have hu_ne : y u ≠ 0 := hczero_free u hu
    have hy2_ne : (y u) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hu_ne
    have h1 : (1 : ℝ) / (y u) ^ 2 = 2 * u + 1 := by
      linarith [hformula u hu]
    have hmul : (1 : ℝ) = (2 * u + 1) * (y u) ^ 2 := by
      exact (div_eq_iff hy2_ne).mp h1
    have hden_pos : 0 < 2 * u + 1 := by
      nlinarith [hu.1]
    have hden_ne : 2 * u + 1 ≠ 0 := by
      linarith
    have hdiv : (1 : ℝ) / (2 * u + 1) = (y u) ^ 2 := by
      exact (div_eq_iff hden_ne).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    simpa [eq_comm] using hdiv
  have hcy_tend : Tendsto (fun u : ℝ => (y u) ^ 2) (𝓝[<] c) (𝓝 0) := by
    simpa [hyc0] using ((hy_diff c hc).continuousAt.pow 2).continuousWithinAt.tendsto
  have hden_pos : 0 < 2 * c + 1 := by
    nlinarith [hc]
  have hden_ne : 2 * c + 1 ≠ 0 := by
    linarith
  have hconst_tend : Tendsto (fun u : ℝ => 1 / (2 * u + 1)) (𝓝[<] c) (𝓝 (1 / (2 * c + 1))) := by
    have hcont : ContinuousAt (fun u : ℝ => 1 / (2 * u + 1)) c := by
      apply ContinuousAt.div
      · exact continuousAt_const
      · exact ((continuous_const.mul continuous_id).continuousAt.add continuousAt_const)
      · exact hden_ne
    exact hcont.continuousWithinAt.tendsto
  haveI : NeBot (𝓝[<] c) := nhdsLT_neBot c
  have hEventually : (fun u : ℝ => (y u) ^ 2) =ᶠ[𝓝[<] c] fun u => 1 / (2 * u + 1) := by
    filter_upwards [Ioo_mem_nhdsLT hc] with u hu
    exact hEq u hu
  have hlim_eq : (0 : ℝ) = 1 / (2 * c + 1) := by
    exact tendsto_nhds_unique_of_eventuallyEq hcy_tend hconst_tend hEventually
  have hpos : 0 < (1 : ℝ) / (2 * c + 1) := by
    positivity
  linarith

theorem cubic_invariant_eq_one (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1)
    (t : ℝ) (ht : 0 < t) : cubic_invariant y t = 1 := by
  have ha : 0 < t + 1 := by
    linarith
  have ht' : t ∈ Set.Ioo 0 (t + 1) := by
    constructor
    · exact ht
    · linarith
  apply cubic_invariant_eq_one_on_nonvanishing_interval y hy_diff hy_cont hy0 (t + 1) t ha ht'
  intro u hu
  exact cubic_no_zero y hy_diff hy_cont hy0 u hu.1

theorem cubic_positive (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1)
    (t : ℝ) (ht : 0 ≤ t) : 0 < y t := by
  by_cases h0 : t = 0
  · subst t
    linarith [hy0]
  · have htpos : 0 < t := by
      exact lt_of_le_of_ne ht (by simpa [eq_comm] using h0)
    rcases cubic_initially_positive y hy_diff hy_cont hy0 with ⟨a, ha, hapos⟩
    let u : ℝ := min (a / 2) (t / 2)
    have hu_pos : 0 < u := by
      dsimp [u]
      apply lt_min
      · linarith
      · linarith
    have hu_le_a : u ≤ a := by
      dsimp [u]
      calc
        min (a / 2) (t / 2) ≤ a / 2 := min_le_left _ _
        _ ≤ a := by linarith
    have hu_mem : u ∈ Set.Icc 0 a := by
      constructor
      · exact le_of_lt hu_pos
      · exact hu_le_a
    have hyu_pos : 0 < y u := hapos u hu_mem
    have hu_le_t : u ≤ t := by
      dsimp [u]
      calc
        min (a / 2) (t / 2) ≤ t / 2 := min_le_right _ _
        _ ≤ t := by linarith
    by_cases hyt : 0 < y t
    · exact hyt
    · have hyt_le : y t ≤ 0 := le_of_not_gt hyt
      have hyt_ne : y t ≠ 0 := cubic_no_zero y hy_diff hy_cont hy0 t htpos
      have hyt_lt : y t < 0 := lt_of_le_of_ne hyt_le hyt_ne
      have hcont_Icc : ContinuousOn y (Set.Icc u t) := by
        intro x hx
        have hxpos : 0 < x := lt_of_lt_of_le hu_pos hx.1
        exact (hy_diff x hxpos).continuousAt.continuousWithinAt
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (y t) (y u) := by
        constructor <;> linarith
      have hzero_img : (0 : ℝ) ∈ y '' Set.Icc u t :=
        (intermediate_value_Icc' hu_le_t hcont_Icc) hzero_mem
      rcases hzero_img with ⟨s, hs_mem, hs_zero⟩
      have hs_pos : 0 < s := lt_of_lt_of_le hu_pos hs_mem.1
      exact False.elim ((cubic_no_zero y hy_diff hy_cont hy0 s hs_pos) hs_zero)

noncomputable def cubic_profile (t : ℝ) : ℝ := 1 / Real.sqrt (2 * t + 1)

theorem cubic_explicit (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1)
    (t : ℝ) (ht : 0 < t) : y t = cubic_profile t := by
  have hypos : 0 < y t := cubic_positive y hy_diff hy_cont hy0 t (le_of_lt ht)
  have hyne : y t ≠ 0 := ne_of_gt hypos
  have hInv : cubic_invariant y t = 1 := cubic_invariant_eq_one y hy_diff hy_cont hy0 t ht
  have hEq1 : 1 / (y t) ^ 2 = 2 * t + 1 := by
    unfold cubic_invariant at hInv
    linarith
  have htpos : 0 < 2 * t + 1 := by
    linarith
  have hy2ne : (y t) ^ 2 ≠ 0 := pow_ne_zero 2 hyne
  have hMul : (2 * t + 1) * (y t) ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x * (y t) ^ 2) hEq1
    simpa [one_div, hy2ne, mul_assoc, mul_left_comm, mul_comm] using h.symm
  have hsq1 : (y t * Real.sqrt (2 * t + 1)) ^ 2 = 1 := by
    calc
      (y t * Real.sqrt (2 * t + 1)) ^ 2 = (y t) ^ 2 * (Real.sqrt (2 * t + 1)) ^ 2 := by ring
      _ = (y t) ^ 2 * (2 * t + 1) := by rw [Real.sq_sqrt (le_of_lt htpos)]
      _ = 1 := by simpa [mul_comm] using hMul
  have hprod_pos : 0 < y t * Real.sqrt (2 * t + 1) := by
    exact mul_pos hypos (Real.sqrt_pos.2 htpos)
  have hprod : y t * Real.sqrt (2 * t + 1) = 1 := by
    nlinarith [hsq1, hprod_pos]
  have hsqrtne : Real.sqrt (2 * t + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 htpos)
  unfold cubic_profile
  exact (eq_div_iff hsqrtne).2 hprod

theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have h_eq : (fun t : ℝ => y t * Real.sqrt t) =ᶠ[atTop] (fun t : ℝ => cubic_profile t * Real.sqrt t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [cubic_explicit y hy_diff hy_cont hy0 t ht]
  refine Filter.Tendsto.congr' h_eq.symm ?_
  have h_pos : ∀ᶠ t : ℝ in atTop, 0 < t := Filter.eventually_gt_atTop (0 : ℝ)
  have h_eq' : (fun t : ℝ => cubic_profile t * Real.sqrt t) =ᶠ[atTop]
      (fun t : ℝ => 1 / Real.sqrt (2 + t⁻¹)) := by
    filter_upwards [h_pos] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hnum : 0 ≤ 2 * t + 1 := by nlinarith
    have h_alg : (2 * t + 1) / t = 2 + t⁻¹ := by
      field_simp [ht0]
    calc
      cubic_profile t * Real.sqrt t
          = Real.sqrt t / Real.sqrt (2 * t + 1) := by
              rw [cubic_profile, one_div_mul_eq_div]
      _ = 1 / (Real.sqrt (2 * t + 1) / Real.sqrt t) := by
              rw [← one_div_div]
      _ = 1 / Real.sqrt ((2 * t + 1) / t) := by
              rw [← Real.sqrt_div hnum t]
      _ = 1 / Real.sqrt (2 + t⁻¹) := by
              rw [h_alg]
  refine Filter.Tendsto.congr' h_eq'.symm ?_
  have h_inv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero
  have h_add : Tendsto (fun t : ℝ => 2 + t⁻¹) atTop (𝓝 (2 : ℝ)) := by
    simpa using tendsto_const_nhds.add h_inv
  have h_sqrt : Tendsto (fun t : ℝ => Real.sqrt (2 + t⁻¹)) atTop (𝓝 (Real.sqrt 2)) := by
    exact Filter.Tendsto.sqrt h_add
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by norm_num)
  have h_inv_sqrt : Tendsto (fun t : ℝ => (Real.sqrt (2 + t⁻¹))⁻¹) atTop (𝓝 ((Real.sqrt 2)⁻¹)) := by
    exact Filter.Tendsto.inv₀ h_sqrt hsqrt2_ne
  simpa [one_div] using h_inv_sqrt


end Submission
