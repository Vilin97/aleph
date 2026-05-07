import Mathlib
import Submission.Helpers

namespace Submission

noncomputable def sturm_wronskian (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

theorem sturm_wronskian_hasDerivAt (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ) (x : ℝ)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hx : x ∈ J) :
    HasDerivAt (sturm_wronskian y₁ y₂) (-(p x * sturm_wronskian y₁ y₂ x)) x := by
  unfold sturm_wronskian
  have h1 := (hy₁ x hx).mul (hy₂' x hx)
  have h2 := (hy₂ x hx).mul (hy₁' x hx)
  convert h1.sub h2 using 1 <;> ring

theorem sturm_weighted_wronskian_eq (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ)
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ J) :
    ∀ x ∈ J,
      Real.exp (∫ t in x₀..x, p t) * sturm_wronskian y₁ y₂ x = sturm_wronskian y₁ y₂ x₀ := by
  let F : ℝ → ℝ := fun x => Real.exp (∫ t in x₀..x, p t) * sturm_wronskian y₁ y₂ x
  have hsubset : ∀ x ∈ J, Set.uIcc x₀ x ⊆ J := by
    intro x hx
    by_cases hxx : x₀ ≤ x
    · simpa [Set.uIcc_of_le hxx] using (hJ_conn.Icc_subset hx₀ hx : Set.Icc x₀ x ⊆ J)
    · have hxx' : x ≤ x₀ := le_of_not_ge hxx
      simpa [Set.uIcc_of_ge hxx'] using (hJ_conn.Icc_subset hx hx₀ : Set.Icc x x₀ ⊆ J)
  have hInt : ∀ x ∈ J, IntervalIntegrable p MeasureTheory.volume x₀ x := by
    intro x hx
    have hp' : ContinuousOn p (Set.uIcc x₀ x) := hp.mono (hsubset x hx)
    simpa using (ContinuousOn.intervalIntegrable (μ := MeasureTheory.volume) hp')
  have hcont : ∀ x ∈ J, ContinuousAt p x := by
    intro x hx
    exact hp.continuousAt (hJ_open.mem_nhds hx)
  have hmeas : ∀ x ∈ J, StronglyMeasurableAtFilter p (nhds x) MeasureTheory.volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter hJ_open hcont
  have hderiv_int : ∀ x ∈ J, HasDerivAt (fun u => ∫ t in x₀..u, p t) (p x) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right (hInt x hx) (hmeas x hx) (hcont x hx)
  have hFderiv : ∀ x ∈ J, HasDerivAt F 0 x := by
    intro x hx
    have h1 : HasDerivAt (fun x => Real.exp (∫ t in x₀..x, p t))
        (Real.exp (∫ t in x₀..x, p t) * p x) x := by
      simpa using (hderiv_int x hx).exp
    have h2 : HasDerivAt (sturm_wronskian y₁ y₂) (-(p x * sturm_wronskian y₁ y₂ x)) x :=
      sturm_wronskian_hasDerivAt p q y₁ y₂ J x hy₁ hy₁' hy₂ hy₂' hx
    have hmul := h1.mul h2
    dsimp [F] at hmul ⊢
    convert hmul using 1
    ring
  have hFdiff : DifferentiableOn ℝ F J := by
    intro x hx
    exact (hFderiv x hx).differentiableAt.differentiableWithinAt
  have hFderiv_eq : Set.EqOn (deriv F) 0 J := by
    intro x hx
    simpa using (hFderiv x hx).deriv
  intro x hx
  have hxeq : F x = F x₀ :=
    IsOpen.is_const_of_deriv_eq_zero hJ_open hJ_conn hFdiff hFderiv_eq hx hx₀
  have hx0eval : F x₀ = sturm_wronskian y₁ y₂ x₀ := by
    simp [F]
  exact hxeq.trans hx0eval

theorem sturm_wronskian_nonvanishing (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ)
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp : ContinuousOn p J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, sturm_wronskian y₁ y₂ x₀ ≠ 0) :
    ∀ x ∈ J, sturm_wronskian y₁ y₂ x ≠ 0 := by
  rcases hW with ⟨x₀, hx₀, hWx₀⟩
  intro x hx
  have hEq :=
    sturm_weighted_wronskian_eq p q y₁ y₂ J hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' x₀ hx₀ x hx
  have hexp : Real.exp (∫ t in x₀..x, p t) ≠ 0 := Real.exp_ne_zero _
  intro hzero
  apply hWx₀
  rw [← hEq, hzero, mul_zero]

theorem sturm_zero_exists (y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_sub : Set.Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hWnz : ∀ x ∈ J, sturm_wronskian y₁ y₂ x ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0) :
    ∃ c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  classical
  by_contra h
  have hy₂nz : ∀ x ∈ Set.Ioo a b, y₂ x ≠ 0 := by
    intro x hx hx0
    apply h
    exact ⟨x, hx, hx0⟩
  have haJ : a ∈ J := hJ_sub ⟨le_rfl, le_of_lt hab⟩
  have hbJ : b ∈ J := hJ_sub ⟨le_of_lt hab, le_rfl⟩
  have hy₂a_nz : y₂ a ≠ 0 := by
    intro hy₂a
    apply (hWnz a haJ)
    simp [sturm_wronskian, hza, hy₂a]
  have hy₂b_nz : y₂ b ≠ 0 := by
    intro hy₂b
    apply (hWnz b hbJ)
    simp [sturm_wronskian, hzb, hy₂b]
  have hy₂Icc : ∀ x ∈ Set.Icc a b, y₂ x ≠ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact hy₂a_nz
    · rcases eq_or_lt_of_le hx.2 with rfl | hxb
      · exact hy₂b_nz
      · exact hy₂nz x ⟨hax, hxb⟩
  have hy₁_cont : ContinuousOn y₁ (Set.Icc a b) := by
    intro x hx
    exact (hy₁ x (hJ_sub hx)).continuousAt.continuousWithinAt
  have hy₂_cont : ContinuousOn y₂ (Set.Icc a b) := by
    intro x hx
    exact (hy₂ x (hJ_sub hx)).continuousAt.continuousWithinAt
  have hf_cont : ContinuousOn (y₁ / y₂) (Set.Icc a b) :=
    hy₁_cont.div hy₂_cont hy₂Icc
  have hEq : (y₁ / y₂) a = (y₁ / y₂) b := by
    calc
      (y₁ / y₂) a = 0 := by simp [hza]
      _ = (y₁ / y₂) b := by simp [hzb]
  have hderiv :
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (y₁ / y₂)
          (((deriv y₁ x) * y₂ x - y₁ x * deriv y₂ x) / y₂ x ^ 2) x := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    simpa using (hy₁ x hxJ).div (hy₂ x hxJ) (hy₂nz x hx)
  obtain ⟨c, hc, hfc⟩ :=
    exists_hasDerivAt_eq_zero hab hf_cont hEq hderiv
  have hcJ : c ∈ J := hJ_sub ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have hy₂c_nz : y₂ c ≠ 0 := hy₂nz c hc
  have hsq_nz : y₂ c ^ 2 ≠ 0 := pow_ne_zero 2 hy₂c_nz
  have hnum_zero : deriv y₁ c * y₂ c - y₁ c * deriv y₂ c = 0 := by
    rcases (div_eq_zero_iff.mp hfc) with hnum_zero | hden_zero
    · exact hnum_zero
    · exact False.elim (hsq_nz hden_zero)
  have hWzero : sturm_wronskian y₁ y₂ c = 0 := by
    unfold sturm_wronskian
    nlinarith [hnum_zero]
  exact (hWnz c hcJ) hWzero

theorem sturm_zero_unique (y₁ y₂ : ℝ → ℝ) (a b : ℝ)
    (J : Set ℝ) (hJ_sub : Set.Icc a b ⊆ J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hWnz : ∀ x ∈ J, sturm_wronskian y₁ y₂ x ≠ 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0)
    (c₁ c₂ : ℝ)
    (hc₁ : c₁ ∈ Set.Ioo a b) (hc₂ : c₂ ∈ Set.Ioo a b)
    (hz₁ : y₂ c₁ = 0) (hz₂ : y₂ c₂ = 0) :
    c₁ = c₂ := by
  by_contra hneq
  have hcase : ∀ {u v : ℝ},
      u ∈ Set.Ioo a b →
      v ∈ Set.Ioo a b →
      y₂ u = 0 →
      y₂ v = 0 →
      u < v →
      False := by
    intro u v hu hv hzu hzv huv
    let g : ℝ → ℝ := fun x => y₂ x / y₁ x
    have hsub_Icc_ab : Set.Icc u v ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨le_trans hu.1.le hx.1, le_trans hx.2 hv.2.le⟩
    have hsub_Icc_J : Set.Icc u v ⊆ J := by
      intro x hx
      exact hJ_sub (hsub_Icc_ab hx)
    have hy₁_ne : ∀ x ∈ Set.Icc u v, y₁ x ≠ 0 := by
      intro x hx
      apply hne x
      exact ⟨lt_of_lt_of_le hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩
    have hcont_y₁ : ContinuousOn y₁ (Set.Icc u v) := by
      intro x hx
      exact (hy₁ x (hsub_Icc_J hx)).continuousAt.continuousWithinAt
    have hcont_y₂ : ContinuousOn y₂ (Set.Icc u v) := by
      intro x hx
      exact (hy₂ x (hsub_Icc_J hx)).continuousAt.continuousWithinAt
    have hcont_g : ContinuousOn g (Set.Icc u v) := by
      apply ContinuousOn.div hcont_y₂ hcont_y₁
      intro x hx
      exact hy₁_ne x hx
    have hg_u : g u = 0 := by
      simp [g, hzu]
    have hg_v : g v = 0 := by
      simp [g, hzv]
    have hderiv_g : ∀ x ∈ Set.Ioo u v,
        HasDerivAt g ((sturm_wronskian y₁ y₂ x) / (y₁ x) ^ 2) x := by
      intro x hx
      have hxIcc : x ∈ Set.Icc u v := ⟨hx.1.le, hx.2.le⟩
      have hxJ : x ∈ J := hsub_Icc_J hxIcc
      have hy1x := hy₁ x hxJ
      have hy2x := hy₂ x hxJ
      have hy1x_ne : y₁ x ≠ 0 := hy₁_ne x hxIcc
      simpa [g, sturm_wronskian, pow_two, mul_comm, mul_left_comm, mul_assoc] using hy2x.div hy1x hy1x_ne
    obtain ⟨x, hx, hzero⟩ := exists_hasDerivAt_eq_zero huv hcont_g (by rw [hg_u, hg_v]) hderiv_g
    have hxIcc : x ∈ Set.Icc u v := ⟨hx.1.le, hx.2.le⟩
    have hxJ : x ∈ J := hsub_Icc_J hxIcc
    have hw : sturm_wronskian y₁ y₂ x ≠ 0 := hWnz x hxJ
    have hy1x_ne : y₁ x ≠ 0 := hy₁_ne x hxIcc
    have hsq_ne : (y₁ x) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hy1x_ne
    exact (div_ne_zero hw hsq_ne) hzero
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact hcase hc₁ hc₂ hz₁ hz₂ hlt
  · exact hcase hc₂ hc₁ hz₂ hz₁ hgt

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  have hW' : ∃ x₀ ∈ J, sturm_wronskian y₁ y₂ x₀ ≠ 0 := by
    simpa [sturm_wronskian] using hW
  have hWnz : ∀ x ∈ J, sturm_wronskian y₁ y₂ x ≠ 0 :=
    sturm_wronskian_nonvanishing p q y₁ y₂ J hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW'
  rcases sturm_zero_exists y₁ y₂ a b hab J hJ_sub hy₁ hy₂ hWnz hza hzb with ⟨c, hc, hzc⟩
  refine ⟨c, ⟨hc, hzc⟩, ?_⟩
  intro c' hc'
  rcases hc' with ⟨hc', hzc'⟩
  exact (sturm_zero_unique y₁ y₂ a b J hJ_sub hy₁ hy₂ hWnz hne c c' hc hc' hzc hzc').symm


end Submission
