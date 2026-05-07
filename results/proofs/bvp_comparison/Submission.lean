import Mathlib
import Submission.Helpers

namespace Submission

theorem bvp_diff_convex (J : Set ℝ) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J) (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => u x - v x) := by
  let D : Set ℝ := Set.Icc (0 : ℝ) 1
  let f : ℝ → ℝ := fun x => u x - v x
  let f' : ℝ → ℝ := fun x => deriv u x - deriv v x
  let f'' : ℝ → ℝ := fun x => deriv (deriv u) x - deriv (deriv v) x
  have hcont : ContinuousOn f D := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub hx
    exact ((hu x hxJ).continuousAt.sub (hv x hxJ).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [D, interior_Icc] using hx
    have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hxIoo)
    simpa [f, f'] using ((hu x hxJ).sub (hv x hxJ)).hasDerivWithinAt
  have hderiv2 : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [D, interior_Icc] using hx
    have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hxIoo)
    simpa [f', f''] using ((hu' x hxJ).sub (hv' x hxJ)).hasDerivWithinAt
  have hnonneg : ∀ x ∈ interior D, 0 ≤ f'' x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [D, interior_Icc] using hx
    have h := hineq x hxIoo
    dsimp [f'']
    linarith
  simpa [D, f] using
    (convexOn_of_hasDerivWithinAt2_nonneg (D := D) (f := f) (f' := f') (f'' := f'')
      (convex_Icc (0 : ℝ) 1) hcont hderiv hderiv2 hnonneg)

theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  intro x hx
  let g : ℝ → ℝ := fun t => u t - v t
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
    bvp_diff_convex J hJ_sub u v hu hu' hv hv' hineq
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hx1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  rcases hx with ⟨hx_nonneg, hx_le_one⟩
  have ha : 0 ≤ 1 - x := by linarith
  have hb : 0 ≤ x := hx_nonneg
  have hab : (1 - x) + x = 1 := by ring
  have hseg := hconv.2 hx0 hx1 ha hb hab
  have h0 : g 0 ≤ 0 := by
    dsimp [g]
    linarith
  have h1 : g 1 ≤ 0 := by
    dsimp [g]
    linarith
  have hcomb : (1 - x) * g 0 + x * g 1 ≤ 0 := by
    nlinarith [h0, h1, ha, hb]
  have hxeq : ((1 - x) • (0 : ℝ) + x • (1 : ℝ)) = x := by
    ring
  have hxineq : g x ≤ (1 - x) • g 0 + x • g 1 := by
    simpa [hxeq, smul_eq_mul] using hseg
  have hright : (1 - x) • g 0 + x • g 1 ≤ 0 := by
    simpa [smul_eq_mul] using hcomb
  have hfinal : g x ≤ 0 := by
    linarith
  dsimp [g] at hfinal
  linarith


end Submission
