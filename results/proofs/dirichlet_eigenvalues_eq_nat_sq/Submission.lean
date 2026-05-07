import Mathlib
import Submission.Helpers

open scoped Real

namespace Submission

def DirichletEigenfunction (lam : ℝ) (y : ℝ → ℝ) (J : Set ℝ) : Prop :=
  IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
    (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
    (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
    y 0 = 0 ∧ y Real.pi = 0 ∧
    ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0

theorem dirichlet_solution_not_lam_eq_zero: (∃ y J, DirichletEigenfunction 0 y J) → False := by
  rintro ⟨y, J, hJ⟩
  rcases hJ with ⟨hopen, hsub, hy1, hy2, hy0, hypi, hne⟩
  have hy2' : ∀ x ∈ J, HasDerivAt (deriv y) 0 x := by
    intro x hx
    simpa using hy2 x hx
  have hcont : ContinuousOn (deriv y) (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    exact (hy2' x (hsub hx)).continuousAt.continuousWithinAt
  have hderiv_zero : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi, HasDerivWithinAt (deriv y) 0 (Set.Ici x) x := by
    intro x hx
    exact (hy2' x (hsub ⟨hx.1, le_of_lt hx.2⟩)).hasDerivWithinAt
  have hconst : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv y x = deriv y 0 :=
    constant_of_has_deriv_right_zero hcont hderiv_zero
  let c : ℝ := deriv y 0
  let g : ℝ → ℝ := fun x => y x - c * x
  have hcontg : ContinuousOn g (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    have hyc : ContinuousAt y x := (hy1 x (hsub hx)).continuousAt
    have hlin : ContinuousAt (fun t : ℝ => c * t) x := by
      simpa [one_mul] using ((hasDerivAt_id x).const_mul c).continuousAt
    exact (hyc.sub hlin).continuousWithinAt
  have hgderiv : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi, HasDerivWithinAt g 0 (Set.Ici x) x := by
    intro x hx
    have hyx : HasDerivAt y (deriv y x) x := hy1 x (hsub ⟨hx.1, le_of_lt hx.2⟩)
    have hc : deriv y x = c := hconst x ⟨hx.1, le_of_lt hx.2⟩
    have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa [one_mul] using (hasDerivAt_id x).const_mul c
    have hg : HasDerivAt g (deriv y x - c) x := by
      simpa [g] using hyx.sub hlin
    have hg' : HasDerivAt g 0 x := by
      simpa [hc] using hg
    exact hg'.hasDerivWithinAt
  have hgconst : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, g x = g 0 :=
    constant_of_has_deriv_right_zero hcontg hgderiv
  have hline : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = c * x := by
    intro x hx
    have hxg := hgconst x hx
    simp [g, hy0] at hxg
    nlinarith
  have hc0 : c = 0 := by
    have hpi := hline Real.pi ⟨le_of_lt Real.pi_pos, le_rfl⟩
    have hmul : c * Real.pi = 0 := by
      simpa [hypi] using hpi.symm
    nlinarith [Real.pi_pos, hmul]
  rcases hne with ⟨x, hx, hxy⟩
  have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hzero : y x = 0 := by
    simpa [hc0] using hline x hx'
  exact hxy hzero

theorem dirichlet_solution_not_lam_lt_zero (lam : ℝ) (hlam : lam < 0) : (∃ y J, DirichletEigenfunction lam y J) → False := by
  intro h
  rcases h with ⟨y, J, hdir⟩
  rcases hdir with ⟨hJopen, hsub, hy1, hy2, hy0, hyπ, hne⟩
  let μ : ℝ := Real.sqrt (-lam)
  have hμpos : 0 < μ := by
    dsimp [μ]
    rw [Real.sqrt_pos]
    linarith
  have hμsq : μ ^ 2 = -lam := by
    dsimp [μ]
    apply Real.sq_sqrt
    linarith
  let P : ℝ → ℝ := fun x => (deriv y x - μ * y x) * Real.exp (x * μ)
  let Q : ℝ → ℝ := fun x => (deriv y x + μ * y x) * Real.exp (x * (-μ))
  have hPderiv : ∀ x ∈ J, HasDerivAt P 0 x := by
    intro x hxJ
    dsimp [P]
    have hyx : HasDerivAt y (deriv y x) x := hy1 x hxJ
    have hydx : HasDerivAt (deriv y) (-(lam * y x)) x := hy2 x hxJ
    have hμy : HasDerivAt (fun t : ℝ => μ * y t) (μ * deriv y x) x := by
      exact hyx.const_mul μ
    have hmain : HasDerivAt (fun t : ℝ => deriv y t - μ * y t) (-(lam * y x) - μ * deriv y x) x := by
      exact hydx.sub hμy
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * μ)) (Real.exp (x * μ) * μ) x := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_mul_const (x := x) μ).exp
    have hmul : HasDerivAt P
        (((-(lam * y x) - μ * deriv y x) * Real.exp (x * μ)) +
          (deriv y x - μ * y x) * (Real.exp (x * μ) * μ)) x := by
      exact hmain.mul hexp
    refine hmul.congr_deriv ?_
    ring_nf
    rw [hμsq]
    ring
  have hQderiv : ∀ x ∈ J, HasDerivAt Q 0 x := by
    intro x hxJ
    dsimp [Q]
    have hyx : HasDerivAt y (deriv y x) x := hy1 x hxJ
    have hydx : HasDerivAt (deriv y) (-(lam * y x)) x := hy2 x hxJ
    have hμy : HasDerivAt (fun t : ℝ => μ * y t) (μ * deriv y x) x := by
      exact hyx.const_mul μ
    have hmain : HasDerivAt (fun t : ℝ => deriv y t + μ * y t) (-(lam * y x) + μ * deriv y x) x := by
      exact hydx.add hμy
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * (-μ))) (Real.exp (x * (-μ)) * (-μ)) x := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_mul_const (x := x) (-μ)).exp
    have hmul : HasDerivAt Q
        (((-(lam * y x) + μ * deriv y x) * Real.exp (x * (-μ))) +
          (deriv y x + μ * y x) * (Real.exp (x * (-μ)) * (-μ))) x := by
      exact hmain.mul hexp
    refine hmul.congr_deriv ?_
    ring_nf
    rw [hμsq]
    ring
  have hPcont : ContinuousOn P (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    exact (hPderiv x (hsub hx)).continuousAt.continuousWithinAt
  have hPright : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi, HasDerivWithinAt P 0 (Set.Ici x) x := by
    intro x hx
    exact (hPderiv x (hsub ⟨hx.1, le_of_lt hx.2⟩)).hasDerivWithinAt
  have hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) Real.pi) := by
    intro x hx
    exact (hQderiv x (hsub hx)).continuousAt.continuousWithinAt
  have hQright : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi, HasDerivWithinAt Q 0 (Set.Ici x) x := by
    intro x hx
    exact (hQderiv x (hsub ⟨hx.1, le_of_lt hx.2⟩)).hasDerivWithinAt
  have hPconst := constant_of_has_deriv_right_zero hPcont hPright
  have hQconst := constant_of_has_deriv_right_zero hQcont hQright
  have hπmem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨Real.pi_pos.le, le_rfl⟩
  have hPπ : deriv y Real.pi * Real.exp (Real.pi * μ) = deriv y 0 := by
    simpa [P, hy0, hyπ] using hPconst Real.pi hπmem
  have hQπ : deriv y Real.pi * Real.exp (Real.pi * (-μ)) = deriv y 0 := by
    simpa [Q, hy0, hyπ] using hQconst Real.pi hπmem
  have harglt : Real.pi * (-μ) < Real.pi * μ := by
    nlinarith [Real.pi_pos, hμpos]
  have hexpne : Real.exp (Real.pi * (-μ)) ≠ Real.exp (Real.pi * μ) := by
    exact ne_of_lt (Real.exp_strictMono harglt)
  have hdyπzero : deriv y Real.pi = 0 := by
    by_contra hdyπne
    have hexpeq : Real.exp (Real.pi * (-μ)) = Real.exp (Real.pi * μ) := by
      apply mul_left_cancel₀ hdyπne
      calc
        deriv y Real.pi * Real.exp (Real.pi * (-μ)) = deriv y 0 := hQπ
        _ = deriv y Real.pi * Real.exp (Real.pi * μ) := hPπ.symm
    exact hexpne hexpeq
  have hdy0zero : deriv y 0 = 0 := by
    simpa [P, hy0, hyπ, hdyπzero] using (hPconst Real.pi hπmem).symm
  have hyzero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 := by
    intro x hx
    have hPx : (deriv y x - μ * y x) * Real.exp (x * μ) = 0 := by
      calc
        P x = P 0 := hPconst x hx
        _ = 0 := by
          dsimp [P]
          simp [hy0, hdy0zero]
    have hQx : (deriv y x + μ * y x) * Real.exp (x * (-μ)) = 0 := by
      calc
        Q x = Q 0 := hQconst x hx
        _ = 0 := by
          dsimp [Q]
          simp [hy0, hdy0zero]
    have h1 : deriv y x - μ * y x = 0 := by
      rcases mul_eq_zero.mp hPx with h1 | h1
      · exact h1
      · exact False.elim ((Real.exp_ne_zero (x * μ)) h1)
    have h2 : deriv y x + μ * y x = 0 := by
      rcases mul_eq_zero.mp hQx with h2 | h2
      · exact h2
      · exact False.elim ((Real.exp_ne_zero (x * (-μ))) h2)
    nlinarith [h1, h2, hμpos]
  rcases hne with ⟨x, hxIoo, hxyne⟩
  exact hxyne (hyzero x ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩)

theorem nat_sq_implies_dirichlet_solution (n : ℕ) (hn : 0 < n) : ∃ y J, DirichletEigenfunction ((n : ℝ) ^ 2) y J := by
  refine ⟨Real.sin ∘ HMul.hMul (n : ℝ), Set.univ, ?_⟩
  dsimp [DirichletEigenfunction]
  constructor
  · exact isOpen_univ
  constructor
  · intro x hx
    trivial
  constructor
  · intro x hx
    have hy' : HasDerivAt (Real.sin ∘ HMul.hMul (n : ℝ))
        ((n : ℝ) * Real.cos (x * (n : ℝ))) x := by
      simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x ((hasDerivAt_id x).const_mul (n : ℝ))
    have hderiv : deriv (Real.sin ∘ HMul.hMul (n : ℝ)) x =
        (n : ℝ) * Real.cos (x * (n : ℝ)) := hy'.deriv
    simpa [hderiv] using hy'
  · constructor
    · have hderivfun : deriv (Real.sin ∘ HMul.hMul (n : ℝ)) =
          fun x => (n : ℝ) * Real.cos (x * (n : ℝ)) := by
        funext x
        have hy' : HasDerivAt (Real.sin ∘ HMul.hMul (n : ℝ))
            ((n : ℝ) * Real.cos (x * (n : ℝ))) x := by
          simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
            (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x ((hasDerivAt_id x).const_mul (n : ℝ))
        exact hy'.deriv
      intro x hx
      rw [hderivfun]
      have hcos' : HasDerivAt (fun t : ℝ => (n : ℝ) * Real.cos (t * (n : ℝ)))
          (-( (n : ℝ) * ((n : ℝ) * Real.sin (x * (n : ℝ))))) x := by
        simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc] using
          ((Real.hasDerivAt_cos ((n : ℝ) * x)).comp x ((hasDerivAt_id x).const_mul (n : ℝ))).const_mul (n : ℝ)
      simpa [pow_two, Function.comp, mul_assoc, mul_left_comm, mul_comm] using hcos'
    · constructor
      · simp [Function.comp, Real.sin_zero]
      · constructor
        · simpa [Function.comp, mul_comm] using Real.sin_nat_mul_pi n
        · refine ⟨Real.pi / (2 * (n : ℝ)), ?_, ?_⟩
          · constructor
            · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
              have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
              exact div_pos Real.pi_pos h2n_pos
            · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
              have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by
                have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
                positivity
              refine (div_lt_iff₀ h2n_pos).2 ?_
              nlinarith [Real.pi_pos, hn1]
          · have hn0' : (n : ℝ) ≠ 0 := by
              exact_mod_cast hn.ne'
            have hx : (n : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 := by
              field_simp [hn0']
            have hyx : Real.sin ((n : ℝ) * (Real.pi / (2 * (n : ℝ)))) = 1 := by
              simp [hx, Real.sin_pi_div_two]
            dsimp [Function.comp]
            rw [hyx]
            norm_num

theorem positive_lam_solution_has_sine_form (lam : ℝ) (hlam : 0 < lam) (y : ℝ → ℝ) (J : Set ℝ) : DirichletEigenfunction lam y J → ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Real.sqrt lam * y x = deriv y 0 * Real.sin (Real.sqrt lam * x) := by
  intro hy
  intro x hx
  let w : ℝ := Real.sqrt lam
  have hwpos : 0 < w := by
    dsimp [w]
    exact Real.sqrt_pos.2 hlam
  have hwsq : w ^ 2 = lam := by
    dsimp [w]
    exact Real.sq_sqrt (le_of_lt hlam)
  rcases hy with ⟨hJopen, hsub, hy', hy'', hy0, hypi, hnonzero⟩
  let A : ℝ → ℝ := fun z => deriv y z * Real.sin (z * w) - Real.cos (z * w) * (y z * w)
  let B : ℝ → ℝ := fun z => deriv y z * Real.cos (z * w) + Real.sin (z * w) * (y z * w)
  have hAderiv : ∀ z ∈ J, HasDerivAt A 0 z := by
    intro z hzJ
    have hyz : HasDerivAt y (deriv y z) z := hy' z hzJ
    have hdyz : HasDerivAt (deriv y) (-(lam * y z)) z := hy'' z hzJ
    have hsin := (Real.hasDerivAt_sin (z * w)).comp z (hasDerivAt_mul_const w)
    have hcos := (Real.hasDerivAt_cos (z * w)).comp z (hasDerivAt_mul_const w)
    have hyw : HasDerivAt (fun t => y t * w) (deriv y z * w) z := by
      simpa using hyz.mul_const w
    have hA' : HasDerivAt A
        (-(lam * y z * Real.sin (z * w)) + deriv y z * (Real.cos (z * w) * w) -
          (-(Real.sin (z * w) * w * (y z * w)) + Real.cos (z * w) * (deriv y z * w))) z := by
      simpa [A] using (hdyz.mul hsin).sub (hcos.mul hyw)
    convert hA' using 1
    ring_nf
    rw [hwsq]
    ring
  have hBderiv : ∀ z ∈ J, HasDerivAt B 0 z := by
    intro z hzJ
    have hyz : HasDerivAt y (deriv y z) z := hy' z hzJ
    have hdyz : HasDerivAt (deriv y) (-(lam * y z)) z := hy'' z hzJ
    have hsin := (Real.hasDerivAt_sin (z * w)).comp z (hasDerivAt_mul_const w)
    have hcos := (Real.hasDerivAt_cos (z * w)).comp z (hasDerivAt_mul_const w)
    have hyw : HasDerivAt (fun t => y t * w) (deriv y z * w) z := by
      simpa using hyz.mul_const w
    have hB' : HasDerivAt B
        (-(lam * y z * Real.cos (z * w)) + -(deriv y z * (Real.sin (z * w) * w)) +
          (Real.cos (z * w) * w * (y z * w) + Real.sin (z * w) * (deriv y z * w))) z := by
      simpa [B] using (hdyz.mul hcos).add (hsin.mul hyw)
    convert hB' using 1
    ring_nf
    rw [hwsq]
    ring
  have hAconst : ∀ z ∈ Set.Icc (0 : ℝ) Real.pi, A z = A 0 := by
    apply constant_of_has_deriv_right_zero
    · intro z hz
      exact (hAderiv z (hsub hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact (hAderiv z (hsub ⟨hz.1, hz.2.le⟩)).hasDerivWithinAt
  have hBconst : ∀ z ∈ Set.Icc (0 : ℝ) Real.pi, B z = B 0 := by
    apply constant_of_has_deriv_right_zero
    · intro z hz
      exact (hBderiv z (hsub hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact (hBderiv z (hsub ⟨hz.1, hz.2.le⟩)).hasDerivWithinAt
  have hAx : A x = 0 := by
    calc
      A x = A 0 := hAconst x hx
      _ = 0 := by
        dsimp [A]
        rw [zero_mul, hy0, zero_mul, Real.sin_zero, Real.cos_zero]
        ring
  have hBx : B x = deriv y 0 := by
    calc
      B x = B 0 := hBconst x hx
      _ = deriv y 0 := by
        dsimp [B]
        rw [zero_mul, hy0, zero_mul, Real.sin_zero, Real.cos_zero]
        ring
  have hsolve' : B x * Real.sin (x * w) - A x * Real.cos (x * w) = y x * w := by
    calc
      B x * Real.sin (x * w) - A x * Real.cos (x * w)
          = (Real.sin (x * w) ^ 2 + Real.cos (x * w) ^ 2) * (y x * w) := by
              dsimp [A, B]
              ring
      _ = y x * w := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hsolve : B x * Real.sin (x * w) - A x * Real.cos (x * w) = w * y x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsolve'
  have : w * y x = deriv y 0 * Real.sin (x * w) := by
    calc
      w * y x = B x * Real.sin (x * w) - A x * Real.cos (x * w) := by
        symm
        exact hsolve
      _ = deriv y 0 * Real.sin (x * w) - 0 * Real.cos (x * w) := by
        rw [hBx, hAx]
      _ = deriv y 0 * Real.sin (x * w) := by ring
  simpa [w, mul_comm, mul_left_comm, mul_assoc] using this

theorem sine_boundary_forces_nat_square (lam : ℝ) (hlam : 0 < lam) : (∃ y J, DirichletEigenfunction lam y J) → ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  intro h
  rcases h with ⟨y, J, hy⟩
  have hDir := hy
  rcases hy with ⟨hJopen, hsubset, hderiv1, hderiv2, hy0, hypi, hnontriv⟩
  have hsine := positive_lam_solution_has_sine_form lam hlam y J hDir
  have hpi := hsine Real.pi ⟨le_of_lt Real.pi_pos, le_rfl⟩
  have hprod : deriv y 0 * Real.sin (Real.sqrt lam * Real.pi) = 0 := by
    simpa only [hypi, mul_zero] using hpi.symm
  have hderiv0_ne : deriv y 0 ≠ 0 := by
    intro hzero
    rcases hnontriv with ⟨x, hxIoo, hxne⟩
    have hx : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
    have hxEq0 : Real.sqrt lam * y x = 0 := by
      simpa only [hzero, zero_mul] using hsine x hx
    have hsqrt_ne : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlam)
    have hyx0 : y x = 0 := by
      rcases mul_eq_zero.mp hxEq0 with hsqrt0 | hyx0
      · exact False.elim (hsqrt_ne hsqrt0)
      · exact hyx0
    exact hxne hyx0
  have hsin_zero : Real.sin (Real.sqrt lam * Real.pi) = 0 := by
    rcases mul_eq_zero.mp hprod with hzero | hsin_zero
    · exact False.elim (hderiv0_ne hzero)
    · exact hsin_zero
  rcases Real.sin_eq_zero_iff.mp hsin_zero with ⟨z, hz⟩
  have hsqrt_eq' : (z : ℝ) = Real.sqrt lam := by
    exact mul_right_cancel₀ Real.pi_ne_zero hz
  have hz_pos : 0 < z := by
    have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
    have hz_pos_real : 0 < (z : ℝ) := by
      simpa only [hsqrt_eq'] using hsqrt_pos
    exact Int.cast_pos.mp hz_pos_real
  have hz_nonneg : 0 ≤ z := le_of_lt hz_pos
  have hz_cast : ((Int.toNat z : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
  have hn_pos_int : (0 : ℤ) < ((Int.toNat z : ℕ) : ℤ) := by
    simpa only [hz_cast] using hz_pos
  have hn_pos : 0 < Int.toNat z := by
    exact_mod_cast hn_pos_int
  refine ⟨Int.toNat z, hn_pos, ?_⟩
  have hz_cast_real : ((Int.toNat z : ℕ) : ℝ) = (z : ℝ) := by
    exact_mod_cast hz_cast
  calc
    lam = (Real.sqrt lam) ^ 2 := by
      symm
      exact Real.sq_sqrt (le_of_lt hlam)
    _ = ((z : ℝ)) ^ 2 := by rw [hsqrt_eq'.symm]
    _ = ((Int.toNat z : ℕ) : ℝ) ^ 2 := by rw [hz_cast_real.symm]

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  change ((∃ y J, DirichletEigenfunction lam y J) ↔ ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2)
  constructor
  · intro h
    by_cases hlt : lam < 0
    · exact (dirichlet_solution_not_lam_lt_zero lam hlt h).elim
    · by_cases hzero : lam = 0
      · exfalso
        have h0 : ∃ y J, DirichletEigenfunction 0 y J := by
          simpa [hzero] using h
        exact dirichlet_solution_not_lam_eq_zero h0
      · have hle : 0 ≤ lam := le_of_not_gt hlt
        have hne : (0 : ℝ) ≠ lam := by
          simpa [eq_comm] using hzero
        have hpos : 0 < lam := lt_of_le_of_ne hle hne
        exact sine_boundary_forces_nat_square lam hpos h
  · rintro ⟨n, hn, rfl⟩
    exact nat_sq_implies_dirichlet_solution n hn


end Submission
