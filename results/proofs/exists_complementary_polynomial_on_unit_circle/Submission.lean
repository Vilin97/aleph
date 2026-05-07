import Mathlib
import Submission.Helpers

open Polynomial

namespace Submission

noncomputable def starReflect (n : ℕ) (p : ℂ[X]) : ℂ[X] := (p.map (starRingEnd ℂ)).reflect n

theorem starReflect_eval_circle (n : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ n) : ∀ z : Circle, (starReflect n p).eval (z : ℂ) = star (p.eval (z : ℂ)) * (z : ℂ) ^ n := by
  intro z
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  letI : Invertible ((z : ℂ)⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  have hmain :
      (starReflect n p).eval (z : ℂ) * ((z : ℂ)⁻¹) ^ n =
        (p.map (starRingEnd ℂ)).eval ((z : ℂ)⁻¹) := by
    simpa [starReflect] using
      (Polynomial.eval₂_reflect_mul_pow (i := RingHom.id ℂ) (x := ((z : ℂ)⁻¹))
        (N := n) (f := p.map (starRingEnd ℂ)) (by simpa using hp))
  have hzstar : (z : ℂ)⁻¹ = star (z : ℂ) := by
    rw [Complex.star_def]
    exact (Circle.coe_inv z).symm.trans (Circle.coe_inv_eq_conj z)
  have hstar : (p.map (starRingEnd ℂ)).eval ((z : ℂ)⁻¹) = star (p.eval (z : ℂ)) := by
    rw [hzstar]
    simpa using (Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ) (x := (z : ℂ)))
  rw [hstar] at hmain
  have h := congrArg (fun w : ℂ => w * (z : ℂ) ^ n) hmain
  simpa [mul_assoc, ← mul_pow, hz] using h

theorem starReflect_involutive (n : ℕ) (p : ℂ[X]) : starReflect n (starReflect n p) = p := by
  unfold starReflect
  rw [reflect_map]
  rw [reflect_reflect]
  rw [Polynomial.map_map]
  simp

theorem starReflect_mul (F G : ℕ) (p q : ℂ[X]) (hp : p.natDegree ≤ F) (hq : q.natDegree ≤ G) : starReflect (F + G) (p * q) = starReflect F p * starReflect G q := by
  unfold starReflect
  rw [Polynomial.map_mul]
  exact Polynomial.reflect_mul (p.map (starRingEnd ℂ)) (q.map (starRingEnd ℂ)) (by simpa using hp) (by simpa using hq)

noncomputable def unitAux (p : ℂ[X]) : ℂ[X] := X ^ p.natDegree - p * starReflect p.natDegree p

theorem unitAux_eval_circle (P : ℂ[X]) : ∀ z : Circle, (unitAux P).eval (z : ℂ) = ((((1 : ℝ) - ‖P.eval (z : ℂ)‖ ^ 2) : ℂ)) * (z : ℂ) ^ P.natDegree := by
  intro z
  have hmul : P.eval (z : ℂ) * star (P.eval (z : ℂ)) = ((‖P.eval (z : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    simpa using (Complex.mul_conj' (P.eval (z : ℂ)))
  calc
    (unitAux P).eval (z : ℂ)
        = (z : ℂ) ^ P.natDegree - P.eval (z : ℂ) * (starReflect P.natDegree P).eval (z : ℂ) := by
            simp only [unitAux, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
              Polynomial.eval_X]
    _ = (z : ℂ) ^ P.natDegree - P.eval (z : ℂ) * (star (P.eval (z : ℂ)) * (z : ℂ) ^ P.natDegree) := by
            rw [starReflect_eval_circle P.natDegree P le_rfl z]
    _ = (z : ℂ) ^ P.natDegree - ((‖P.eval (z : ℂ)‖ ^ 2 : ℝ) : ℂ) * (z : ℂ) ^ P.natDegree := by
            rw [← mul_assoc, hmul]
    _ = ((((1 : ℝ) - ‖P.eval (z : ℂ)‖ ^ 2) : ℂ)) * (z : ℂ) ^ P.natDegree := by
            simpa [sub_mul, mul_comm, mul_left_comm, mul_assoc]

theorem unitAux_self_adjoint (P : ℂ[X]) : starReflect (P.natDegree + P.natDegree) (unitAux P) = unitAux P := by
  unfold unitAux starReflect
  have hrev : Polynomial.revAt (P.natDegree + P.natDegree) P.natDegree = P.natDegree := by
    calc
      Polynomial.revAt (P.natDegree + P.natDegree) P.natDegree =
          (P.natDegree + P.natDegree) - P.natDegree := by
            rw [Polynomial.revAt_le (H := by omega)]
      _ = P.natDegree := by
        omega
  have hdeg1 : (P.map (starRingEnd ℂ)).natDegree ≤ P.natDegree := by
    exact Polynomial.natDegree_map_le
  have hdeg2 : (((P.map (starRingEnd ℂ)).reflect P.natDegree).map (starRingEnd ℂ)).natDegree ≤
      P.natDegree := by
    calc
      (((P.map (starRingEnd ℂ)).reflect P.natDegree).map (starRingEnd ℂ)).natDegree ≤
          ((P.map (starRingEnd ℂ)).reflect P.natDegree).natDegree :=
            Polynomial.natDegree_map_le
      _ ≤ max P.natDegree (P.map (starRingEnd ℂ)).natDegree :=
            Polynomial.natDegree_reflect_le
      _ ≤ P.natDegree := by
            exact max_le le_rfl Polynomial.natDegree_map_le
  have hmapmap (Q : ℂ[X]) : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q := by
    ext i
    simp [Polynomial.coeff_map, starRingEnd_self_apply]
  calc
    reflect (P.natDegree + P.natDegree)
        (map (starRingEnd ℂ) (X ^ P.natDegree - P * reflect P.natDegree (map (starRingEnd ℂ) P))) =
        reflect (P.natDegree + P.natDegree) ((X ^ P.natDegree).map (starRingEnd ℂ)) -
          reflect (P.natDegree + P.natDegree)
            ((P * reflect P.natDegree (map (starRingEnd ℂ) P)).map (starRingEnd ℂ)) := by
          rw [Polynomial.map_sub, Polynomial.reflect_sub]
    _ = X ^ P.natDegree -
          reflect (P.natDegree + P.natDegree)
            ((P * reflect P.natDegree (map (starRingEnd ℂ) P)).map (starRingEnd ℂ)) := by
          rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.reflect_monomial, hrev]
    _ = X ^ P.natDegree -
          (map (starRingEnd ℂ) (reflect P.natDegree P) *
            reflect P.natDegree (map (starRingEnd ℂ) (map (starRingEnd ℂ) (reflect P.natDegree P)))) := by
          rw [Polynomial.map_mul,
            Polynomial.reflect_mul
              (f := P.map (starRingEnd ℂ))
              (g := ((reflect P.natDegree (P.map (starRingEnd ℂ))).map (starRingEnd ℂ)))
              (F := P.natDegree) (G := P.natDegree) hdeg1 hdeg2,
            Polynomial.reflect_map]
    _ = X ^ P.natDegree - (map (starRingEnd ℂ) (reflect P.natDegree P) * P) := by
          rw [hmapmap (reflect P.natDegree P), Polynomial.reflect_reflect]
    _ = X ^ P.natDegree - P * map (starRingEnd ℂ) (reflect P.natDegree P) := by
          rw [mul_comm]
    _ = X ^ P.natDegree - P * reflect P.natDegree (map (starRingEnd ℂ) P) := by
          rw [← Polynomial.reflect_map (f := starRingEnd ℂ) (p := P) (n := P.natDegree)]

theorem exists_square_factor_of_unitAux (P : ℂ[X]) (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) : ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧ unitAux P = Q * starReflect P.natDegree Q := by
  sorry

theorem exists_complementary_polynomial_on_unit_circle (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  rcases exists_square_factor_of_unitAux P hP with ⟨Q, hQdeg, hfac⟩
  refine ⟨Q, hQdeg, ?_⟩
  intro z
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have heval : (unitAux P).eval (z : ℂ) = (Q * starReflect P.natDegree Q).eval (z : ℂ) := by
    simpa using congrArg (fun R : ℂ[X] => R.eval (z : ℂ)) hfac
  rw [unitAux_eval_circle P z, eval_mul, starReflect_eval_circle P.natDegree Q hQdeg z] at heval
  have hzpow : (z : ℂ) ^ P.natDegree ≠ 0 := pow_ne_zero P.natDegree hz
  have hc : (((1 : ℝ) - ‖P.eval (z : ℂ)‖ ^ 2 : ℝ) : ℂ) = ((Q.eval (z : ℂ)) * star (Q.eval (z : ℂ)) : ℂ) := by
    apply mul_right_cancel₀ hzpow
    simpa [mul_assoc] using heval
  have hreal : (1 : ℝ) - ‖P.eval (z : ℂ)‖ ^ 2 = ‖Q.eval (z : ℂ)‖ ^ 2 := by
    apply Complex.ofReal_injective
    simpa [Complex.mul_conj'] using hc
  linarith


end Submission
