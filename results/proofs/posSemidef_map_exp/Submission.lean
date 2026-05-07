import Mathlib
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

theorem hasSum_map_exp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} : HasSum (fun k => ((Nat.factorial k : ℝ)⁻¹) • A.map (fun x => x ^ k)) (A.map Real.exp) := by
  refine (Pi.hasSum).2 ?_
  intro i
  refine (Pi.hasSum).2 ?_
  intro j
  simpa [Matrix.map_apply, Pi.smul_apply, smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) (A i j))

theorem posSemidef_map_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) : ∀ k : ℕ, (A.map (fun x => x ^ k)).PosSemidef := by
  intro k
  induction k with
  | zero =>
      classical
      rw [show A.map (fun x => x ^ 0) = Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) by
        ext i j
        simp [Matrix.vecMulVec]]
      simpa using Matrix.posSemidef_vecMulVec_self_star (fun _ : n => (1 : ℝ))
  | succ k ih =>
      have hpow : A.map (fun x => x ^ (k + 1)) = (A.map (fun x => x ^ k)).hadamard A := by
        ext i j
        simp [pow_succ]
      rw [hpow]
      exact ih.hadamard hA

theorem posSemidef_tsum {n : Type*} [Fintype n] [DecidableEq n] {f : ℕ → Matrix n n ℝ} (hf : Summable f) (hpsd : ∀ k, (f k).PosSemidef) : (tsum f).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_tsum]
    refine tsum_congr ?_
    intro k
    exact (hpsd k).isHermitian.eq
  · intro x
    let ψ : Matrix n n ℝ →ₗ[ℝ] n → ℝ :=
      (LinearMap.applyₗ x).comp (Matrix.mulVecBilin ℝ ℝ)
    let φ : Matrix n n ℝ →ₗ[ℝ] ℝ :=
      ((dotProductBilin ℝ ℝ) (star x)).comp ψ
    have hφ : φ (tsum f) = ∑' k, φ (f k) :=
      (LinearMap.toContinuousLinearMap φ).map_tsum hf
    have hk : ∀ k, 0 ≤ φ (f k) := by
      intro k
      simpa [φ, ψ] using (hpsd k).dotProduct_mulVec_nonneg x
    calc
      0 ≤ ∑' k, φ (f k) := tsum_nonneg hk
      _ = φ (tsum f) := by symm; exact hφ
      _ = dotProduct (star x) (Matrix.mulVec (tsum f) x) := by simp [φ, ψ]
    

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  let f : ℕ → Matrix n n ℝ := fun k => ((Nat.factorial k : ℝ)⁻¹) • A.map (fun x => x ^ k)
  have hsum : HasSum f (A.map Real.exp) := by
    simpa only [f] using (hasSum_map_exp (A := A))
  have hpsd : ∀ k : ℕ, (f k).PosSemidef := by
    intro k
    exact (posSemidef_map_pow hA k).smul (by positivity)
  have htsum : (tsum f).PosSemidef := posSemidef_tsum hsum.summable hpsd
  simpa only [hsum.tsum_eq] using htsum


end Submission
