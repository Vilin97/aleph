import Mathlib
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

theorem det_mono_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℝ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : (Y - X).PosSemidef) :
    X.det ≤ Y.det := by
  classical
  have rank_one_step : ∀ {A : Matrix n n ℝ}, A.PosDef → ∀ u : n → ℝ,
      A.det ≤ (A + Matrix.vecMulVec u u).det := by
    intro A hA u
    have houter : Matrix.vecMulVec u u = Matrix.replicateCol Unit u * Matrix.replicateRow Unit u := by
      simpa using Matrix.vecMulVec_eq (ι := Unit) u u
    have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
    have hdet := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) (A := A) hAunit u u
    have hMpsd : (Matrix.replicateRow Unit u * A⁻¹ * Matrix.replicateCol Unit u).PosSemidef := by
      simpa using hA.inv.posSemidef.conjTranspose_mul_mul_same (Matrix.replicateCol Unit u)
    have hdiag : 0 ≤ (Matrix.replicateRow Unit u * A⁻¹ * Matrix.replicateCol Unit u) () () := by
      simpa using hMpsd.diag_nonneg (i := ())
    have hone : 1 ≤ (1 + Matrix.replicateRow Unit u * A⁻¹ * Matrix.replicateCol Unit u).det := by
      simpa [Matrix.det_fin_one] using add_le_add_left hdiag 1
    calc
      A.det ≤ A.det * (1 + Matrix.replicateRow Unit u * A⁻¹ * Matrix.replicateCol Unit u).det := by
        nlinarith [hA.det_pos, hone]
      _ = (A + Matrix.replicateCol Unit u * Matrix.replicateRow Unit u).det := by
        symm
        exact hdet
      _ = (A + Matrix.vecMulVec u u).det := by rw [houter]
  have hpd_sum_rankone : ∀ {m : ℕ} (v : Fin m → n → ℝ) {A : Matrix n n ℝ}, A.PosDef →
      A.det ≤ (A + ∑ i, Matrix.vecMulVec (v i) (v i)).det := by
    intro m
    induction m with
    | zero =>
        intro v A hA
        simpa using le_rfl
    | succ m ih =>
        intro v A hA
        have hSpsd : (∑ i : Fin m, Matrix.vecMulVec (v i.castSucc) (v i.castSucc)).PosSemidef := by
          simpa using Matrix.posSemidef_sum (x := fun i : Fin m => Matrix.vecMulVec (v i.castSucc) (v i.castSucc))
            Finset.univ (by
              intro i hi
              simpa using Matrix.posSemidef_vecMulVec_self_star (v i.castSucc))
        have hA' : (A + ∑ i : Fin m, Matrix.vecMulVec (v i.castSucc) (v i.castSucc)).PosDef := by
          exact hA.add_posSemidef hSpsd
        have h1 := ih (fun i => v i.castSucc) (A := A) hA
        have h2 := rank_one_step hA' (v (Fin.last m))
        have hsum : (∑ i : Fin (m + 1), Matrix.vecMulVec (v i) (v i)) =
            (∑ i : Fin m, Matrix.vecMulVec (v i.castSucc) (v i.castSucc)) +
              Matrix.vecMulVec (v (Fin.last m)) (v (Fin.last m)) := by
          rw [Fin.sum_univ_castSucc]
        simpa [hsum, add_assoc] using le_trans h1 h2
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < ε k := by
    intro k
    dsimp [ε]
    positivity
  have hdet_eps : ∀ k, (X + ε k • (1 : Matrix n n ℝ)).det ≤ (Y + ε k • (1 : Matrix n n ℝ)).det := by
    intro k
    have hεI : (ε k • (1 : Matrix n n ℝ)).PosDef := by
      exact Matrix.PosDef.smul (x := (1 : Matrix n n ℝ)) Matrix.PosDef.one (hεpos k)
    have hXk : (X + ε k • (1 : Matrix n n ℝ)).PosDef := by
      exact Matrix.PosDef.posSemidef_add hX hεI
    have hDiff : (Y + ε k • (1 : Matrix n n ℝ) - (X + ε k • (1 : Matrix n n ℝ))).PosSemidef := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hXY
    obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hDiff
    have := hpd_sum_rankone v (A := X + ε k • (1 : Matrix n n ℝ)) hXk
    have hrewrite : Y + ε k • (1 : Matrix n n ℝ) =
        X + ε k • (1 : Matrix n n ℝ) + ∑ i, Matrix.vecMulVec (v i) (v i) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_eq_iff_eq_add'.mp hv
    simpa [hrewrite] using this
  have hXt : Filter.Tendsto (fun k => (X + ε k • (1 : Matrix n n ℝ)).det) Filter.atTop (nhds X.det) := by
    have hcont : Continuous fun r : ℝ => (X + r • (1 : Matrix n n ℝ)).det := by
      fun_prop
    simpa [ε] using hcont.tendsto 0 |>.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hYt : Filter.Tendsto (fun k => (Y + ε k • (1 : Matrix n n ℝ)).det) Filter.atTop (nhds Y.det) := by
    have hcont : Continuous fun r : ℝ => (Y + r • (1 : Matrix n n ℝ)).det := by
      fun_prop
    simpa [ε] using hcont.tendsto 0 |>.comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto' hXt hYt hdet_eps

theorem det_nonneg_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) : 0 ≤ M.det := by
  simpa using hM.det_nonneg

theorem hadamard_fromBlocks_fin1 {n : Type*} [Fintype n] [DecidableEq n]
    {A11 : Matrix (Fin 1) (Fin 1) ℝ} {U V : Matrix n (Fin 1) ℝ}
    {A22 C22 : Matrix n n ℝ} :
    Matrix.hadamard (Matrix.fromBlocks A11 U.transpose U A22)
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) V.transpose V C22) =
      Matrix.fromBlocks A11 (Matrix.hadamard U V).transpose (Matrix.hadamard U V)
        (Matrix.hadamard A22 C22) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have h : i = j := Subsingleton.elim _ _
          simp [Matrix.hadamard_apply, Matrix.transpose_apply, Matrix.one_apply, h]
      | inr j =>
          simp [Matrix.hadamard_apply, Matrix.transpose_apply]
  | inr i =>
      cases j with
      | inl j =>
          simp [Matrix.hadamard_apply, Matrix.transpose_apply]
      | inr j =>
          simp [Matrix.hadamard_apply, Matrix.transpose_apply]

theorem hadamard_schur_split_fin1 {n : Type*} [Fintype n] [DecidableEq n]
    {A11 : Matrix (Fin 1) (Fin 1) ℝ} [Invertible A11]
    {U V : Matrix n (Fin 1) ℝ} {A22 C22 : Matrix n n ℝ} :
    Matrix.hadamard A22 C22 - (Matrix.hadamard U V) * A11⁻¹ * (Matrix.hadamard U V).transpose =
      Matrix.hadamard (A22 - U * A11⁻¹ * U.transpose) C22 +
      Matrix.hadamard (U * A11⁻¹ * U.transpose) (C22 - V * V.transpose) := by
  ext i j
  simp only [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_one]
  ring

theorem hadamard_vecMulVec_eq_diagonal_mul_mul_diagonal {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (v : n → ℝ) :
    Matrix.hadamard A (Matrix.vecMulVec v v) = Matrix.diagonal v * A * Matrix.diagonal v := by
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.vecMulVec, mul_assoc, mul_left_comm, mul_comm]

theorem posDef_of_posSemidef_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (hdet : M.det ≠ 0) : M.PosDef := by
  classical
  rcases Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM with ⟨m, v, hMv⟩
  let A : Matrix n (Fin m) ℝ := fun j i => v i j
  have hAeq : (∑ i, Matrix.vecMulVec (v i) (v i)) = A * A.transpose := by
    ext j k
    simp_rw [Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, A]
  have hM' : M = A * A.transpose := by
    calc
      M = ∑ i, Matrix.vecMulVec (v i) (star (v i)) := hMv
      _ = ∑ i, Matrix.vecMulVec (v i) (v i) := by simp
      _ = A * A.transpose := hAeq
  have hAinj : Function.Injective A.vecMul := by
    have hU : IsUnit (A * A.transpose) :=
      (Matrix.isUnit_iff_isUnit_det (A := A * A.transpose)).2
        (isUnit_iff_ne_zero.2 (by simpa [hM'] using hdet))
    have hMinj : Function.Injective (A * A.transpose).vecMul :=
      (Matrix.vecMul_injective_iff_isUnit).2 hU
    intro x y hxy
    apply hMinj
    simpa [Matrix.vecMul_vecMul] using congrArg (fun z => Matrix.vecMul z A.transpose) hxy
  simpa [hM'] using Matrix.PosDef.mul_conjTranspose_self A hAinj

theorem schur_product_theorem_real {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (Matrix.hadamard A B).PosSemidef := by
  simpa using hA.hadamard hB

theorem oppenheim_diag_one_core {n : Type*} [Fintype n] [DecidableEq n] {A C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosSemidef) (hdiag : ∀ i, C i i = 1) :
    A.det ≤ (Matrix.hadamard A C).det := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ {A C : Matrix (Fin k) (Fin k) ℝ},
      A.PosDef → C.PosSemidef → (∀ i, C i i = 1) → A.det ≤ (Matrix.hadamard A C).det
  have hP : ∀ k, P k := by
    intro k
    induction k with
    | zero =>
        intro A C hA hC hdiag
        simp
    | succ k ih =>
        intro A C hA hC hdiag
        let e : Fin 1 ⊕ Fin k ≃ Fin (k + 1) := (Equiv.sumComm (Fin 1) (Fin k)).trans finSumFinEquiv
        let A0 : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ := A.submatrix e e
        let C0 : Matrix (Fin 1 ⊕ Fin k) (Fin 1 ⊕ Fin k) ℝ := C.submatrix e e
        have hA0 : A0.PosDef := by
          simpa [A0] using hA.submatrix e.injective
        have hC0 : C0.PosSemidef := by
          simpa [A0, C0] using hC.submatrix e
        have hdiag0 : ∀ i, C0 i i = 1 := by
          intro i
          simpa [C0] using hdiag (e i)
        let A11 : Matrix (Fin 1) (Fin 1) ℝ := A0.toBlocks₁₁
        let A12 : Matrix (Fin 1) (Fin k) ℝ := A0.toBlocks₁₂
        let U : Matrix (Fin k) (Fin 1) ℝ := A12.transpose
        let A22 : Matrix (Fin k) (Fin k) ℝ := A0.toBlocks₂₂
        let C11 : Matrix (Fin 1) (Fin 1) ℝ := C0.toBlocks₁₁
        let C12 : Matrix (Fin 1) (Fin k) ℝ := C0.toBlocks₁₂
        let V : Matrix (Fin k) (Fin 1) ℝ := C12.transpose
        let C22 : Matrix (Fin k) (Fin k) ℝ := C0.toBlocks₂₂
        have hA12 : A12.transpose = A0.toBlocks₂₁ := by
          have hherm : A0.IsHermitian := hA0.isHermitian
          have hherm' : (Matrix.fromBlocks A0.toBlocks₁₁ A0.toBlocks₁₂ A0.toBlocks₂₁ A0.toBlocks₂₂).IsHermitian := by
            simpa [Matrix.fromBlocks_toBlocks] using hherm
          simpa [A12] using (Matrix.isHermitian_fromBlocks_iff.mp hherm').2.1
        have hA12' : U.transpose = A12 := by
          simpa [U] using congrArg Matrix.transpose hA12
        have hC12 : C12.transpose = C0.toBlocks₂₁ := by
          have hherm : C0.IsHermitian := hC0.isHermitian
          have hherm' : (Matrix.fromBlocks C0.toBlocks₁₁ C0.toBlocks₁₂ C0.toBlocks₂₁ C0.toBlocks₂₂).IsHermitian := by
            simpa [Matrix.fromBlocks_toBlocks] using hherm
          simpa [C12] using (Matrix.isHermitian_fromBlocks_iff.mp hherm').2.1
        have hC12' : V.transpose = C12 := by
          simpa [V] using congrArg Matrix.transpose hC12
        have hA0eq : Matrix.fromBlocks A11 U.transpose U A22 = A0 := by
          rw [hA12', show U = A0.toBlocks₂₁ by simpa [U] using hA12]
          simpa [A11, A12, A22] using (Matrix.fromBlocks_toBlocks A0)
        have hC11 : C11 = 1 := by
          ext i j
          fin_cases i
          fin_cases j
          simpa [C11] using hdiag0 (Sum.inl 0)
        have hC0eq : Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) V.transpose V C22 = C0 := by
          rw [hC12', show V = C0.toBlocks₂₁ by simpa [V] using hC12]
          simpa [C11, C12, C22, hC11] using (Matrix.fromBlocks_toBlocks C0)
        have hA11 : A11.PosDef := by
          simpa [A11] using hA0.submatrix (fun a b h => by cases h; rfl)
        have hC22 : C22.PosSemidef := by
          simpa [C22] using hC0.submatrix (fun i => Sum.inr i)
        have hdiag22 : ∀ i, C22 i i = 1 := by
          intro i
          simpa [C22] using hdiag0 (Sum.inr i)
        haveI : Invertible A11 := hA11.isUnit.invertible
        let SA : Matrix (Fin k) (Fin k) ℝ := A22 - U * A11⁻¹ * U.transpose
        have hSApsd : SA.PosSemidef := by
          have htmp : (Matrix.fromBlocks A11 U.transpose U A22).PosSemidef := by
            rw [hA0eq]
            exact hA0.posSemidef
          simpa [SA] using (Matrix.PosDef.fromBlocks₁₁ (B := U.transpose) (D := A22) hA11).mp htmp
        have hSA : SA.PosDef := by
          have hdetA0nz : A0.det ≠ 0 := by
            exact ((Matrix.isUnit_iff_isUnit_det A0).mp hA0.isUnit).ne_zero
          have hdetA0 : A0.det = A11.det * SA.det := by
            rw [← hA0eq]
            simpa [SA] using (Matrix.det_fromBlocks₁₁ A11 U.transpose U A22)
          have hdetSAnz : SA.det ≠ 0 := by
            intro hzero
            apply hdetA0nz
            rw [hdetA0, hzero, mul_zero]
          exact posDef_of_posSemidef_det_ne_zero hSApsd hdetSAnz
        let SC : Matrix (Fin k) (Fin k) ℝ := C22 - V * V.transpose
        letI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
        have hSC : SC.PosSemidef := by
          have htmp : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) V.transpose V C22).PosSemidef := by
            rw [hC0eq]
            exact hC0
          simpa [SC] using
            (Matrix.PosDef.fromBlocks₁₁ (B := V.transpose) (D := C22)
              (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)).mp htmp
        have hIH : SA.det ≤ (Matrix.hadamard SA C22).det := by
          exact ih hSA hC22 hdiag22
        have hH0eq : Matrix.hadamard A0 C0 =
            Matrix.fromBlocks A11 (Matrix.hadamard U V).transpose (Matrix.hadamard U V) (Matrix.hadamard A22 C22) := by
          rw [← hA0eq, ← hC0eq]
          simpa using (hadamard_fromBlocks_fin1 (A11 := A11) (U := U) (V := V) (A22 := A22) (C22 := C22))
        let S : Matrix (Fin k) (Fin k) ℝ := Matrix.hadamard A22 C22 - (Matrix.hadamard U V) * A11⁻¹ * (Matrix.hadamard U V).transpose
        have hSsplit : S =
            Matrix.hadamard SA C22 +
            Matrix.hadamard (U * A11⁻¹ * U.transpose) SC := by
          simpa [SA, SC, S] using
            (hadamard_schur_split_fin1 (A11 := A11) (U := U) (V := V) (A22 := A22) (C22 := C22))
        have hKpsd : (U * A11⁻¹ * U.transpose).PosSemidef := by
          simpa using (Matrix.PosSemidef.mul_mul_conjTranspose_same hA11.inv.posSemidef U)
        have hextra : (Matrix.hadamard (U * A11⁻¹ * U.transpose) SC).PosSemidef := by
          exact schur_product_theorem_real hKpsd hSC
        have hbase : (Matrix.hadamard SA C22).PosSemidef := by
          exact schur_product_theorem_real hSApsd hC22
        have hSpsd : S.PosSemidef := by
          rw [hSsplit]
          exact hbase.add hextra
        have hSdiff : (S - Matrix.hadamard SA C22) = Matrix.hadamard (U * A11⁻¹ * U.transpose) SC := by
          calc
            S - Matrix.hadamard SA C22 =
                (Matrix.hadamard SA C22 + Matrix.hadamard (U * A11⁻¹ * U.transpose) SC) -
                  Matrix.hadamard SA C22 := by rw [hSsplit]
            _ = Matrix.hadamard (U * A11⁻¹ * U.transpose) SC := by
              abel
        have hdiff : (S - Matrix.hadamard SA C22).PosSemidef := by
          rw [hSdiff]
          exact hextra
        have hdet_le : (Matrix.hadamard SA C22).det ≤ S.det := by
          exact det_mono_of_posSemidef hbase hSpsd hdiff
        have hSAleS : SA.det ≤ S.det := le_trans hIH hdet_le
        have hA11detpos : 0 < A11.det := by
          have hdiagpos : 0 < A11 0 0 := Matrix.PosDef.diag_pos hA11
          simpa [Matrix.det_fin_one] using hdiagpos
        have hdetA0 : A0.det = A11.det * SA.det := by
          rw [← hA0eq]
          simpa [SA] using (Matrix.det_fromBlocks₁₁ A11 U.transpose U A22)
        have hdetH0 : (Matrix.hadamard A0 C0).det = A11.det * S.det := by
          rw [hH0eq]
          simpa [S] using (Matrix.det_fromBlocks₁₁ A11 (Matrix.hadamard U V).transpose (Matrix.hadamard U V) (Matrix.hadamard A22 C22))
        have hA0le : A0.det ≤ (Matrix.hadamard A0 C0).det := by
          rw [hdetA0, hdetH0]
          exact mul_le_mul_of_nonneg_left hSAleS hA11detpos.le
        have hHsub : Matrix.hadamard A0 C0 = (Matrix.hadamard A C).submatrix e e := by
          ext i j
          simp [A0, C0, Matrix.hadamard_apply]
        rw [show A0.det = A.det by simpa [A0] using (Matrix.det_submatrix_equiv_self e A)] at hA0le
        rw [hHsub, Matrix.det_submatrix_equiv_self e (Matrix.hadamard A C)] at hA0le
        exact hA0le
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let A0 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ := A.submatrix e.symm e.symm
  let C0 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ := C.submatrix e.symm e.symm
  have hA0 : A0.PosDef := by
    simpa [A0] using hA.submatrix e.symm.injective
  have hC0 : C0.PosSemidef := by
    simpa [A0, C0] using hC.submatrix e.symm
  have hdiag0 : ∀ i, C0 i i = 1 := by
    intro i
    simpa [C0] using hdiag (e.symm i)
  have hmain : A0.det ≤ (Matrix.hadamard A0 C0).det := by
    exact hP (Fintype.card n) hA0 hC0 hdiag0
  have hHsub : Matrix.hadamard A0 C0 = (Matrix.hadamard A C).submatrix e.symm e.symm := by
    ext i j
    simp [A0, C0, Matrix.hadamard_apply]
  rw [show A0.det = A.det by simpa [A0] using (Matrix.det_submatrix_equiv_self e.symm A)] at hmain
  rw [hHsub, Matrix.det_submatrix_equiv_self e.symm (Matrix.hadamard A C)] at hmain
  exact hmain

theorem oppenheim_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  classical
  have hABpsd : (Matrix.hadamard A B).PosSemidef := schur_product_theorem_real hA hB
  have hABdet_nonneg : 0 ≤ (Matrix.hadamard A B).det := det_nonneg_of_posSemidef hABpsd
  by_cases hdetA : A.det = 0
  · rw [hdetA]
    simp
    exact hABdet_nonneg
  · have hApos : A.PosDef := posDef_of_posSemidef_det_ne_zero hA hdetA
    by_cases hprod : Finset.univ.prod (fun i => B i i) = 0
    · rw [hprod, mul_zero]
      exact hABdet_nonneg
    · have hdiag_ne : ∀ i, B i i ≠ 0 := by
        intro i
        exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
      have hdiag_pos : ∀ i, 0 < B i i := by
        intro i
        have hnonneg : 0 ≤ B i i := hB.diag_nonneg
        have h0ne : 0 ≠ B i i := by
          exact fun h => hdiag_ne i h.symm
        exact lt_of_le_of_ne hnonneg h0ne
      let d : n → ℝ := fun i => Real.sqrt (B i i)
      let D : Matrix n n ℝ := Matrix.diagonal d
      let C : Matrix n n ℝ := Matrix.diagonal (fun i => (d i)⁻¹) * B * Matrix.diagonal (fun i => (d i)⁻¹)
      have hC : C.PosSemidef := by
        dsimp [C]
        simpa [d] using hB.mul_mul_conjTranspose_same (B := Matrix.diagonal (fun i => (d i)⁻¹))
      have hdiag : ∀ i, C i i = 1 := by
        intro i
        have hsqrt_ne : Real.sqrt (B i i) ≠ 0 := Real.sqrt_ne_zero'.2 (hdiag_pos i)
        dsimp [C, d]
        simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
        field_simp [hsqrt_ne]
        nlinarith [Real.sq_sqrt (show 0 ≤ B i i by exact hB.diag_nonneg)]
      have hcore : A.det ≤ (Matrix.hadamard A C).det := oppenheim_diag_one_core hApos hC hdiag
      have hhad : Matrix.hadamard A B = D * Matrix.hadamard A C * D := by
        ext i j
        have hsqrt_ne_i : Real.sqrt (B i i) ≠ 0 := Real.sqrt_ne_zero'.2 (hdiag_pos i)
        have hsqrt_ne_j : Real.sqrt (B j j) ≠ 0 := Real.sqrt_ne_zero'.2 (hdiag_pos j)
        dsimp [D, C, d]
        simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
        field_simp [hsqrt_ne_i, hsqrt_ne_j]
      have hDsq : D * D = Matrix.diagonal (fun i => B i i) := by
        ext i j
        dsimp [D, d]
        by_cases hij : i = j
        · subst hij
          simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Real.sq_sqrt, hB.diag_nonneg]
        · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hij]
      have hprod_nonneg : 0 ≤ Finset.univ.prod (fun i => B i i) := by
        exact Finset.prod_nonneg (fun i hi => hB.diag_nonneg)
      have hdet_eq : (Matrix.hadamard A B).det = Finset.univ.prod (fun i => B i i) * (Matrix.hadamard A C).det := by
        calc
          (Matrix.hadamard A B).det = (D * Matrix.hadamard A C * D).det := by rw [hhad]
          _ = (D * Matrix.hadamard A C).det * D.det := by rw [Matrix.det_mul]
          _ = (D.det * (Matrix.hadamard A C).det) * D.det := by rw [Matrix.det_mul]
          _ = (D.det * D.det) * (Matrix.hadamard A C).det := by ring
          _ = (D * D).det * (Matrix.hadamard A C).det := by rw [← Matrix.det_mul]
          _ = Finset.univ.prod (fun i => B i i) * (Matrix.hadamard A C).det := by rw [hDsq, Matrix.det_diagonal]
      rw [hdet_eq, mul_comm A.det]
      exact mul_le_mul_of_nonneg_left hcore hprod_nonneg


end Submission
