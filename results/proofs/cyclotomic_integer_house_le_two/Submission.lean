import Mathlib
import Submission.Helpers

open NumberField

namespace Submission

theorem abs_cos_le_cos_of_mem_Icc_pi_sub {a x : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ Real.pi / 2) (hxa : a ≤ x) (hxp : x ≤ Real.pi - a) : |Real.cos x| ≤ Real.cos a := by
  have hx0 : 0 ≤ x := le_trans ha0 hxa
  have hxpi : x ≤ Real.pi := le_trans hxp (sub_le_self _ ha0)
  by_cases hxhalf : x ≤ Real.pi / 2
  · have hcos_nonneg : 0 ≤ Real.cos x := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · nlinarith [Real.pi_pos, hx0]
      · exact hxhalf
    rw [abs_of_nonneg hcos_nonneg]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 hxpi hxa
  · have hxhalf' : Real.pi / 2 ≤ x := by linarith
    have hcos_nonpos : Real.cos x ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · exact hxhalf'
      · nlinarith [Real.pi_pos, hxpi]
    rw [abs_of_nonpos hcos_nonpos, ← Real.cos_pi_sub]
    have hpi_sub_le_pi : Real.pi - x ≤ Real.pi := sub_le_self _ hx0
    have ha_le_pi_sub_x : a ≤ Real.pi - x := by linarith
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 hpi_sub_le_pi ha_le_pi_sub_x

theorem complex_exp_trace_norm_eq_two_abs_cos (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹‖ = 2 * |Real.cos θ| := by
  let z : ℂ := (Real.cos θ : ℂ) + Real.sin θ * Complex.I
  have hexp : Complex.exp (θ * Complex.I) = z := by
    simp [z, Complex.exp_mul_I]
  have hinv : (Complex.exp (θ * Complex.I))⁻¹ = Complex.exp (-θ * Complex.I) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← Complex.exp_add]
    simp
  have hnegexp : Complex.exp (-θ * Complex.I) = (Real.cos θ : ℂ) - Real.sin θ * Complex.I := by
    simpa [sub_eq_add_neg] using (Complex.exp_mul_I (-θ))
  have hsum : z + Complex.exp (-θ * Complex.I) = ((2 * Real.cos θ : ℝ) : ℂ) := by
    rw [hnegexp]
    apply Complex.ext <;> simp [z, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
  calc
    ‖Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹‖
        = ‖z + Complex.exp (-θ * Complex.I)‖ := by rw [hinv, hexp]
    _ = ‖((2 * Real.cos θ : ℝ) : ℂ)‖ := by rw [hsum]
    _ = 2 * |Real.cos θ| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num)]

theorem complex_norm_eq_one_of_real_quadratic_root {a : ℝ} {z : ℂ} (ha : |a| ≤ 2)
    (hz : z ^ 2 - (a : ℂ) * z + 1 = 0) :
    ‖z‖ = 1 := by
  have hconj : (star z) ^ 2 - (a : ℂ) * star z + 1 = 0 := by
    have h := congrArg star hz
    simpa using h
  have hz1 : z ^ 2 - (a : ℂ) * z = (-1 : ℂ) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  have hconj1 : (star z) ^ 2 - (a : ℂ) * star z = (-1 : ℂ) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconj
  have hfactor : (z - star z) * (z + star z - (a : ℂ)) = 0 := by
    calc
      (z - star z) * (z + star z - (a : ℂ))
          = (z ^ 2 - (a : ℂ) * z) - ((star z) ^ 2 - (a : ℂ) * star z) := by ring
      _ = (-1 : ℂ) - (-1 : ℂ) := by rw [hz1, hconj1]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfactor with hreal | hsum
  · have hzreal : z = star z := sub_eq_zero.mp hreal
    have him0 : z.im = 0 := by
      have h : z.im = -z.im := by
        simpa using congrArg Complex.im hzreal
      linarith
    have hre : z.re ^ 2 - a * z.re + 1 = 0 := by
      have h := congrArg Complex.re hz
      have h' : z.re * z.re + (-(a * z.re) + 1) = 0 := by
        simpa [pow_two, Complex.mul_re, him0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using h
      nlinarith
    have hdisc : a ^ 2 ≤ 4 := by
      have h := abs_le.mp ha
      nlinarith
    have hx2 : z.re ^ 2 = 1 := by
      nlinarith [hre, hdisc, sq_nonneg (2 * z.re - a)]
    have hsq : ‖z‖ ^ 2 = 1 := by
      calc
        ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
          simpa using (RCLike.norm_sq_eq_def (z := z))
        _ = z.re ^ 2 := by simp [him0, pow_two]
        _ = 1 := hx2
    have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  · have hsum' : z + star z = (a : ℂ) := sub_eq_zero.mp hsum
    have hzstar : star z = (a : ℂ) - z := by
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsum')
    have hprod : z * star z = 1 := by
      calc
        z * star z = z * ((a : ℂ) - z) := by rw [hzstar]
        _ = (a : ℂ) * z - z ^ 2 := by ring
        _ = 1 := by
          apply eq_of_sub_eq_zero
          calc
            ((a : ℂ) * z - z ^ 2) - 1 = -((z ^ 2 - (a : ℂ) * z) + 1) := by ring
            _ = 0 := by rw [hz1]; ring
    have hnormSqC : ((Complex.normSq z : ℝ) : ℂ) = 1 := by
      calc
        ((Complex.normSq z : ℝ) : ℂ) = z * star z := by
          symm
          simpa using (Complex.mul_conj z)
        _ = 1 := hprod
    have hnormSq : Complex.normSq z = 1 := by
      exact_mod_cast hnormSqC
    have hsq : ‖z‖ ^ 2 = 1 := by
      calc
        ‖z‖ ^ 2 = Complex.normSq z := by
          symm
          exact RCLike.normSq_eq_def' z
        _ = 1 := hnormSq
    have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith

theorem even_index_abs_cos_le (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hkm : k ≤ m - 1) :
    |Real.cos (Real.pi * k / m)| ≤ Real.cos (Real.pi / m) := by
  have hm0_nat : 0 < m := lt_trans Nat.zero_lt_one hm
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast hm0_nat
  have hm2_nat : 2 ≤ m := Nat.succ_le_of_lt hm
  have hm2 : (2 : ℝ) ≤ m := by
    exact_mod_cast hm2_nat
  have ha0 : 0 ≤ Real.pi / m := by
    exact div_nonneg (le_of_lt Real.pi_pos) hm0.le
  have ha2 : Real.pi / m ≤ Real.pi / 2 := by
    exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num) hm2
  have hk1R : (1 : ℝ) ≤ k := by
    exact_mod_cast hk1
  have hxa : Real.pi / m ≤ Real.pi * k / m := by
    have hmul : Real.pi * 1 ≤ Real.pi * k := by
      exact mul_le_mul_of_nonneg_left hk1R (le_of_lt Real.pi_pos)
    have hdiv : Real.pi * 1 / m ≤ Real.pi * k / m := by
      exact div_le_div_of_nonneg_right hmul hm0.le
    simpa only [mul_one] using hdiv
  have hkR : (k : ℝ) ≤ (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hkm
  have hupper_aux : Real.pi * k / m ≤ Real.pi * (((m - 1 : ℕ) : ℝ)) / m := by
    have hmul : Real.pi * k ≤ Real.pi * (((m - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hkR (le_of_lt Real.pi_pos)
    exact div_le_div_of_nonneg_right hmul hm0.le
  have hrewrite : Real.pi * (((m - 1 : ℕ) : ℝ)) / m = Real.pi - Real.pi / m := by
    rw [Nat.cast_sub (show 1 ≤ m by exact le_of_lt hm)]
    field_simp [hm0.ne']
    ring
  have hxp : Real.pi * k / m ≤ Real.pi - Real.pi / m := by
    calc
      Real.pi * k / m ≤ Real.pi * (((m - 1 : ℕ) : ℝ)) / m := hupper_aux
      _ = Real.pi - Real.pi / m := hrewrite
  simpa using abs_cos_le_cos_of_mem_Icc_pi_sub ha0 ha2 hxa hxp

theorem house_algebraMap_eq_house {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L] (β : K) :
    house (algebraMap K L β) = house β := by
  rw [NumberField.house_eq_sup' (algebraMap K L β), NumberField.house_eq_sup' β]
  exact_mod_cast (show
    Finset.univ.sup' Finset.univ_nonempty (fun ψ : L →+* ℂ => ‖ψ (algebraMap K L β)‖₊) =
      Finset.univ.sup' Finset.univ_nonempty (fun φ : K →+* ℂ => ‖φ β‖₊) from by
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro ψ hψ
      simpa using
        (Finset.le_sup' (s := Finset.univ) (f := fun φ : K →+* ℂ => ‖φ β‖₊)
          (Finset.mem_univ (ψ.comp (algebraMap K L))))
    · rw [Finset.sup'_le_iff]
      intro φ hφ
      simpa [NumberField.ComplexEmbedding.lift_algebraMap_apply] using
        (Finset.le_sup' (s := Finset.univ)
          (f := fun ψ : L →+* ℂ => ‖ψ (algebraMap K L β)‖₊)
          (Finset.mem_univ (NumberField.ComplexEmbedding.lift L φ))))

theorem house_le_two_exists_root_of_unity_in_splitting_field {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K)
    (hβ : house β ≤ 2) :
    let L := Polynomial.SplittingField (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1)
    ∃ z : L, algebraMap K L β = z + z⁻¹ ∧ ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  dsimp
  let f : Polynomial K := Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1
  let L := Polynomial.SplittingField f
  letI : NumberField L := NumberField.of_module_finite K L
  have hf_map_monicDeg : (f.map (algebraMap K L)).IsMonicOfDegree 2 := by
    simpa [f] using Polynomial.isMonicOfDegree_sub_add_two ((algebraMap K L) β) (1 : L)
  have hf_map_ne_zero : f.map (algebraMap K L) ≠ 0 := hf_map_monicDeg.ne_zero
  have hf_deg_ne_zero : (f.map (algebraMap K L)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf_map_ne_zero, hf_map_monicDeg.natDegree_eq]
    norm_num
  let z : L := Polynomial.rootOfSplits (Polynomial.SplittingField.splits (f := f)) hf_deg_ne_zero
  have hz : z ^ 2 - algebraMap K L β * z + 1 = 0 := by
    simpa [f, z] using Polynomial.eval_rootOfSplits (hf := Polynomial.SplittingField.splits (f := f)) hf_deg_ne_zero
  have hβL_int : IsIntegral ℤ (algebraMap K L β) := hβ_int.algebraMap
  let s : L := algebraMap K L β - z
  have hs_mul : s * z = 1 := by
    have hz2 : z * z + 1 = algebraMap K L β * z := by
      apply eq_of_sub_eq_zero
      calc
        (z * z + 1) - algebraMap K L β * z = z ^ 2 - algebraMap K L β * z + 1 := by
          rw [pow_two]
          ring
        _ = 0 := hz
    dsimp [s]
    calc
      (algebraMap K L β - z) * z = algebraMap K L β * z - z * z := by ring
      _ = (z * z + 1) - z * z := by rw [hz2]
      _ = 1 := by ring
  have hs_mem : s ∈ Algebra.adjoin ℤ ({s} : Set L) := by
    exact Algebra.subset_adjoin (by simp)
  have hs_int : IsIntegral (Algebra.adjoin ℤ ({s} : Set L)) s := by
    simpa using (isIntegral_algebraMap (R := Algebra.adjoin ℤ ({s} : Set L)) (A := L)
      (x := ⟨s, hs_mem⟩))
  have hβ_int_adjoin : IsIntegral (Algebra.adjoin ℤ ({s} : Set L)) (algebraMap K L β) := by
    exact hβL_int.tower_top
  have hz_int_adjoin : IsIntegral (Algebra.adjoin ℤ ({s} : Set L)) z := by
    rw [show z = algebraMap K L β - s by
      dsimp [s]
      ring]
    exact hβ_int_adjoin.sub hs_int
  have hz_int : IsIntegral ℤ z := by
    exact isIntegral_of_isIntegral_adjoin_of_mul_eq_one z s hs_mul hz_int_adjoin
  have hz_norm : ∀ ψ : L →+* ℂ, ‖ψ z‖ = 1 := by
    intro ψ
    have hβ_realψ : star ((ψ.comp (algebraMap K L)) β) = (ψ.comp (algebraMap K L)) β := by
      exact (NumberField.mem_maximalRealSubfield_iff β).1 hβ_real (ψ.comp (algebraMap K L))
    have hβ_eq : ((Complex.re (ψ (algebraMap K L β))) : ℂ) = ψ (algebraMap K L β) := by
      exact (Complex.conj_eq_iff_re).1 (by simpa using hβ_realψ)
    have ha : |Complex.re (ψ (algebraMap K L β))| ≤ 2 := by
      have hnorm : ‖ψ (algebraMap K L β)‖ ≤ 2 := by
        calc
          ‖(ψ.comp (algebraMap K L)) β‖ ≤ house β := NumberField.norm_embedding_le_house β
            (ψ.comp (algebraMap K L))
          _ ≤ 2 := hβ
      rw [← hβ_eq] at hnorm
      simpa using hnorm
    have hzψ0 : ψ z ^ 2 - ψ (algebraMap K L β) * ψ z + 1 = 0 := by
      simpa [map_sub, map_add, map_mul, map_pow] using congrArg ψ hz
    have hzψ : ψ z ^ 2 - (Complex.re (ψ (algebraMap K L β)) : ℂ) * ψ z + 1 = 0 := by
      simpa [hβ_eq] using hzψ0
    exact complex_norm_eq_one_of_real_quadratic_root ha hzψ
  rcases NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := L) (A := ℂ) hz_int hz_norm with
    ⟨m, hmpos, hzm⟩
  have hz_ne_zero : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_pow hmpos.ne'] at hzm
    exact zero_ne_one hzm
  have hs_eq : s = z⁻¹ := by
    exact (mul_eq_one_iff_eq_inv₀ hz_ne_zero).1 hs_mul
  have hβ_eq_final : algebraMap K L β = z + z⁻¹ := by
    calc
      algebraMap K L β = z + s := by
        dsimp [s]
        ring
      _ = z + z⁻¹ := by rw [hs_eq]
  exact ⟨z, hβ_eq_final, m, hmpos, hzm⟩

theorem odd_index_abs_cos_le (m k : ℕ) (hm : 0 < m) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    |Real.cos (2 * Real.pi * k / (2 * m + 1))| ≤
      Real.cos (Real.pi / (2 * m + 1)) := by
  have hpi_nonneg : 0 ≤ Real.pi := by positivity
  have hNpos_nat : 0 < 2 * m + 1 := by omega
  have hNpos : (0 : ℝ) < 2 * m + 1 := by exact_mod_cast hNpos_nat
  have ha0 : 0 ≤ Real.pi / (2 * m + 1) := by positivity
  have hNge2_nat : 2 ≤ 2 * m + 1 := by omega
  have hNge2 : (2 : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hNge2_nat
  have ha2 : Real.pi / (2 * m + 1) ≤ Real.pi / 2 := by
    exact div_le_div_of_nonneg_left hpi_nonneg (by norm_num) hNge2
  have hxa : Real.pi / (2 * m + 1) ≤ 2 * Real.pi * k / (2 * m + 1) := by
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hmult : Real.pi ≤ 2 * Real.pi * k := by
      nlinarith [hpi_nonneg]
    have hmult' : (Real.pi / (2 * m + 1)) * (2 * m + 1) ≤ 2 * Real.pi * k := by
      calc
        (Real.pi / (2 * m + 1)) * (2 * m + 1) = Real.pi := by
          field_simp [hNpos.ne']
        _ ≤ 2 * Real.pi * k := hmult
    exact (le_div_iff₀ hNpos).2 hmult'
  have hm_id : 2 * Real.pi * m / (2 * m + 1) = Real.pi - Real.pi / (2 * m + 1) := by
    field_simp [hNpos.ne']
    ring_nf
  have hx_le_mid : 2 * Real.pi * k / (2 * m + 1) ≤ 2 * Real.pi * m / (2 * m + 1) := by
    have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
    have hcoef_nonneg : 0 ≤ 2 * Real.pi := by positivity
    have hmul : 2 * Real.pi * k ≤ 2 * Real.pi * m := by
      nlinarith
    exact div_le_div_of_nonneg_right hmul (le_of_lt hNpos)
  have hxp : 2 * Real.pi * k / (2 * m + 1) ≤ Real.pi - Real.pi / (2 * m + 1) := by
    calc
      2 * Real.pi * k / (2 * m + 1) ≤ 2 * Real.pi * m / (2 * m + 1) := hx_le_mid
      _ = Real.pi - Real.pi / (2 * m + 1) := hm_id
  exact abs_cos_le_cos_of_mem_Icc_pi_sub ha0 ha2 hxa hxp

noncomputable def primitiveRootsTraceSup (n : ℕ) [NeZero n] : ℝ :=
  ↑((primitiveRoots n ℂ).sup'
      (Finset.card_pos.mp <| by
        rw [Complex.card_primitiveRoots, Nat.totient_pos]
        exact NeZero.pos n)
      (fun ζ => ‖ζ + ζ⁻¹‖₊))

theorem house_trace_of_primitive_root_eq_primitiveRootsTraceSup {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] {ζ : L} {n : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) :
    house (ζ + ζ⁻¹) = primitiveRootsTraceSup n := by
  classical
  let F := IntermediateField.adjoin ℚ ({ζ} : Set L)
  letI : Algebra ℚ F := IntermediateField.algebra' F
  letI : NumberField F := NumberField.of_intermediateField (K := ℚ) (L := L) F
  letI : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ ↥(IntermediateField.adjoin ℚ ({ζ} : Set L))
    exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let ζF : F := ⟨ζ, (IntermediateField.subset_adjoin ℚ ({ζ} : Set L)) (by simp)⟩
  have hζF : IsPrimitiveRoot ζF n := by
    exact (IsPrimitiveRoot.coe_submonoidClass_iff).mp hζ
  have hhouse : house (ζ + ζ⁻¹) = house (ζF + ζF⁻¹) := by
    simpa [ζF, map_add, map_inv] using
      (house_algebraMap_eq_house (K := F) (L := L) (β := ζF + ζF⁻¹))
  rw [hhouse]
  rw [NumberField.house_eq_sup']
  rw [primitiveRootsTraceSup]
  norm_cast
  have hprim : (primitiveRoots n ℂ).Nonempty := by
    exact Finset.card_pos.mp <| by
      rw [Complex.card_primitiveRoots, Nat.totient_pos]
      exact NeZero.pos n
  letI : Nonempty (primitiveRoots n ℂ) := by
    rcases hprim with ⟨ξ, hξ⟩
    exact ⟨⟨ξ, hξ⟩⟩
  let e : (F →+* ℂ) ≃ primitiveRoots n ℂ :=
    RingHom.equivRatAlgHom.trans
      (hζF.embeddingsEquivPrimitiveRoots ℂ
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)))
  have he (φ : F →+* ℂ) : ((e φ : primitiveRoots n ℂ) : ℂ) = φ ζF := by
    simp [e]
  have hsup₁ :
      Finset.univ.sup' Finset.univ_nonempty (fun φ : F →+* ℂ => ‖φ (ζF + ζF⁻¹)‖₊)
        = Finset.univ.sup' Finset.univ_nonempty
            (fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊) := by
    calc
      Finset.univ.sup' Finset.univ_nonempty (fun φ : F →+* ℂ => ‖φ (ζF + ζF⁻¹)‖₊)
          = Finset.univ.sup' Finset.univ_nonempty
              ((fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊) ∘ e) := by
                refine Finset.sup'_congr (H := Finset.univ_nonempty) rfl ?_
                intro φ hφ
                simp [he, map_add, map_inv]
      _ = (Finset.univ.map e.toEmbedding).sup'
            (Finset.map_nonempty.2 Finset.univ_nonempty)
            (fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊) := by
              exact Finset.sup'_comp_eq_map
                (s := Finset.univ)
                (f := e.toEmbedding)
                (g := fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊)
                Finset.univ_nonempty
      _ = Finset.univ.sup' Finset.univ_nonempty
            (fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊) := by
              simpa [Finset.univ_map_equiv_to_embedding e]
  have hs : (primitiveRoots n ℂ).attach.Nonempty := by
    simpa [Finset.attach_nonempty_iff] using hprim
  have hsup₂ :
      Finset.univ.sup' Finset.univ_nonempty
          (fun ξ : primitiveRoots n ℂ => ‖(ξ : ℂ) + ((ξ : ℂ)⁻¹)‖₊)
        = (primitiveRoots n ℂ).sup' hprim (fun ξ : ℂ => ‖ξ + ξ⁻¹‖₊) := by
    simpa [Finset.univ_eq_attach, Finset.attach_map_val] using
      (Finset.sup'_comp_eq_map
        (s := (primitiveRoots n ℂ).attach)
        (f := Function.Embedding.subtype _)
        (g := fun ξ : ℂ => ‖ξ + ξ⁻¹‖₊)
        hs)
  exact hsup₁.trans hsup₂

theorem primitiveRootsTraceSup_eq_of_mem_eq_and_bound (n : ℕ) [NeZero n] {ζ : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (hζ : ζ ∈ primitiveRoots n ℂ)
    (hval : ‖ζ + ζ⁻¹‖ = a)
    (hbound : ∀ ξ ∈ primitiveRoots n ℂ, ‖ξ + ξ⁻¹‖ ≤ a) :
    primitiveRootsTraceSup n = a := by
  classical
  have H : (primitiveRoots n ℂ).Nonempty := by
    apply Finset.card_pos.mp
    rw [Complex.card_primitiveRoots, Nat.totient_pos]
    exact NeZero.pos n
  let aNN : NNReal := ⟨a, ha⟩
  apply le_antisymm
  · unfold primitiveRootsTraceSup
    change ↑((primitiveRoots n ℂ).sup' H (fun ζ => ‖ζ + ζ⁻¹‖₊)) ≤ ↑aNN
    exact_mod_cast ((Finset.sup'_le_iff (H := H) (f := fun ξ => ‖ξ + ξ⁻¹‖₊)).2 fun ξ hξ => by
      exact_mod_cast hbound ξ hξ)
  · rw [← hval]
    unfold primitiveRootsTraceSup
    change ↑(‖ζ + ζ⁻¹‖₊) ≤ ↑((primitiveRoots n ℂ).sup' H (fun ξ => ‖ξ + ξ⁻¹‖₊))
    exact_mod_cast (Finset.le_sup' (s := primitiveRoots n ℂ) (f := fun ξ => ‖ξ + ξ⁻¹‖₊) hζ)

theorem primitive_root_trace_norm_eq_two_abs_cos_of_mem (n : ℕ) [NeZero n] {ζ : ℂ} (hζ : ζ ∈ primitiveRoots n ℂ) :
    ∃ i < n, i.Coprime n ∧ ‖ζ + ζ⁻¹‖ = 2 * |Real.cos (2 * Real.pi * i / n)| := by
  classical
  have hprim : IsPrimitiveRoot ζ n := isPrimitiveRoot_of_mem_primitiveRoots hζ
  rcases (Complex.isPrimitiveRoot_iff ζ n (Nat.ne_of_gt (NeZero.pos n))).1 hprim with
    ⟨i, hi_lt, hi_cop, hi_eq⟩
  refine ⟨i, hi_lt, hi_cop, ?_⟩
  rw [← hi_eq]
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    complex_exp_trace_norm_eq_two_abs_cos (2 * Real.pi * i / n)

theorem primitiveRootsTraceSup_eq_cos_of_even (n : ℕ) [NeZero n] (hn : 2 < n) (heven : Even n) :
    primitiveRootsTraceSup n = 2 * Real.cos (Real.pi / (n / 2)) := by
  rcases heven with ⟨m, rfl⟩
  have hm : 1 < m := by omega
  have hmpos : 0 < m := by omega
  have hmne : m ≠ 0 := by omega
  have hhalfR : (((m + m : ℕ) : ℝ) / 2) = (m : ℝ) := by
    have htwoR : (((m + m : ℕ) : ℝ)) = 2 * (m : ℝ) := by
      exact_mod_cast (show m + m = 2 * m by omega)
    rw [htwoR]
    ring_nf
  rw [hhalfR]
  let ω : ℂ := Complex.exp ((2 * Real.pi / ((m + m : ℕ) : ℝ)) * Complex.I)
  have hωeq : ω = Complex.exp (2 * Real.pi * Complex.I / ((m + m : ℕ) : ℝ)) := by
    dsimp [ω]
    have hnmz : (((m + m : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hnmz]
  have hωprim : IsPrimitiveRoot ω (m + m) := by
    rw [hωeq]
    simpa using Complex.isPrimitiveRoot_exp (m + m) (by omega)
  have hωmem : ω ∈ primitiveRoots (m + m) ℂ := by
    exact (mem_primitiveRoots (by omega : 0 < m + m)).2 hωprim
  have hθbase (k : ℕ) : 2 * Real.pi * (k : ℝ) / ((m + m : ℕ) : ℝ) = Real.pi * (k : ℝ) / (m : ℝ) := by
    have htwoR : (((m + m : ℕ) : ℝ)) = 2 * (m : ℝ) := by
      exact_mod_cast (show m + m = 2 * m by omega)
    rw [htwoR]
    field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmne]
  have hθ : 2 * Real.pi / ((m + m : ℕ) : ℝ) = Real.pi / (m : ℝ) := by
    simpa using hθbase 1
  have hcos_nonneg : 0 ≤ Real.cos (Real.pi / (m : ℝ)) := by
    have hpi_div_nonneg : 0 ≤ Real.pi / (m : ℝ) := by positivity
    have hpi_div_le : Real.pi / (m : ℝ) ≤ Real.pi / 2 := by
      have hmge : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      exact div_le_div_of_nonneg_left Real.pi_nonneg (by positivity : (0 : ℝ) < 2) hmge
    have hneg : -(Real.pi / 2) ≤ Real.pi / (m : ℝ) := by nlinarith
    exact Real.cos_nonneg_of_mem_Icc ⟨hneg, hpi_div_le⟩
  have ha : 0 ≤ 2 * Real.cos (Real.pi / (m : ℝ)) := by
    nlinarith
  refine primitiveRootsTraceSup_eq_of_mem_eq_and_bound (n := m + m)
    (a := 2 * Real.cos (Real.pi / (m : ℝ))) ha hωmem ?_ ?_
  · have hωval : ‖ω + ω⁻¹‖ = 2 * |Real.cos (2 * Real.pi / ((m + m : ℕ) : ℝ))| := by
      simpa [ω] using complex_exp_trace_norm_eq_two_abs_cos (2 * Real.pi / ((m + m : ℕ) : ℝ))
    rw [hωval, hθ, abs_of_nonneg hcos_nonneg]
  · intro ζ hζ
    obtain ⟨i, hi_lt, hicop, hi_eval⟩ := primitive_root_trace_norm_eq_two_abs_cos_of_mem (n := m + m) hζ
    have hi2 : i.Coprime 2 := Nat.Coprime.of_dvd_right (by omega) hicop
    have hiodd : Odd i := (Nat.coprime_two_right).1 hi2
    have hi_pos : 0 < i := hiodd.pos
    have hi_one : 1 ≤ i := by omega
    by_cases him : i ≤ m
    · have him_ne : i ≠ m := by
        intro hieq
        have hcopm : m.Coprime (m + m) := by
          simpa [hieq] using hicop
        have hm_dvd : m ∣ 1 * (m + m) := by
          refine ⟨2, by omega⟩
        have hm_dvd_one : m ∣ 1 := (Nat.Coprime.dvd_mul_right hcopm).1 hm_dvd
        have hm_le_one : m ≤ 1 := Nat.le_of_dvd (by norm_num) hm_dvd_one
        omega
      have hi_top : i ≤ m - 1 := by omega
      have hboundcos : |Real.cos (Real.pi * (i : ℝ) / (m : ℝ))| ≤ Real.cos (Real.pi / (m : ℝ)) :=
        even_index_abs_cos_le m i hm hi_one hi_top
      have hbound2 : 2 * |Real.cos (Real.pi * (i : ℝ) / (m : ℝ))| ≤ 2 * Real.cos (Real.pi / (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hboundcos (by positivity : (0 : ℝ) ≤ 2)
      rw [hi_eval, hθbase i]
      exact hbound2
    · let j : ℕ := (m + m) - i
      have hj1 : 1 ≤ j := by
        dsimp [j]
        omega
      have hjtop : j ≤ m - 1 := by
        dsimp [j]
        omega
      have hboundcos : |Real.cos (Real.pi * (j : ℝ) / (m : ℝ))| ≤ Real.cos (Real.pi / (m : ℝ)) :=
        even_index_abs_cos_le m j hm hj1 hjtop
      have hbound2 : 2 * |Real.cos (Real.pi * (j : ℝ) / (m : ℝ))| ≤ 2 * Real.cos (Real.pi / (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hboundcos (by positivity : (0 : ℝ) ≤ 2)
      have hij_sum : i + j = m + m := by
        dsimp [j]
        omega
      have hijRsum : (i : ℝ) + (j : ℝ) = 2 * (m : ℝ) := by
        have htmp : (i : ℝ) + (j : ℝ) = (((m + m : ℕ) : ℝ)) := by
          exact_mod_cast hij_sum
        have htwoR : (((m + m : ℕ) : ℝ)) = 2 * (m : ℝ) := by
          exact_mod_cast (show m + m = 2 * m by omega)
        linarith
      have hijR : (i : ℝ) = 2 * (m : ℝ) - (j : ℝ) := by
        nlinarith
      have hθj : 2 * Real.pi * (i : ℝ) / ((m + m : ℕ) : ℝ) = 2 * Real.pi - Real.pi * (j : ℝ) / (m : ℝ) := by
        calc
          2 * Real.pi * (i : ℝ) / ((m + m : ℕ) : ℝ) = Real.pi * (i : ℝ) / (m : ℝ) := hθbase i
          _ = Real.pi * (2 * (m : ℝ) - (j : ℝ)) / (m : ℝ) := by rw [hijR]
          _ = 2 * Real.pi - Real.pi * (j : ℝ) / (m : ℝ) := by
            field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmne]
      rw [hi_eval, hθj, Real.cos_two_pi_sub]
      exact hbound2

theorem primitiveRootsTraceSup_eq_cos_of_odd (n : ℕ) [NeZero n] (hn : 1 < n) (hodd : Odd n) :
    primitiveRootsTraceSup n = 2 * Real.cos (Real.pi / n) := by
  rcases hodd with ⟨m, rfl⟩
  have hm : 0 < m := by omega
  have hNpos : 0 < 2 * m + 1 := by omega
  have hNne : (2 * m + 1) ≠ 0 := by omega
  have hNposR : (0 : ℝ) < (2 * m + 1 : ℕ) := by
    exact_mod_cast hNpos
  have htwo_le : (2 : ℝ) ≤ (2 * m + 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ 2 * m + 1 by omega)
  have hpi_div_nonneg : 0 ≤ Real.pi / (2 * m + 1 : ℕ) := by
    exact div_nonneg Real.pi_pos.le hNposR.le
  have hpi_div_le_half : Real.pi / (2 * m + 1 : ℕ) ≤ Real.pi / 2 := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity : (0 : ℝ) < 2) htwo_le
  have hcos_nonneg : 0 ≤ Real.cos (Real.pi / (2 * m + 1 : ℕ)) := by
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hpi_div_nonneg]) hpi_div_le_half
  have ha : 0 ≤ 2 * Real.cos (Real.pi / (2 * m + 1 : ℕ)) := by
    positivity
  let θ : ℝ := 2 * Real.pi * (m / (2 * m + 1 : ℕ))
  let ξ : ℂ := Complex.exp (θ * Complex.I)
  have hm_cop : m.Coprime (2 * m + 1) := by
    have hm1 : m.Coprime 1 := by
      simpa using (Nat.coprime_one_right_iff m).2 trivial
    simpa [two_mul, add_assoc, add_comm, add_left_comm] using
      (Nat.coprime_mul_right_add_right m 1 2).2 hm1
  have hξprim : IsPrimitiveRoot ξ (2 * m + 1) := by
    dsimp [ξ, θ]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.isPrimitiveRoot_exp_of_coprime m (2 * m + 1) hNne hm_cop)
  have hξmem : ξ ∈ primitiveRoots (2 * m + 1) ℂ := by
    exact (mem_primitiveRoots hNpos).2 hξprim
  have hcast : (2 * (m : ℝ) + 1) = ((2 * m + 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hmid : θ = Real.pi - Real.pi / (2 * m + 1 : ℕ) := by
    dsimp [θ]
    field_simp [hNposR.ne']
    nlinarith
  refine primitiveRootsTraceSup_eq_of_mem_eq_and_bound (n := 2 * m + 1)
    (a := 2 * Real.cos (Real.pi / (2 * m + 1 : ℕ))) ha hξmem ?_ ?_
  · dsimp [ξ]
    rw [complex_exp_trace_norm_eq_two_abs_cos, hmid, Real.cos_pi_sub, abs_neg, abs_of_nonneg hcos_nonneg]
  · intro ζ hζ
    rcases primitive_root_trace_norm_eq_two_abs_cos_of_mem (n := 2 * m + 1) hζ with ⟨i, hi_lt, hi_cop, hi_eval⟩
    have hi0 : 0 < i := by
      by_contra hi0
      have hi_eq : i = 0 := by omega
      subst hi_eq
      have hN1 : 2 * m + 1 = 1 := by
        simpa using hi_cop.symm
      omega
    have hi1 : 1 ≤ i := by omega
    by_cases hle : i ≤ m
    · have hcos_le : |Real.cos (2 * Real.pi * i / (2 * m + 1 : ℕ))| ≤
          Real.cos (Real.pi / (2 * m + 1 : ℕ)) := by
        simpa only [hcast] using odd_index_abs_cos_le m i hm hi1 hle
      linarith [hi_eval, hcos_le]
    · let j : ℕ := 2 * m + 1 - i
      have hj1 : 1 ≤ j := by
        omega
      have hjm : j ≤ m := by
        omega
      have hji : i + j = 2 * m + 1 := by
        dsimp [j]
        omega
      have hjiR : (i : ℝ) + (j : ℝ) = (2 * m + 1 : ℕ) := by
        exact_mod_cast hji
      have hangle : 2 * Real.pi * i / (2 * m + 1 : ℕ) =
          2 * Real.pi - 2 * Real.pi * j / (2 * m + 1 : ℕ) := by
        field_simp [hNposR.ne']
        nlinarith [hjiR]
      have hcos_eq : |Real.cos (2 * Real.pi * i / (2 * m + 1 : ℕ))| =
          |Real.cos (2 * Real.pi * j / (2 * m + 1 : ℕ))| := by
        rw [hangle, Real.cos_two_pi_sub]
      have hcos_le_j : |Real.cos (2 * Real.pi * j / (2 * m + 1 : ℕ))| ≤
          Real.cos (Real.pi / (2 * m + 1 : ℕ)) := by
        simpa only [hcast] using odd_index_abs_cos_le m j hm hj1 hjm
      have hcos_le : |Real.cos (2 * Real.pi * i / (2 * m + 1 : ℕ))| ≤
          Real.cos (Real.pi / (2 * m + 1 : ℕ)) := by
        rw [hcos_eq]
        exact hcos_le_j
      linarith [hi_eval, hcos_le]

theorem primitiveRootsTraceSup_eq_two_or_cos (n : ℕ) [NeZero n] :
    primitiveRootsTraceSup n = 2 ∨
      ∃ m : ℕ, 0 < m ∧ primitiveRootsTraceSup n = 2 * Real.cos (Real.pi / m) := by
  classical
  by_cases h1 : n = 1
  · left
    subst h1
    simp [primitiveRootsTraceSup]
    norm_num
  · by_cases h2 : n = 2
    · left
      subst h2
      have hcard : (primitiveRoots 2 ℂ).card = 1 := by
        simpa using Complex.card_primitiveRoots 2
      rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
      have hmem : (-1 : ℂ) ∈ primitiveRoots 2 ℂ := by
        rw [mem_primitiveRoots (R := ℂ) (show 0 < 2 by decide)]
        simpa using (IsPrimitiveRoot.neg_one (R := ℂ) 0 (by decide))
      have ha' : a = -1 := by
        rw [ha] at hmem
        have : (-1 : ℂ) = a := by simpa using hmem
        exact this.symm
      subst ha'
      simp [primitiveRootsTraceSup, ha]
      norm_num
    · have hn0 : 0 < n := NeZero.pos n
      have hn2 : 2 < n := by omega
      have hn1 : 1 < n := by omega
      rcases Nat.even_or_odd n with heven | hodd
      · right
        refine ⟨n / 2, ?_, ?_⟩
        · omega
        · have hdiv : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
            exact Nat.cast_div (by simpa [even_iff_two_dvd] using heven) (by norm_num)
          rw [hdiv]
          simpa using primitiveRootsTraceSup_eq_cos_of_even (n := n) hn2 heven
      · right
        refine ⟨n, hn0, ?_⟩
        simpa using primitiveRootsTraceSup_eq_cos_of_odd (n := n) hn1 hodd

theorem house_trace_of_primitive_root_eq_two_or_cos {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] {ζ : L} {n : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) :
    house (ζ + ζ⁻¹) = 2 ∨
      ∃ m : ℕ, 0 < m ∧ house (ζ + ζ⁻¹) = 2 * Real.cos (Real.pi / m) := by
  simpa [house_trace_of_primitive_root_eq_primitiveRootsTraceSup hζ] using
    (primitiveRootsTraceSup_eq_two_or_cos (n := n))

theorem cyclotomic_integer_house_le_two {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    house β ≤ 2 →
      house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) := by
  intro hβ
  classical
  let L := Polynomial.SplittingField (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1)
  rcases house_le_two_exists_root_of_unity_in_splitting_field (K := K) (β := β) hβ_int hβ_real hβ with
    ⟨z, hzβ, m, hmpos, hzm⟩
  letI : NumberField L := NumberField.of_module_finite (K := K) (L := L)
  have hz_fin : IsOfFinOrder z :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨m, hmpos, hzm⟩
  letI : NeZero (orderOf z) := ⟨orderOf_ne_zero_iff.2 hz_fin⟩
  have hprim : IsPrimitiveRoot z (orderOf z) := IsPrimitiveRoot.orderOf z
  have hclass :=
    house_trace_of_primitive_root_eq_two_or_cos (L := L) (ζ := z) (n := orderOf z) hprim
  have hhouse : house β = house (z + z⁻¹) := by
    calc
      house β = house (algebraMap K L β) := by
        symm
        exact house_algebraMap_eq_house (K := K) (L := L) β
      _ = house (z + z⁻¹) := by rw [hzβ]
  rcases hclass with htwo | ⟨k, hkpos, hk⟩
  · left
    rw [hhouse]
    exact htwo
  · right
    refine ⟨k, hkpos, ?_⟩
    rw [hhouse]
    exact hk


end Submission
