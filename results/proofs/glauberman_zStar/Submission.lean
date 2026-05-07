import Mathlib
import Submission.Helpers

namespace Submission

theorem glauberman_fixed_coset_unique (G : Type) [Group G] [Fintype G] (t : G)
    (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∀ q : G ⧸ Subgroup.centralizer ({t} : Set G),
      t • q = q → q = QuotientGroup.mk 1 := by
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have htinv : t⁻¹ = t := by
    exact inv_eq_of_mul_eq_one_left ht2
  intro q hq
  rcases Quotient.exists_rep q with ⟨g, rfl⟩
  change QuotientGroup.mk (t * g) = QuotientGroup.mk g at hq
  have hgC : g⁻¹ * t * g ∈ C := by
    have hq' : ((t * g : G) : G ⧸ C) = g := by simpa [C] using hq
    have hgC0 : (t * g)⁻¹ * g ∈ C := (QuotientGroup.eq).1 hq'
    simpa [htinv, mul_assoc] using hgC0
  have hcomm : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hconj : g⁻¹ * t * g = t := by
    have hconj0 : g⁻¹ * t * (g⁻¹)⁻¹ = t :=
      hisolated (g⁻¹) (by simpa [inv_inv, htinv, mul_assoc] using hcomm)
    simpa [inv_inv] using hconj0
  have htg : t * g = g * t := by
    simpa [mul_assoc] using congrArg (fun x => g * x) hconj
  have hgt : g * t = t * g := by
    simpa [eq_comm] using htg
  have hgmem : g ∈ C := by
    change g ∈ Subgroup.centralizer ({t} : Set G)
    simpa [Subgroup.mem_centralizer_singleton_iff] using hgt
  have hmk : (g : G ⧸ C) = QuotientGroup.mk (1 : G) := by
    exact (QuotientGroup.eq).2 (by simpa [C] using C.inv_mem hgmem)
  simpa using hmk

theorem glauberman_centralizer_index_odd (G : Type) [Group G] [Fintype G] (t : G)
    (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    Odd ((Subgroup.centralizer ({t} : Set G)).index) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let q1 : G ⧸ C := QuotientGroup.mk 1
  let f : Function.End (G ⧸ C) := fun q => t • q
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htC : t ∈ C := by
    dsimp [C]
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hfixed_one : f q1 = q1 := by
    simpa [f, q1] using
      (QuotientGroup.mk_mul_of_mem (s := C) (a := (1 : G)) (b := t) htC)
  have hfixed_unique : ∀ q : G ⧸ C, f q = q → q = q1 := by
    intro q hq
    simpa [f, q1] using glauberman_fixed_coset_unique G t ht2 hisolated q (by simpa [f] using hq)
  have hcard_fixed : Fintype.card ↑(Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨q1, ?_⟩, ?_⟩
    · exact Function.mem_fixedPoints_iff.mpr hfixed_one
    · intro x
      apply Subtype.ext
      exact hfixed_unique x.1 (Function.mem_fixedPoints_iff.mp x.2)
  have hf2 : f ^ 2 = 1 := by
    funext q
    change t • (t • q) = q
    rw [← mul_smul, ht2, one_smul]
  have hmod : Fintype.card (G ⧸ C) ≡ Fintype.card ↑(Function.fixedPoints f) [MOD 2] := by
    simpa using (Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2)
  have hmod1 : Fintype.card (G ⧸ C) ≡ 1 [MOD 2] := by
    simpa [hcard_fixed] using hmod
  have hoddq : Odd (Fintype.card (G ⧸ C)) := by
    rw [Nat.odd_iff]
    exact Nat.mod_eq_of_modEq hmod1 (by decide)
  simpa [C, Subgroup.index_eq_card, Nat.card_eq_fintype_card] using hoddq

theorem glauberman_exists_sylow_two_containing_t (G : Type) [Group G] [Fintype G] (t : G)
    (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ P : Sylow 2 G, t ∈ (P : Subgroup G) ∧
      (P : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hCodd : Odd C.index := glauberman_centralizer_index_odd G t ht2 hisolated
  have htC : t ∈ C := by
    simpa using (Subgroup.mem_centralizer_singleton_iff.mpr (show t * t = t * t by rfl))
  let tc : C := ⟨t, htC⟩
  have htc_dvd_two : orderOf tc ∣ 2 := by
    rw [Subgroup.orderOf_mk t htC]
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ht2)
  have hzc_pg : IsPGroup 2 (Subgroup.zpowers tc) := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx_dvd_two : orderOf x ∣ 2 := by
      simpa using (dvd_trans (orderOf_dvd_of_mem_zpowers (x := tc) (y := (x : C)) x.property) htc_dvd_two)
    rcases (Nat.dvd_prime (show Nat.Prime 2 by decide)).1 hx_dvd_two with hx1 | hx2
    · exact ⟨0, by simpa [hx1]⟩
    · exact ⟨1, by simpa [hx2]⟩
  obtain ⟨Pc, hPc_le⟩ := IsPGroup.exists_le_sylow (G := C) (P := Subgroup.zpowers tc) hzc_pg
  have htcPc : tc ∈ (Pc : Subgroup C) := hPc_le (Subgroup.mem_zpowers tc)
  let H : Subgroup G := (Pc : Subgroup C).map C.subtype
  have hH_pg : IsPGroup 2 H := by
    simpa [H] using Pc.isPGroup'.map C.subtype
  have hH_index : H.index = (Pc : Subgroup C).index * C.index := by
    simpa [H] using (Subgroup.index_map_subtype (H := C) (K := (Pc : Subgroup C)))
  have hH_not_dvd : ¬ 2 ∣ H.index := by
    rw [hH_index]
    exact Nat.Prime.not_dvd_mul (show Nat.Prime 2 by decide) Pc.not_dvd_index (Odd.not_two_dvd_nat hCodd)
  refine ⟨hH_pg.toSylow hH_not_dvd, ?_, ?_⟩
  · have htH : t ∈ H := by
      change t ∈ (Pc : Subgroup C).map C.subtype
      exact ⟨tc, htcPc, rfl⟩
    simpa using (IsPGroup.mem_toSylow hH_pg hH_not_dvd).2 htH
  · have hH_le : H ≤ C := by
      simpa [H] using (Subgroup.map_subtype_le (K := (Pc : Subgroup C)))
    simpa using hH_le

theorem glauberman_isolated_of_weakly_closed_in_sylow (G : Type) [Group G] [Fintype G]
    (t : G) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hweak : ∀ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) → g * t * g⁻¹ = t) :
    ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
  intro g hxcomm
  let x := g * t * g⁻¹
  let S : Set G := ({x, t} : Set G)
  let K : Subgroup G := Subgroup.closure S
  have hxK : x ∈ K := by
    exact Subgroup.subset_closure (by simp [S])
  have htK : t ∈ K := by
    exact Subgroup.subset_closure (by simp [S])
  have hx2 : x * x = 1 := by
    dsimp [x]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * t * (g⁻¹ * g) * t * g⁻¹ := by simp [mul_assoc]
      _ = g * (t * t) * g⁻¹ := by simp [mul_assoc]
      _ = 1 := by simpa [ht2, mul_assoc]
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hxcomm, x, hx2, ht2]
  letI : CommGroup K := Subgroup.closureCommGroupOfComm hcommS
  letI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hKsq : ∀ y : K, y * y = 1 := by
    intro y
    have hygen : y ∈ Subgroup.closure (K.subtype ⁻¹' S) := by
      rw [Subgroup.closure_preimage_eq_top S]
      simp
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hygen
    · intro a ha
      apply Subtype.ext
      have ha' : (a : G) = x ∨ (a : G) = t := by
        simpa [S] using ha
      rcases ha' with hax | hat
      · simpa [hax] using hx2
      · simpa [hat] using ht2
    · simp
    · intro a b ha hb hha hhb
      calc
        (a * b) * (a * b) = (a * a) * (b * b) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
        _ = 1 := by rw [hha, hhb]; simp
    · intro a ha hha
      have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_left hha
      simpa [hia] using hha
  have hKp : IsPGroup 2 K := by
    rw [IsPGroup.iff_orderOf]
    intro y
    rw [exists_orderOf_eq_prime_pow_iff]
    refine ⟨1, ?_⟩
    simpa [pow_two] using hKsq y
  letI : MulAction.IsPretransitive G (Sylow 2 G) := Sylow.isPretransitive_of_finite
  obtain ⟨Q, hKQ⟩ := IsPGroup.exists_le_sylow hKp
  obtain ⟨a, haQ⟩ := MulAction.exists_smul_eq (M := G) P Q
  have hxQ : x ∈ (Q : Subgroup G) := hKQ hxK
  have htQ : t ∈ (Q : Subgroup G) := hKQ htK
  have hxt_in_P : a⁻¹ * x * a ∈ (P : Subgroup G) := by
    rw [← haQ] at hxQ
    simpa [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hxQ
  have htt_in_P : a⁻¹ * t * a ∈ (P : Subgroup G) := by
    rw [← haQ] at htQ
    simpa [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_apply, mul_assoc] using htQ
  have htt_in_P' : a⁻¹ * t * (a⁻¹)⁻¹ ∈ (P : Subgroup G) := by
    simpa using htt_in_P
  have hxt_in_P' : (a⁻¹ * g) * t * (a⁻¹ * g)⁻¹ ∈ (P : Subgroup G) := by
    simpa [x, mul_assoc, mul_inv_rev] using hxt_in_P
  have hta : a⁻¹ * t * a = t := by
    simpa using hweak a⁻¹ htt_in_P'
  have hxa : a⁻¹ * x * a = t := by
    simpa [x, mul_assoc, mul_inv_rev] using hweak (a⁻¹ * g) hxt_in_P'
  have ha_cent : a * t * a⁻¹ = t := by
    have h := congrArg (fun z => a * z * a⁻¹) hta
    simpa [mul_assoc] using h.symm
  have hxeq : x = a * t * a⁻¹ := by
    have h := congrArg (fun z => a * z * a⁻¹) hxa
    simpa [mul_assoc] using h
  calc
    x = a * t * a⁻¹ := hxeq
    _ = t := ha_cent

theorem glauberman_normalizer_le_centralizer_of_contains_t (G : Type) [Group G] (t : G)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t)
    (H : Subgroup G) (htH : t ∈ H) (hH : H ≤ Subgroup.centralizer ({t} : Set G)) :
    Subgroup.normalizer H ≤ Subgroup.centralizer ({t} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : g * t * g⁻¹ ∈ H := by
    exact (Subgroup.mem_normalizer_iff.mp hg) t |>.mp htH
  have hcomm : (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
    exact Subgroup.mem_centralizer_singleton_iff.mp (hH hconj)
  have hEq : g * t * g⁻¹ = t := hisolated g hcomm
  have hmul := congrArg (fun x => x * g) hEq
  simpa [mul_assoc] using hmul

theorem glauberman_odd_card_of_normal_disjoint_sylow_two (G : Type) [Group G] [Fintype G]
    (N : Subgroup G) (hN : N.Normal)
    (hdisj : ∃ P : Sylow 2 G, Disjoint N (P : Subgroup G)) :
    Odd (Nat.card N) := by
  rcases hdisj with ⟨P, hNP⟩
  letI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hnot2 : ¬ 2 ∣ Nat.card N := by
    intro h2
    rcases exists_prime_orderOf_dvd_card' (G := N) 2 h2 with ⟨u, hu⟩
    have huG : orderOf (u : G) = 2 := by
      simpa [Subgroup.orderOf_coe u] using hu
    let H : Subgroup G := Subgroup.zpowers (u : G)
    have hHu : (u : G) ∈ H := by
      change (u : G) ∈ Subgroup.zpowers (u : G)
      exact Subgroup.mem_zpowers (u : G)
    have hH2 : IsPGroup 2 H := by
      rw [IsPGroup.iff_orderOf]
      intro x
      have hx : orderOf (x : G) ∣ orderOf (u : G) := orderOf_dvd_of_mem_zpowers x.2
      have hx' : orderOf x ∣ 2 := by
        rw [Subgroup.orderOf_coe x, huG] at hx
        exact hx
      rcases (Nat.dvd_prime Nat.prime_two).mp hx' with hx1 | hx2
      · refine ⟨0, ?_⟩
        simpa using hx1
      · refine ⟨1, ?_⟩
        simpa using hx2
    letI : MulAction.IsPretransitive G (Sylow 2 G) := Sylow.isPretransitive_of_finite
    rcases IsPGroup.exists_le_sylow (P := H) hH2 with ⟨Q, hHQ⟩
    rcases MulAction.exists_smul_eq G P Q with ⟨a, ha⟩
    have huQ : (u : G) ∈ (Q : Subgroup G) := hHQ hHu
    have huP : a⁻¹ * (u : G) * a ∈ (P : Subgroup G) := by
      rw [← ha, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at huQ
      simpa [MulAut.conj_symm_apply] using
        (Subgroup.mem_map_equiv (f := MulAut.conj a) (K := (P : Subgroup G))
          (x := (u : G))).1 huQ
    have huN : a⁻¹ * (u : G) * a ∈ N := by
      exact hN.conj_mem' (u : G) u.2 a
    have hconj1 : a⁻¹ * (u : G) * a = 1 := by
      exact (Subgroup.disjoint_def.mp hNP) huN huP
    have hu_ne_one : (u : G) ≠ 1 := by
      intro hu1
      rw [hu1, orderOf_one] at huG
      norm_num at huG
    have hu1 : (u : G) = 1 := by
      calc
        (u : G) = a * (a⁻¹ * (u : G) * a) * a⁻¹ := by simp [mul_assoc]
        _ = 1 := by simp [hconj1, mul_assoc]
    exact hu_ne_one hu1
  have hne : ¬ Even (Nat.card N) := by
    simpa [even_iff_two_dvd] using hnot2
  exact Nat.not_even_iff_odd.mp hne

theorem glauberman_transfer_eq_pow_key_of_isolated (G : Type) [Group G]
    (t : G) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∀ (k : ℕ) (g₀ : G),
      g₀⁻¹ * t ^ k * g₀ ∈ Subgroup.centralizer ({t} : Set G) →
      g₀⁻¹ * t ^ k * g₀ = t ^ k := by
  intro k g₀ hmem
  rcases Nat.even_or_odd k with hk | hk
  · rcases hk with ⟨m, rfl⟩
    have ht2pow : t ^ 2 = 1 := by
      simpa only [pow_two] using ht2
    have hteven : t ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul, ht2pow, one_pow]
    calc
      g₀⁻¹ * t ^ (m + m) * g₀ = g₀⁻¹ * 1 * g₀ := by rw [hteven]
      _ = 1 := by simp
      _ = t ^ (m + m) := by rw [hteven]
  · rcases hk with ⟨m, rfl⟩
    have ht2pow : t ^ 2 = 1 := by
      simpa only [pow_two] using ht2
    have htodd : t ^ (2 * m + 1) = t := by
      rw [pow_add, pow_mul, ht2pow, one_pow, one_mul, pow_one]
    have hconjmem : g₀⁻¹ * t * g₀ ∈ Subgroup.centralizer ({t} : Set G) := by
      simpa only [htodd] using hmem
    have hcomm : (g₀⁻¹ * t * g₀) * t = t * (g₀⁻¹ * t * g₀) := by
      simpa only [Subgroup.mem_centralizer_singleton_iff] using hconjmem
    have hfix' : g₀⁻¹ * t * g₀⁻¹⁻¹ = t := by
      exact hisolated (g₀⁻¹) (by simpa only [inv_inv] using hcomm)
    have hfix : g₀⁻¹ * t * g₀ = t := by
      simpa only [inv_inv] using hfix'
    simpa only [htodd] using hfix

theorem glauberman_transfer_eq_pow_key_of_weakly_closed_in_sylow (G : Type) [Group G]
    (t : G) (ht2 : t * t = 1)
    (P : Sylow 2 G)
    (hweak : ∀ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) → g * t * g⁻¹ = t) :
    ∀ (k : ℕ) (g₀ : G),
      g₀⁻¹ * t ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * t ^ k * g₀ = t ^ k := by
  intro k g₀ hmem
  rcases Nat.even_or_odd k with hk | hk
  · rcases hk with ⟨m, rfl⟩
    have ht2pow : t ^ 2 = 1 := by
      simpa only [pow_two] using ht2
    have hteven : t ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul, ht2pow, one_pow]
    calc
      g₀⁻¹ * t ^ (m + m) * g₀ = g₀⁻¹ * 1 * g₀ := by rw [hteven]
      _ = 1 := by simp
      _ = t ^ (m + m) := by rw [hteven]
  · rcases hk with ⟨m, rfl⟩
    have ht2pow : t ^ 2 = 1 := by
      simpa only [pow_two] using ht2
    have htodd : t ^ (2 * m + 1) = t := by
      rw [pow_add, pow_mul, ht2pow, one_pow, one_mul, pow_one]
    have hconjmem : g₀⁻¹ * t * g₀ ∈ (P : Subgroup G) := by
      simpa only [htodd] using hmem
    have hfix' : g₀⁻¹ * t * (g₀⁻¹)⁻¹ = t := by
      exact hweak (g₀⁻¹) (by simpa using hconjmem)
    have hfix : g₀⁻¹ * t * g₀ = t := by
      simpa only [inv_inv] using hfix'
    simpa only [htodd] using hfix

theorem glauberman_transfer_kernel_of_sylow_control (G : Type) [Group G] [Fintype G] (t : G)
    (P : Sylow 2 G)
    (hP : Subgroup.normalizer (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  classical
  letI : Bracket G G := commutatorElement
  refine ⟨(MonoidHom.transferSylow P hP).ker, ?_, ?_, ?_⟩
  · exact MonoidHom.normal_ker _
  · have hnd : ¬ 2 ∣ Nat.card ((MonoidHom.transferSylow P hP).ker) := by
      simpa using (MonoidHom.not_dvd_card_ker_transferSylow (P := P) hP)
    exact Nat.not_even_iff_odd.mp (by
      simpa [even_iff_two_dvd] using hnd)
  · intro g
    have htop :
        (MonoidHom.transferSylow P hP).ker ⊔ (P : Subgroup G) = ⊤ := by
      exact (MonoidHom.ker_transferSylow_isComplement' (P := P) hP).sup_eq_top
    have hPc : (P : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
      le_trans Subgroup.le_normalizer hP
    haveI : IsMulCommutative (P : Subgroup G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative).mp hPc
    have hcomm :
        commutator G ≤ (MonoidHom.transferSylow P hP).ker := by
      exact (MonoidHom.normal_ker _).commutator_le_of_self_sup_commutative_eq_top htop inferInstance
    have hmem : ⁅g, t⁆ ∈ commutator G := by
      simpa [commutator_def] using
        (Subgroup.commutator_mem_commutator
          (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
          (show g ∈ (⊤ : Subgroup G) by simp)
          (show t ∈ (⊤ : Subgroup G) by simp))
    simpa [commutatorElement_def] using hcomm hmem

theorem glauberman_weakly_closed_in_sylow_of_isolated (G : Type) [Group G]
    (t : G)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t)
    (P : Sylow 2 G)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G)) :
    ∀ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) → g * t * g⁻¹ = t := by
  intro g hgP
  apply hisolated g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hPC hgP)

theorem glauberman_zStar_of_mem_center (G : Type) [Group G] [Fintype G] (t : G) (hcentral : t ∈ Subgroup.center G) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  refine ⟨⊥, Subgroup.normal_bot, ?_, ?_⟩
  · simpa using (show Odd 1 from odd_one)
  · intro g
    simp [Subgroup.mem_center_iff] at hcentral
    have ht : g * t * g⁻¹ = t := by
      calc
        g * t * g⁻¹ = t * g * g⁻¹ := by rw [hcentral g]
        _ = t := by simp
    simp [ht]

theorem glauberman_zStar_of_weakly_closed_in_sylow (G : Type) [Group G] [Fintype G]
    (t : G) (ht2 : t * t = 1)
    (hnotcentral : t ∉ Subgroup.center G)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hweak : ∀ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) → g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  -- This is now the core theorem. Work from the weak-closure hypothesis inside the chosen Sylow `2`-subgroup `P`, not from an attempted direct control theorem for `P`.
  -- 
  -- ## Primary route: transfer from a suitable abelian `2`-quotient of `P`
  -- 1. First derive the isolation hypothesis
  --    `hisolated := glauberman_isolated_of_weakly_closed_in_sylow G t ht2 P htP hweak`.
  --    This gives a robust fallback interface to the already-proved isolated lemmas.
  -- 2. Choose a finite commutative `2`-group quotient
  --    `φ : (P : Subgroup G) →* A`
  --    that is strong enough to detect the `2`-part carried by `t`.
  --    Natural candidates are a characteristic abelian quotient of `P`, or a quotient related to `P ⧸ frattini P` if that is the cleanest formalization.
  -- 3. Let `f := MonoidHom.transfer φ : G →* A`.
  -- 4. Use `glauberman_transfer_eq_pow_key_of_weakly_closed_in_sylow` with `MonoidHom.transfer_eq_pow` to compute `f t` directly from the weak-closure hypothesis.
  --    Because `P` is a Sylow `2`-subgroup, `P.index` is odd; together with `ht2 : t^2 = 1`, the odd-power formula simplifies so that `f t` is exactly the same class of `t` in `A`.
  -- 5. Set `N := f.ker`.
  --    Then:
  --    - `N` is normal by `MonoidHom.normal_ker`, and
  --    - `commutator G ≤ N` because the codomain is commutative, so every element
  --      `g * t * g⁻¹ * t⁻¹` automatically lies in `N`.
  -- 6. The remaining hard step is to choose `φ` strongly enough that `Disjoint N (P : Subgroup G)`.
  --    Once that is obtained, apply the generic node
  --    `glauberman_odd_card_of_normal_disjoint_sylow_two G N hN ⟨P, hdisj⟩`
  --    to conclude `Odd (Nat.card N)`.
  -- 
  -- ## Fallback route: pass through the proved isolated lemmas
  -- After step 1, you may also use the isolated machinery already in the blueprint:
  -- - `glauberman_centralizer_index_odd G t ht2 hisolated`
  -- - `glauberman_transfer_eq_pow_key_of_isolated G t ht2 hisolated`
  -- 
  -- This gives a second transfer computation through `C_G(t)` if the direct `P`-quotient route is awkward. Use this only as a computation aid; do **not** try to prove
  -- `Subgroup.normalizer (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G)`
  -- directly from `hweak`.
  -- 
  -- ## Practical warning
  -- The tempting one-line attempt
  -- ```lean
  -- refine glauberman_transfer_kernel_of_sylow_control G t P ?_
  -- ```
  -- is exactly the false route in disguise. Remove it entirely from consideration here.
  -- 
  -- So the theorem should decompose mentally as:
  -- 1. choose quotient/section of `P`,
  -- 2. compute transfer on `t`,
  -- 3. prove the transfer kernel is disjoint from `P`,
  -- 4. invoke `glauberman_odd_card_of_normal_disjoint_sylow_two`,
  -- 5. conclude all commutators with `t` lie in the kernel.
  sorry

theorem glauberman_zStar_of_noncentral_isolated (G : Type) [Group G] [Fintype G]
    (t : G) (ht2 : t * t = 1)
    (hnotcentral : t ∉ Subgroup.center G)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  obtain ⟨P, htP, hPC⟩ := glauberman_exists_sylow_two_containing_t G t ht2 hisolated
  have hweak := glauberman_weakly_closed_in_sylow_of_isolated G t hisolated P hPC
  exact glauberman_zStar_of_weakly_closed_in_sylow G t ht2 hnotcentral P htP hweak

theorem glauberman_zStar (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  by_cases hcentral : t ∈ Subgroup.center G
  · exact glauberman_zStar_of_mem_center G t hcentral
  · exact glauberman_zStar_of_noncentral_isolated G t ht2 hcentral hisolated


end Submission
