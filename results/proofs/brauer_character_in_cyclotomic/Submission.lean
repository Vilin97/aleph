import Mathlib
import Submission.Helpers

namespace Submission

theorem cyclotomic_embedding_contains_nth_roots (n : ℕ) (hn : n ≠ 0) :
    ∃ φ : CyclotomicField n ℚ →+* ℂ, ∀ z : ℂ, z ^ n = 1 → z ∈ φ.range := by
  classical
  let K : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ {z : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ z ^ m = 1}
  letI : IsCyclotomicExtension ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero (n := n) (K := ℚ)
  obtain ⟨e⟩ :=
    IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
      (K := ℚ) (S := ({n} : Set ℕ)) (L := CyclotomicField n ℚ) (M := ℂ)
  refine ⟨(IntermediateField.val K).toRingHom.comp e.toAlgHom.toRingHom, ?_⟩
  intro z hz
  refine ⟨e.symm ⟨z, ?_⟩, ?_⟩
  · change z ∈ IntermediateField.adjoin ℚ {z : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ z ^ m = 1}
    exact (IntermediateField.subset_adjoin (F := ℚ)
      (S := {z : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ z ^ m = 1}))
      ⟨n, by simp, hn, hz⟩
  · simp

theorem matrix_charpoly_root_pow_eq_one (n : ℕ) {m : Type} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A ^ n = 1) {z : ℂ}
    (hz : z ∈ A.charpoly.roots) :
    z ^ n = 1 := by
  have hroot : A.charpoly.IsRoot z := by
    rw [Polynomial.mem_roots (A.charpoly_monic.ne_zero)] at hz
    exact hz
  have hzspec : z ∈ spectrum ℂ A := by
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have hpow : z ^ n ∈ spectrum ℂ (A ^ n) := by
    exact spectrum.pow_mem_pow A n hzspec
  by_cases hs : Subsingleton (Matrix m m ℂ)
  · have hspec1 : spectrum ℂ (A ^ n) = (∅ : Set ℂ) := by
      rw [hA]
      exact spectrum.of_subsingleton (1 : Matrix m m ℂ)
    rw [hspec1] at hpow
    simp at hpow
  · have hnt : Nontrivial (Matrix m m ℂ) := by
      exact not_subsingleton_iff_nontrivial.mp hs
    have hspec1 : spectrum ℂ (A ^ n) = ({1} : Set ℂ) := by
      rw [hA]
      exact spectrum.one_eq
    rw [hspec1] at hpow
    simpa using hpow

theorem trace_mem_cyclotomic_range_of_pow_eq_one (n : ℕ) (φ : CyclotomicField n ℚ →+* ℂ)
    (hφ : ∀ z : ℂ, z ^ n = 1 → z ∈ φ.range)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (f : V →ₗ[ℂ] V) (hf : f ^ n = 1) :
    LinearMap.trace ℂ V f ∈ φ.range := by
  classical
  let b := Module.finBasis ℂ V
  let A := LinearMap.toMatrix b b f
  have hA : A ^ n = 1 := by
    rw [show A = LinearMap.toMatrix b b f by rfl]
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  have htrace : LinearMap.trace ℂ V f = Matrix.trace A := by
    simpa [A, b] using (LinearMap.trace_eq_matrix_trace (R := ℂ) (b := b) (f := f))
  have hroot_mem : ∀ z : ℂ, z ∈ A.charpoly.roots → z ∈ φ.range := by
    intro z hz
    exact hφ z (matrix_charpoly_root_pow_eq_one n A hA hz)
  have hsum_mem : ∀ t : Multiset ℂ, (∀ z : ℂ, z ∈ t → z ∈ φ.range) → t.sum ∈ φ.range := by
    intro t
    refine Multiset.induction_on t ?_ ?_
    · intro _
      exact ⟨0, by simp⟩
    · intro a s ih hs
      have ha : a ∈ φ.range := hs a (by simp)
      have hs' : ∀ z : ℂ, z ∈ s → z ∈ φ.range := by
        intro z hz
        exact hs z (by simp [hz])
      have hssum : s.sum ∈ φ.range := ih hs'
      rcases ha with ⟨x, hx⟩
      rcases hssum with ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      simpa [Multiset.sum_cons, hx, hy] using φ.map_add x y
  rw [htrace, Matrix.trace_eq_sum_roots_charpoly]
  exact hsum_mem _ hroot_mem

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  let n := Monoid.exponent G
  have hn : n ≠ 0 := by
    simpa [n] using Monoid.exponent_ne_zero_of_finite (G := G)
  rcases cyclotomic_embedding_contains_nth_roots n hn with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro V hVadd hVmod hVfd ρ g
  have hpow : (ρ g) ^ n = 1 := by
    simpa [n] using congrArg ρ (Monoid.pow_exponent_eq_one g)
  exact trace_mem_cyclotomic_range_of_pow_eq_one n φ hφ V hVadd hVmod hVfd (ρ g) hpow


end Submission
