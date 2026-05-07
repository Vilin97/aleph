import ChallengeDeps
import Submission.Helpers

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

theorem centralizer_adjoin_eq_centralizer {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (s : Set A) :
    Subalgebra.centralizer R ((Algebra.adjoin R s : Subalgebra R A) : Set A) =
      Subalgebra.centralizer R s := by
  apply le_antisymm
  · exact
      Subalgebra.centralizer_le (R := R) s ((Algebra.adjoin R s : Subalgebra R A) : Set A)
        Algebra.subset_adjoin
  · exact
      (Subalgebra.le_centralizer_iff (Algebra.adjoin R s) (Subalgebra.centralizer R s)).mp
        (Algebra.adjoin_le_centralizer_centralizer (R := R) s)

theorem centralizer_glAction_toSubmodule_eq_linHom_invariants {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (k : ℕ) :
    (Subalgebra.centralizer R (Set.range (glAction R M k))).toSubmodule =
      (Representation.linHom (glAction R M k) (glAction R M k)).invariants := by
  ext x
  constructor <;> intro hx
  · have hx' : x ∈ Subalgebra.centralizer R (Set.range (glAction R M k)) := by
      simpa using hx
    rw [Representation.mem_invariants]
    intro g
    have hxg := hx' (glAction R M k g) ⟨g, rfl⟩
    rw [Representation.linHom.mem_invariants_iff_comm (X := Rep.of (glAction R M k))
      (Y := Rep.of (glAction R M k))]
    simpa [Module.End.mul_eq_comp] using hxg.symm
  · rw [Representation.mem_invariants] at hx
    have hx' : x ∈ Subalgebra.centralizer R (Set.range (glAction R M k)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro y hy
      rcases hy with ⟨g, rfl⟩
      have hxg := hx g
      rw [Representation.linHom.mem_invariants_iff_comm (X := Rep.of (glAction R M k))
        (Y := Rep.of (glAction R M k))] at hxg
      simpa [Module.End.mul_eq_comp] using hxg.symm
    simpa using hx'

theorem glAction_symAction_commute {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (k : ℕ) (σ : Equiv.Perm (Fin k)) (g : (M →ₗ[R] M)ˣ) :
    Commute (glAction R M k g) (symAction R M k σ) := by
  ext x
  simpa [glAction, symAction, Module.End.mul_apply] using
    (PiTensorProduct.map_reindex (R := R) (s := fun _ : Fin k => M) (t := fun _ : Fin k => M)
      (f := fun _ => (g : M →ₗ[R] M)) σ x).symm

theorem adjoin_glAction_le_centralizer_symAction {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (k : ℕ) :
    Algebra.adjoin R (Set.range (glAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (symAction R M k)) := by
  rw [Algebra.adjoin_le_iff]
  intro z hz
  rcases hz with ⟨g, rfl⟩
  change glAction R M k g ∈ Subalgebra.centralizer R (Set.range (symAction R M k))
  rw [Subalgebra.mem_centralizer_iff]
  intro w hw
  rcases hw with ⟨σ, rfl⟩
  exact (glAction_symAction_commute (R := R) (M := M) k σ g).eq.symm

theorem adjoin_symAction_le_centralizer_glAction {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (k : ℕ) :
    Algebra.adjoin R (Set.range (symAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  rw [Algebra.adjoin_le_iff]
  intro z hz
  rcases hz with ⟨σ, rfl⟩
  change (symAction R M k) σ ∈ Subalgebra.centralizer R (Set.range (glAction R M k))
  rw [Subalgebra.mem_centralizer_iff]
  intro w hw
  rcases hw with ⟨g, rfl⟩
  exact (glAction_symAction_commute (R := R) (M := M) k σ g).eq

theorem symAction_asAlgebraHom_range_toSubmodule_eq_span {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (k : ℕ) :
    ((Representation.asAlgebraHom (symAction R M k)).range.toSubmodule) =
      Submodule.span R (Set.range (symAction R M k)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    let p : MonoidAlgebra R (Equiv.Perm (Fin k)) → Prop := fun a =>
      (Representation.asAlgebraHom (symAction R M k)).toRingHom a ∈
        Submodule.span R (Set.range (symAction R M k))
    change p a
    refine MonoidAlgebra.induction_on a ?_ ?_ ?_
    · intro σ
      show p (MonoidAlgebra.of R (Equiv.Perm (Fin k)) σ)
      dsimp [p]
      simpa [Representation.asAlgebraHom_single] using
        (Submodule.smul_mem (Submodule.span R (Set.range (symAction R M k))) (1 : R)
          (Submodule.subset_span ⟨σ, rfl⟩))
    · intro a b ha hb
      show p (a + b)
      dsimp [p] at ha hb ⊢
      simpa using Submodule.add_mem (Submodule.span R (Set.range (symAction R M k))) ha hb
    · intro r a ha
      show p (r • a)
      dsimp [p] at ha ⊢
      simpa using Submodule.smul_mem (Submodule.span R (Set.range (symAction R M k))) r ha
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨MonoidAlgebra.of R (Equiv.Perm (Fin k)) σ, Representation.asAlgebraHom_of _ σ⟩

theorem linHom_invariants_le_symAction_asAlgebraHom_range {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    (Representation.linHom (glAction R M k) (glAction R M k)).invariants ≤
      ((Representation.asAlgebraHom (symAction R M k)).range.toSubmodule) := by
  -- Do **not** retry the previous one-line proof; `linHom_invariants_le_span_symAction_range` does not exist. Treat this as the core Schur–Weyl step.
  -- 
  -- Most promising route now: a **basis/coordinates proof after reducing to a finite free module**.
  -- 
  -- 1. First rewrite the target with
  --    `symAction_asAlgebraHom_range_toSubmodule_eq_span`; the goal is equivalent to
  --    `... ≤ Submodule.span R (Set.range (symAction R M k))`.
  -- 
  -- 2. Use `FiniteDimensional` to choose a basis `b : Basis ι R M` with `[Fintype ι] [DecidableEq ι]`.
  --    Transport the whole problem along `b.equivFun : M ≃ₗ[R] (ι → R)` and the induced tensor-power
  --    equivalence
  --    `PiTensorProduct.congr (fun _ : Fin k => b.equivFun)`.
  --    Important naturality lemmas here are:
  --    - `PiTensorProduct.congr_tprod`
  --    - `PiTensorProduct.ext`
  --    - `PiTensorProduct.map_tprod`
  --    - `PiTensorProduct.reindex_tprod`
  --    After transport, you may assume `M = ι → R` and work with the standard basis `Pi.basisFun R ι`.
  -- 
  -- 3. In coordinates, prove that a `GL(M)`-equivariant endomorphism has matrix coefficients depending
  --    only on the `Equiv.Perm (Fin k)`-orbit of a basis tensor.
  --    Recommended concrete generators of `GL(M)`:
  --    - diagonal units;
  --    - transvections `1 + c • e_{ij}` built from matrix units / basis endomorphisms.
  --    Relevant basis lemmas:
  --    - `Module.Basis.end`
  --    - `Module.Basis.end_apply_apply`
  --    - `LinearMap.toMatrixAlgEquiv`
  --    - `Matrix.isUnit_toLin_iff` / `LinearMap.isUnit_toMatrix_iff`
  -- 
  -- 4. Once coefficients are shown to be orbit-constant, reconstruct the operator as an `R`-linear
  --    combination of the permutation operators `symAction R M k σ`. The endpoint should be span
  --    membership, not direct range membership; then finish with
  --    `symAction_asAlgebraHom_range_toSubmodule_eq_span`.
  -- 
  -- 5. If you need to switch between invariant elements and commuting linear maps, use
  --    - `Representation.linHom.mem_invariants_iff_comm`
  --    - `linHom.invariantsEquivRepHom`
  --    rather than unfolding the action manually.
  -- 
  -- Conceptual fallback if coordinates get messy:
  -- - combine semisimplicity of the symmetric-group action (Maschke: `MonoidAlgebra.Submodule.instIsSemisimpleRepresentation`)
  --   with Jacobson density (`Module.Finite.toModuleEnd_moduleEnd_surjective`) and
  --   `Representation.asModuleEquiv_map_smul`; however this still seems to require a separate argument
  --   identifying the relevant commutant, so the coordinate proof is still the primary plan.
  -- 
  -- Sanity checks:
  -- - `k = 0`: both sides are the line spanned by `1`.
  -- - `k = 1`: invariants are scalar maps, matching the trivial `S₁`-action.
  -- - Because `Invertible (k.factorial : R)` forces characteristic `0` or `> k`, finite-field pathologies
  --   from small characteristic should not obstruct the usual Schur–Weyl argument.
  -- 
  -- Avoid lazy offloading: if you introduce any further helpers, they should be concrete pieces such as
  -- "basis transport", "orbit-constancy under transvections", or "reconstruction from orbit sums", not a
  -- single giant helper restating this theorem.
  sorry

theorem centralizer_glAction_le_adjoin_symAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (glAction R M k)) ≤
      Algebra.adjoin R (Set.range (symAction R M k)) := by
  intro x hx
  have hxSub : x ∈ (Subalgebra.centralizer R (Set.range (glAction R M k))).toSubmodule := hx
  rw [centralizer_glAction_toSubmodule_eq_linHom_invariants (R := R) (M := M) k] at hxSub
  have hxRange : x ∈ ((Representation.asAlgebraHom (symAction R M k)).range.toSubmodule) :=
    linHom_invariants_le_symAction_asAlgebraHom_range (R := R) (M := M) (k := k) hxSub
  rw [symAction_asAlgebraHom_range_toSubmodule_eq_span (R := R) (M := M) k] at hxRange
  exact (Algebra.span_le_adjoin (R := R) (s := Set.range (symAction R M k))) hxRange

theorem symAction_range_eq_centralizer_glAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (symAction R M k)) =
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  exact le_antisymm
    (adjoin_symAction_le_centralizer_glAction (R := R) (M := M) k)
    (centralizer_glAction_le_adjoin_symAction (R := R) (M := M) (k := k))


end Submission
