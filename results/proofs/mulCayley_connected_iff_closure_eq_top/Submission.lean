import Mathlib
import Submission.Helpers

namespace Submission

theorem mulCayley_mem_closure_of_adj {G : Type*} [Group G] (S : Set G) {u v : G} (hu : u ∈ Subgroup.closure S) (h : (SimpleGraph.mulCayley S).Adj u v) : v ∈ Subgroup.closure S := by
  rw [SimpleGraph.mulCayley_adj] at h
  rcases h with ⟨_, hS | hS⟩
  · have huv : u⁻¹ * v ∈ Subgroup.closure S := Subgroup.subset_closure hS
    have hv : u * (u⁻¹ * v) ∈ Subgroup.closure S := Subgroup.mul_mem (Subgroup.closure S) hu huv
    simpa [mul_assoc] using hv
  · have huv : v⁻¹ * u ∈ Subgroup.closure S := Subgroup.subset_closure hS
    have hinv : (v⁻¹ * u)⁻¹ ∈ Subgroup.closure S := Subgroup.inv_mem (Subgroup.closure S) huv
    have hv : u * (v⁻¹ * u)⁻¹ ∈ Subgroup.closure S := Subgroup.mul_mem (Subgroup.closure S) hu hinv
    simpa [mul_assoc] using hv

theorem mulCayley_reachable_mul_left {G : Type*} [Group G] (S : Set G) {u v d : G} (h : (SimpleGraph.mulCayley S).Reachable u v) : (SimpleGraph.mulCayley S).Reachable (d * u) (d * v) := by
  let f : SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S :=
    { toFun := fun x => d * x
      map_rel' := by
        intro a b hab
        exact (SimpleGraph.mulCayley_adj_mul_iff_right (s := S) (d := d) (u := a) (v := b)).2 hab }
  exact h.map f

theorem mulCayley_reachable_one_inv {G : Type*} [Group G] (S : Set G) {x : G} (hx : (SimpleGraph.mulCayley S).Reachable 1 x) : (SimpleGraph.mulCayley S).Reachable 1 x⁻¹ := by
  simpa only [inv_mul_cancel, mul_one] using
    mulCayley_reachable_mul_left S (d := x⁻¹) hx.symm

theorem mulCayley_reachable_one_mem_closure {G : Type*} [Group G] (S : Set G) {g : G} (h : (SimpleGraph.mulCayley S).Reachable 1 g) : g ∈ Subgroup.closure S := by
  rcases h with ⟨p⟩
  have hwalk : ∀ {u v : G}, (SimpleGraph.mulCayley S).Walk u v → u ∈ Subgroup.closure S → v ∈ Subgroup.closure S := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        simpa using hu
    | @cons u v w hadj p ih =>
        intro hu
        have hv : v ∈ Subgroup.closure S := mulCayley_mem_closure_of_adj S hu hadj
        exact ih hv
  exact hwalk p (Subgroup.one_mem (Subgroup.closure S))

theorem mulCayley_reachable_one_mul {G : Type*} [Group G] (S : Set G) {x y : G} (hx : (SimpleGraph.mulCayley S).Reachable 1 x) (hy : (SimpleGraph.mulCayley S).Reachable 1 y) : (SimpleGraph.mulCayley S).Reachable 1 (x * y) := by
  have hxy : (SimpleGraph.mulCayley S).Reachable x (x * y) := by
    simpa only [mul_one] using (mulCayley_reachable_mul_left S (u := 1) (v := y) (d := x) hy)
  exact hx.trans hxy

theorem mulCayley_mem_reachable_one_of_mem_closure {G : Type*} [Group G] (S : Set G) {g : G} (hg : g ∈ Subgroup.closure S) : (SimpleGraph.mulCayley S).Reachable 1 g := by
  classical
  refine Subgroup.closure_induction (k := S) (p := fun x _ => (SimpleGraph.mulCayley S).Reachable 1 x) ?_ ?_ ?_ ?_ hg
  · intro x hx
    by_cases hx1 : x = 1
    · simpa [hx1] using (SimpleGraph.Reachable.refl 1 : (SimpleGraph.mulCayley S).Reachable 1 1)
    · have hne : 1 ≠ x := by simpa [eq_comm] using hx1
      have hx' : 1⁻¹ * x ∈ S := by simpa using hx
      exact SimpleGraph.Adj.reachable ((SimpleGraph.mulCayley_adj (s := S) 1 x).2 ⟨hne, Or.inl hx'⟩)
  · exact SimpleGraph.Reachable.refl 1
  · intro x y hx hy hxR hyR
    exact mulCayley_reachable_one_mul S hxR hyR
  · intro x hx hxR
    exact mulCayley_reachable_one_inv S hxR

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro hconn
    apply top_unique
    intro g hg
    exact mulCayley_reachable_one_mem_closure S (hconn 1 g)
  · intro hS
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨1, ?_⟩
    intro g
    apply mulCayley_mem_reachable_one_of_mem_closure S
    simpa [hS] using (show g ∈ (⊤ : Subgroup G) from Subgroup.mem_top g)



end Submission
