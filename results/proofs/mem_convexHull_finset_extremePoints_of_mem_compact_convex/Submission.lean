import Mathlib
import Submission.Helpers

open Set

namespace Submission

theorem closedConvexHull_extremePoints_eq_of_isCompact_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) : closedConvexHull ℝ (s.extremePoints ℝ) = s := by
  rw [closedConvexHull_eq_closure_convexHull, closure_convexHull_extremePoints hscomp hsconv]

theorem exists_finset_subset_card_le_finrank_add_one_of_mem_convexHull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) : ∃ t : Finset E, (↑t : Set E) ⊆ s ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [t] using Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  · let hAI : AffineIndependent ℝ ((↑) : t → E) :=
      by simpa [t] using Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
    simpa [t] using
      le_trans (AffineIndependent.card_le_finrank_succ hAI)
        (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))) 1)
  · simpa [t] using Caratheodory.mem_minCardFinsetOfMemConvexHull hx

theorem exists_fixed_arity_convcomb_of_mem_convexHull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) : ∃ w : Fin (Module.finrank ℝ E + 1) → ℝ, ∃ z : Fin (Module.finrank ℝ E + 1) → E, (∀ i, 0 ≤ w i) ∧ Finset.univ.sum w = 1 ∧ (∀ i, z i ∈ s) ∧ Finset.univ.sum (fun i => w i • z i) = x := by
  classical
  rcases exists_finset_subset_card_le_finrank_add_one_of_mem_convexHull hx with ⟨t, hts, hcard, hx_t⟩
  rcases (Finset.mem_convexHull').1 hx_t with ⟨w, hw0, hw1, hwx⟩
  have ht_nonempty : t.Nonempty := by
    by_contra ht
    rw [Finset.not_nonempty_iff_eq_empty] at ht
    simp [ht] at hw1
  let z0 : E := ht_nonempty.choose
  have hz0_mem_t : z0 ∈ t := ht_nonempty.choose_spec
  have hz0_mem_s : z0 ∈ s := hts hz0_mem_t
  let e := t.equivFin
  have hsum_sub : (∑ y : t, w (y : E)) = 1 := by
    rw [Finset.sum_coe_sort]
    exact hw1
  have hsum_sub_smul : (∑ y : t, w (y : E) • (y : E)) = x := by
    calc
      (∑ y : t, w (y : E) • (y : E)) = ∑ y ∈ t, w y • y := by
        simpa using (Finset.sum_coe_sort (s := t) (f := fun y : E => w y • y))
      _ = x := hwx
  have hsum_fin : (∑ i : Fin t.card, w (((e.symm i : t) : E))) = 1 := by
    calc
      (∑ i : Fin t.card, w (((e.symm i : t) : E))) = ∑ y : t, w (y : E) := by
        symm
        exact Fintype.sum_equiv e (fun y : t => w (y : E))
          (fun i : Fin t.card => w (((e.symm i : t) : E))) (by
            intro y
            simp [e])
      _ = 1 := hsum_sub
  have hsum_fin_smul : (∑ i : Fin t.card, w (((e.symm i : t) : E)) • (((e.symm i : t) : E))) = x := by
    calc
      (∑ i : Fin t.card, w (((e.symm i : t) : E)) • (((e.symm i : t) : E))) =
          ∑ y : t, w (y : E) • (y : E) := by
        symm
        exact Fintype.sum_equiv e (fun y : t => w (y : E) • (y : E))
          (fun i : Fin t.card => w (((e.symm i : t) : E)) • (((e.symm i : t) : E))) (by
            intro y
            simp [e])
      _ = x := hsum_sub_smul
  rcases Nat.exists_eq_add_of_le hcard with ⟨k, hk⟩
  let wpad : Fin (t.card + k) → ℝ :=
    Fin.append (fun i : Fin t.card => w (((e.symm i : t) : E))) (fun _ : Fin k => 0)
  let zpad : Fin (t.card + k) → E :=
    Fin.append (fun i : Fin t.card => (((e.symm i : t) : E))) (fun _ : Fin k => z0)
  have hwpad_nonneg : ∀ i, 0 ≤ wpad i := by
    rw [Fin.forall_fin_add]
    constructor
    · intro i
      simpa [wpad] using hw0 (((e.symm i : t) : E)) (e.symm i).2
    · intro j
      simp [wpad]
  have hzpad_mem : ∀ i, zpad i ∈ s := by
    rw [Fin.forall_fin_add]
    constructor
    · intro i
      simpa [zpad] using hts (e.symm i).2
    · intro j
      simpa [zpad] using hz0_mem_s
  have hwpad_sum : Finset.univ.sum wpad = 1 := by
    rw [Fin.sum_univ_add]
    simp [wpad, hsum_fin]
  have hsum_pad : Finset.univ.sum (fun i => wpad i • zpad i) = x := by
    rw [Fin.sum_univ_add]
    simp [wpad, zpad, hsum_fin_smul]
  let w' : Fin (Module.finrank ℝ E + 1) → ℝ := wpad ∘ finCongr hk
  let z' : Fin (Module.finrank ℝ E + 1) → E := zpad ∘ finCongr hk
  have hw'_nonneg : ∀ i, 0 ≤ w' i := by
    intro i
    exact hwpad_nonneg ((finCongr hk) i)
  have hz'_mem : ∀ i, z' i ∈ s := by
    intro i
    exact hzpad_mem ((finCongr hk) i)
  have hw'_sum : Finset.univ.sum w' = 1 := by
    calc
      Finset.univ.sum w' = ∑ j : Fin (t.card + k), wpad j := by
        exact Fintype.sum_equiv (finCongr hk) (fun i : Fin (Module.finrank ℝ E + 1) => w' i)
          wpad (by
            intro i
            rfl)
      _ = 1 := hwpad_sum
  have hsum' : Finset.univ.sum (fun i => w' i • z' i) = x := by
    calc
      Finset.univ.sum (fun i => w' i • z' i) = ∑ j : Fin (t.card + k), wpad j • zpad j := by
        exact Fintype.sum_equiv (finCongr hk)
          (fun i : Fin (Module.finrank ℝ E + 1) => w' i • z' i)
          (fun j : Fin (t.card + k) => wpad j • zpad j) (by
            intro i
            rfl)
      _ = x := hsum_pad
  exact ⟨w', z', hw'_nonneg, hw'_sum, hz'_mem, hsum'⟩

theorem isClosed_extremePoints_of_isCompact_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) : IsClosed (s.extremePoints ℝ) := by
  -- Important warning: there is **no** short field-projection theorem here (for example, do not try `hscomp.isClosed_extremePoints_of_convex` or `hscomp.isCompact_extremePoints_of_convex`; these names do not exist).
  -- 
  -- This node should carry the real geometric content, while compactness is recovered later as a trivial wrapper.
  -- 
  -- Recommended proof plan: prove that the non-extreme locus is open in `s`.
  -- 
  -- 1. Let `x ∈ s` with `hxne : x ∉ s.extremePoints ℝ`.
  --    By `hsconv.mem_extremePoints_iff_mem_diff_convexHull_diff`, obtain
  --    `hxrep : x ∈ convexHull ℝ (s \ {x})`.
  -- 2. Apply `eq_pos_convex_span_of_mem_convexHull` to `hxrep`.
  --    This should produce:
  --    - a finite type `ι`,
  --    - `z : ι → E` with `Set.range z ⊆ s \ {x}`,
  --    - `AffineIndependent ℝ z`,
  --    - strictly positive weights `w : ι → ℝ`,
  --    - `∑ i, w i = 1`,
  --    - `∑ i, w i • z i = x`.
  -- 3. Let `P := convexHull ℝ (Set.range z)`. By `convexHull_min`, `P ⊆ s`.
  -- 4. Because the weights are all strictly positive and `z` is affinely independent, `x` lies in the intrinsic interior of the simplex `P`.
  -- 5. Show that every point in the intrinsic interior of a positive-dimensional simplex contained in `s` is **not** extreme in `s`:
  --    - a point in the intrinsic interior of a simplex lies on a nontrivial open segment with endpoints in that simplex;
  --    - since `P ⊆ s`, those endpoints lie in `s`, so such a point cannot belong to `s.extremePoints ℝ`.
  -- 6. Therefore there is a neighborhood of `x` inside `s` contained in the non-extreme locus. Hence the non-extreme locus is open in `s`.
  -- 7. Since `hscomp.isClosed : IsClosed s`, a subset of `s` whose complement is open in `s` is closed in the ambient space. Conclude `IsClosed (s.extremePoints ℝ)`.
  -- 
  -- Useful declarations to try explicitly:
  -- - `Convex.mem_extremePoints_iff_mem_diff_convexHull_diff`
  -- - `eq_pos_convex_span_of_mem_convexHull`
  -- - `convexHull_min`
  -- - `extremePoints_subset`
  -- - intrinsic tools from `Mathlib.Analysis.Convex.Intrinsic`
  --   (`intrinsicInterior`, `intrinsicInterior_subset`, `Set.Nonempty.intrinsicInterior`, etc.)
  -- - if needed for boundary reductions: `disjoint_interior_extremePoints`, `IsClosed.frontier_eq`
  -- 
  -- Alternative face-based route if the simplex-intrinsic-interior step is hard to formalize:
  -- 1. Every non-extreme boundary point lies in the intrinsic interior of a nontrivial proper exposed face.
  -- 2. Exposed faces are compact and convex (`IsExposed.isCompact`, `IsExposed.convex`) and are extreme in `s` (`IsExposed.isExtreme`).
  -- 3. Points in the intrinsic interior of a nontrivial exposed face are not extreme in `s`, and these intrinsic interiors are relatively open in `s`.
  -- 4. Hence the complement of `s.extremePoints ℝ` is open in `s`.
  -- 
  -- This node is the right hard target: once it is proved, `isCompact_extremePoints_of_isCompact_of_convex` is immediate, and the whole blueprint should collapse.
  sorry

theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) : IsCompact (convexHull ℝ s) := by
  let N := Fin (Module.finrank ℝ E + 1)
  let K : Set (N → ℝ) := stdSimplex ℝ N
  let P : Set (N → E) := Set.pi Set.univ (fun _ : N => s)
  let F : (N → ℝ) × (N → E) → E := fun p => Finset.univ.sum (fun i => p.1 i • p.2 i)
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hK : IsCompact K := by
    simpa [K] using (isCompact_stdSimplex ℝ N)
  have hP : IsCompact P := by
    simpa [P] using (isCompact_univ_pi (fun _ : N => hscomp))
  have hsubset₁ : F '' (K ×ˢ P) ⊆ convexHull ℝ s := by
    rintro x ⟨⟨w, z⟩, hp, rfl⟩
    rcases hp with ⟨hw, hzP⟩
    have hw0 : ∀ i, 0 ≤ w i := by
      simpa [K, stdSimplex] using hw.1
    have hw1 : Finset.univ.sum w = 1 := by
      simpa [K, stdSimplex] using hw.2
    have hz : ∀ i, z i ∈ s := by
      change ∀ i, i ∈ Set.univ → z i ∈ s at hzP
      intro i
      exact hzP i (by simp)
    exact mem_convexHull_of_exists_fintype w z hw0 hw1 hz rfl
  have hsubset₂ : convexHull ℝ s ⊆ F '' (K ×ˢ P) := by
    intro x hx
    rcases exists_fixed_arity_convcomb_of_mem_convexHull hx with ⟨w, z, hw0, hw1, hz, hsum⟩
    refine ⟨⟨w, z⟩, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [K, stdSimplex] using And.intro hw0 hw1
      · change ∀ i, i ∈ Set.univ → z i ∈ s
        intro i hi
        exact hz i
    · simpa [F] using hsum
  have hEq : convexHull ℝ s = F '' (K ×ˢ P) := Set.Subset.antisymm hsubset₂ hsubset₁
  rw [hEq]
  exact (hK.prod hP).image hFcont

theorem isCompact_extremePoints_of_isCompact_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) : IsCompact (s.extremePoints ℝ) := by
  have hclosed : IsClosed (s.extremePoints ℝ) :=
    isClosed_extremePoints_of_isCompact_of_convex hscomp hsconv
  exact hscomp.of_isClosed_subset hclosed extremePoints_subset

theorem isClosed_convexHull_extremePoints_of_isCompact_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) : IsClosed (convexHull ℝ (s.extremePoints ℝ)) := by
  have hcomp_ext : IsCompact (s.extremePoints ℝ) :=
    isCompact_extremePoints_of_isCompact_of_convex hscomp hsconv
  have hcomp_conv : IsCompact (convexHull ℝ (s.extremePoints ℝ)) :=
    isCompact_convexHull_of_isCompact hcomp_ext
  exact hcomp_conv.isClosed

theorem mem_convexHull_extremePoints_of_mem_compact_convex_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {x : E} (hscomp : IsCompact s) (hsconv : Convex ℝ s) (hx : x ∈ s) : x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  have hxcl : x ∈ closure (convexHull ℝ (s.extremePoints ℝ)) := by
    rw [closure_convexHull_extremePoints hscomp hsconv]
    exact hx
  have hclosed : IsClosed (convexHull ℝ (s.extremePoints ℝ)) :=
    isClosed_convexHull_extremePoints_of_isCompact_of_convex hscomp hsconv
  simpa [hclosed.closure_eq] using hxcl

theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  obtain hxext : x ∈ convexHull ℝ (s.extremePoints ℝ) :=
    mem_convexHull_extremePoints_of_mem_compact_convex_core hscomp hsconv hx
  exact exists_finset_subset_card_le_finrank_add_one_of_mem_convexHull (s := s.extremePoints ℝ) hxext


end Submission
