import Mathlib
import Submission.Helpers

namespace Submission

theorem rado_locPathConnected {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] : LocPathConnectedSpace X := by
  simpa using (ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X))

theorem rado_locallyCompact {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] : LocallyCompactSpace X := by
  simpa using (Manifold.locallyCompact_of_finiteDimensional (I := modelWithCornersSelf ℂ ℂ) (M := X))

theorem rado_pathConnected {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] : PathConnectedSpace X := by
  haveI : LocPathConnectedSpace X := rado_locPathConnected (X := X)
  exact PathConnectedSpace.of_locPathConnectedSpace (X := X)

theorem rado_regular {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] : RegularSpace X := by
  haveI : LocallyCompactSpace X := rado_locallyCompact (X := X)
  haveI : WeaklyLocallyCompactSpace X := inferInstance
  haveI : R1Space X := inferInstance
  infer_instance

theorem rado_countable_chart_cover_points {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : ∃ t : Set X, t.Countable ∧ (⋃ x ∈ t, (chartAt ℂ x).source = Set.univ) := by
  -- This is the actual hard theorem. Express the countable-cover problem using preferred chart centers instead of arbitrary charts.
  -- 
  -- Target shape.
  -- Build a countable set `t : Set X` such that the union of the preferred chart sources `⋃ x ∈ t, (chartAt ℂ x).source` is all of `X`.
  -- 
  -- Recommended proof architecture.
  -- 1. Fix a base point `x₀ : X`.
  -- 2. Use `rado_locallyCompact` and `rado_regular` to shrink chart neighborhoods to relatively compact open sets with compact closure staying inside chart sources; `exists_open_between_and_isCompact_closure` is the main shrinking tool.
  -- 3. Use `rado_locPathConnected` to further refine to path-connected neighborhoods. In chart coordinates, restrict to a countable family of rational discs / rational rectangles in `ℂ` whose closures remain inside the target. This gives a countable alphabet of admissible local moves.
  -- 4. Generate centers recursively from `x₀` by finite admissible continuation chains between overlapping preferred charts. Finite lists over a countable alphabet are countable, so the set of all reachable endpoints is countable.
  -- 5. Let `U := ⋃ x ∈ t, (chartAt ℂ x).source`. Show `U` is nonempty and open. For coverage, either:
  --    - use `rado_pathConnected` to choose a path from `x₀` to any `x`, cover the compact path image by finitely many admissible overlapping neighborhoods, and conclude that `x` lies in the source of a reachable preferred chart; or
  --    - show `U` is closed under one more continuation step and hence is also closed, then apply connectedness.
  -- 6. The analytic uniqueness input for consistent continuation on connected overlaps should be `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
  -- 
  -- Critical guidance.
  -- - Work with `chartAt ℂ x` throughout; do not try to construct arbitrary `OpenPartialHomeomorph`s as the main object.
  -- - Do NOT use `countable_cover_nhds_of_sigmaCompact`, `rado_sigmaCompact`, `rado_secondCountable_source_localHomeomorph`, or either theorem named `rado_riemannSurface`; all of these are downstream/circular here.
  -- - Do NOT try to hide the argument inside a generic Lindelöf/subcover theorem. The real content is analytic continuation / propagation of preferred charts from one countable seed family.
  sorry

theorem rado_countable_subatlas {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : ∃ s : Set (OpenPartialHomeomorph X ℂ), s.Countable ∧ (⋃ e ∈ s, e.source = Set.univ) := by
  obtain ⟨t, ht, hcover⟩ := rado_countable_chart_cover_points (X := X)
  refine ⟨(chartAt ℂ) '' t, ht.image (chartAt ℂ), ?_⟩
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨e, he, hx⟩
    rcases he with ⟨y, hy, rfl⟩
    simp only [Set.mem_univ]
  · intro hx
    rw [← hcover] at hx
    simp only [Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩
    exact ⟨chartAt ℂ y, ⟨y, hy, rfl⟩, hxy⟩

theorem rado_secondCountable_of_countable_chart_cover {X : Type*} [TopologicalSpace X] {s : Set (OpenPartialHomeomorph X ℂ)} : s.Countable → (⋃ e ∈ s, e.source = Set.univ) → SecondCountableTopology X := by
  intro hsc hscover
  letI : Encodable s := hsc.toEncodable
  haveI : ∀ e : s, SecondCountableTopology ((e : OpenPartialHomeomorph X ℂ).source) :=
    fun e => (e : OpenPartialHomeomorph X ℂ).secondCountableTopology_source
  rw [Set.biUnion_eq_iUnion] at hscover
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun e : s => ((e : OpenPartialHomeomorph X ℂ).source : Set X))
    (Uo := fun e => (e : OpenPartialHomeomorph X ℂ).open_source)
    hscover

theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X := by
  obtain ⟨s, hsc, hscover⟩ := rado_countable_subatlas (X := X)
  exact rado_secondCountable_of_countable_chart_cover (X := X) hsc hscover


end Submission
