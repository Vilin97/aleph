import ChallengeDeps
import Submission.Helpers

open LeanEval.Topology
open Set (Icc Ioo)

namespace Submission

theorem contractibleSpace_of_retract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (i : ContinuousMap X Y) (r : ContinuousMap Y X) (hr : r.comp i = ContinuousMap.id X) [ContractibleSpace Y] : ContractibleSpace X := by
  refine (contractible_iff_id_nullhomotopic X).2 ?_
  have hY : (ContinuousMap.id Y).Nullhomotopic := id_nullhomotopic Y
  have h1 : (r.comp (ContinuousMap.id Y)).Nullhomotopic :=
    ContinuousMap.Nullhomotopic.comp_right hY r
  have h2 : ((r.comp (ContinuousMap.id Y)).comp i).Nullhomotopic :=
    ContinuousMap.Nullhomotopic.comp_left h1 i
  simpa [ContinuousMap.comp_assoc, hr] using h2

def houseSupportWall : Set (ℝ × ℝ × ℝ) := ({(2 : ℝ)} : Set ℝ) ×ˢ Icc 1 3 ×ˢ Icc 0 2

theorem contractibleSpace_houseSupportWall: ContractibleSpace houseSupportWall := by
  simpa [houseSupportWall] using
    (Convex.contractibleSpace
      ((convex_singleton (2 : ℝ)).prod
        ((convex_Icc (1 : ℝ) (3 : ℝ)).prod (convex_Icc (0 : ℝ) (2 : ℝ))))
      (by
        refine ⟨((2 : ℝ), (1 : ℝ), (0 : ℝ)), ?_⟩
        simp [houseSupportWall]))

theorem houseSupportWall_subset_houseWithTwoRooms: houseSupportWall ⊆ HouseWithTwoRooms := by
  intro p hp
  simp [houseSupportWall, HouseWithTwoRooms] at hp ⊢
  left
  right
  left
  left
  left
  right
  exact hp

def houseWithTwoRooms_box : Set (ℝ × ℝ × ℝ) := Icc 0 4 ×ˢ Icc 0 3 ×ˢ Icc 0 2

theorem contractibleSpace_houseWithTwoRooms_box: ContractibleSpace houseWithTwoRooms_box := by
  refine Convex.contractibleSpace ?_ ?_
  · simpa [houseWithTwoRooms_box, Set.Icc_prod_Icc] using
      (convex_Icc (𝕜 := ℝ) (r := ((0 : ℝ), ((0 : ℝ), (0 : ℝ))))
        (s := ((4 : ℝ), ((3 : ℝ), (2 : ℝ)))))
  · refine ⟨((0 : ℝ), ((0 : ℝ), (0 : ℝ))), ?_⟩
    simp [houseWithTwoRooms_box]

theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms := by
  sorry


end Submission
