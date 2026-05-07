import ChallengeDeps
import Submission.Helpers

import Challenge
open LeanEval.GroupTheory

namespace Submission

theorem conj_ker_eq_center (S : Type) [Group S] : (MulAut.conj : S →* MulAut S).ker = Subgroup.center S := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hg x
    have h := congrArg (fun f : MulAut S => f x) hg
    have h' := congrArg (fun y => y * g) h
    simpa [MulAut.conj_apply, mul_assoc] using h'.symm
  · intro hg
    ext x
    have h' := congrArg (fun y => y * g⁻¹) (hg x).symm
    simpa [MulAut.conj_apply, mul_assoc] using h'


theorem schreier_conjecture (S : Type) [Group S] [Fintype S] [IsSimpleGroup S]
    (hS : ∃ a b : S, ¬ Commute a b) :
    IsSolvable (MulAut S ⧸ (MulAut.conj : S →* MulAut S).range) := by
  simpa using (_root_.schreier_conjecture (S := S) hS)

theorem simple_noncomm_center_eq_bot (S : Type) [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, ¬ Commute a b) : Subgroup.center S = ⊥ := by
  rcases (Subgroup.instNormalCenter : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · rcases hS with ⟨a, b, hab⟩
    letI : CommGroup S := Group.commGroupOfCenterEqTop h
    have hcomm : Commute a b := by
      simpa [Commute] using mul_comm a b
    exact (hab hcomm).elim

theorem conj_injective_of_noncomm_simple (S : Type) [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, ¬ Commute a b) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [conj_ker_eq_center, simple_noncomm_center_eq_bot S hS]

theorem simple_noncomm_isPerfect (S : Type) [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, ¬ Commute a b) : Group.IsPerfect S := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator S) inferInstance with hcomm | hcomm
  · exfalso
    have hcenter : Subgroup.center S = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (G := S)).mp hcomm
    letI : CommGroup S := Group.commGroupOfCenterEqTop hcenter
    rcases hS with ⟨a, b, hab⟩
    exact hab (by
      change a * b = b * a
      exact mul_comm a b)
  · exact hcomm


end Submission
