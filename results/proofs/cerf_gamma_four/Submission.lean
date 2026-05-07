import Mathlib
import Submission.Helpers

import Challenge
open scoped Manifold ContDiff
open Metric (sphere)

namespace Submission

abbrev cerf_gamma_four_S3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

noncomputable abbrev cerf_gamma_four_model3 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))

noncomputable abbrev cerf_gamma_four_modelI1x3 :=
  (modelWithCornersEuclideanHalfSpace 1).prod
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))

abbrev cerf_gamma_four_smooth_index : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem cerf_gamma_four (f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯
         sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ∃ (A : Matrix.orthogonalGroup (Fin 4) ℝ)
      (F F' : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
              sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 3) ∞ F ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 3) ∞ F' ∧
      (∀ t p, F  (t, F' (t, p)) = p) ∧
      (∀ t p, F' (t, F  (t, p)) = p) ∧
      (∀ p, F (0, p) = f p) ∧
      (∀ p, (F (1, p) : EuclideanSpace ℝ (Fin 4)) =
            Matrix.UnitaryGroup.toLinearEquiv A
              (p : EuclideanSpace ℝ (Fin 4))) := by
  simpa [cerf_gamma_four_S3, cerf_gamma_four_model3, cerf_gamma_four_modelI1x3,
    cerf_gamma_four_smooth_index] using (_root_.cerf_gamma_four f)


end Submission
