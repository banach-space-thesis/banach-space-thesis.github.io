import ThesisCommon.Analysis.DualDirectSums
import ThesisCommon.Analysis.ScalarExtensionAbsorption

/-! Absorbing one scalar coordinate passes to the actual continuous dual. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Evaluation at one identifies the continuous dual of the scalar field. -/
def scalarDualEquiv : StrongDual 𝕜 𝕜 ≃L[𝕜] 𝕜 := by
  let A : StrongDual 𝕜 𝕜 →L[𝕜] 𝕜 := LinearMap.mkContinuous
    { toFun := fun φ => φ 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun φ => by simpa only [norm_one, mul_one, one_mul] using φ.le_opNorm 1)
  let B : 𝕜 →L[𝕜] StrongDual 𝕜 𝕜 := LinearMap.mkContinuous
    { toFun := fun c => c • ContinuousLinearMap.id 𝕜 𝕜
      map_add' := fun a b => by
        apply ContinuousLinearMap.ext
        intro z
        change (a + b) * z = a * z + b * z
        exact add_mul _ _ _
      map_smul' := fun a b => by
        apply ContinuousLinearMap.ext
        intro z
        change (a * b) * z = a * (b * z)
        exact mul_assoc _ _ _ }
    1 (fun c => by
      change ‖c • ContinuousLinearMap.id 𝕜 𝕜‖ ≤ 1 * ‖c‖
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
      intro z
      change ‖c * z‖ ≤ ‖c‖ * ‖z‖
      rw [norm_mul])
  refine ContinuousLinearEquiv.equivOfInverse A B ?_ ?_
  · intro φ
    apply ContinuousLinearMap.ext
    intro c
    change φ 1 * c = φ c
    calc
      φ 1 * c = c * φ 1 := mul_comm _ _
      _ = φ (c • (1 : 𝕜)) := (φ.map_smul c 1).symm
      _ = φ c := by rw [smul_eq_mul, mul_one]
  · intro c
    change c * 1 = c
    exact mul_one c

theorem IsIsomorphicToScalarExtension.dual (h : IsIsomorphicToScalarExtension 𝕜 X) :
    IsIsomorphicToScalarExtension 𝕜 (StrongDual 𝕜 X) := by
  obtain ⟨e⟩ := h
  exact ⟨(banachDualEquiv e).trans ((banachDualProductEquiv (𝕜 := 𝕜) (E := X) (F := 𝕜)).trans
    ((ContinuousLinearEquiv.refl 𝕜 (StrongDual 𝕜 X)).prodCongr scalarDualEquiv))⟩

end ThesisCommon
