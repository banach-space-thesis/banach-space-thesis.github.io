import Posets.MainStatements
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Scalars are one-dimensional full operator algebras, with precisely
the scalar absolute-value norm required by Theorem 1.5. -/
noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def scalarOneDimensionalHom :
    BoundedHom 𝕜 𝕜 ((Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) where
  toContinuousLinearMap := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
    (ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜))
  map_mul' a b := by
    ext x i
    change (a * b) * x i = a * (b * x i)
    exact mul_assoc _ _ _

theorem scalarOneDimensionalHom_isometry :
    Isometry (scalarOneDimensionalHom (𝕜 := 𝕜)) := by
  apply AddMonoidHomClass.isometry_of_norm scalarOneDimensionalHom.toContinuousLinearMap
  intro a
  change ‖a • ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)‖ = ‖a‖
  simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one]

theorem scalarOneDimensionalHom_surjective :
    Function.Surjective (scalarOneDimensionalHom (𝕜 := 𝕜)) := by
  intro T
  refine ⟨T (fun _ => 1) 0, ?_⟩
  ext x i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change T (fun _ => 1) 0 * x 0 = T x 0
  have hx : x = x 0 • (fun _ : Fin 1 => (1 : 𝕜)) := by
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
  conv_rhs => rw [hx, map_smul]
  exact mul_comm _ _

theorem admissible_scalar : AdmissibleAlgebra 𝕜 𝕜 := by
  refine Or.inr (Or.inl ⟨0, scalarOneDimensionalHom, scalarOneDimensionalHom_isometry, ?_⟩)
  exact Set.range_eq_univ.mpr scalarOneDimensionalHom_surjective

end Posets
