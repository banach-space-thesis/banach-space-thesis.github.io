import ThesisCommon.Analysis.FilterFunctionalCharge
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Hahn–Banach extensions of the actual coordinate functionals of a bounded
operator on a filter-null space. Their indicator charges have the required
uniform total-variation bound. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 Γ : Type*} [RCLike 𝕜] (F : Filter Γ)

theorem filter_coordinate_extension_exists
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    ∃ φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜,
      ‖φ‖ ≤ ‖T‖ ∧ ∀ x : FilterNullSpace 𝕜 F, φ x.val = T x α := by
  let ψ := (filterCoordinate F α).comp T
  have hψ : ‖ψ‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    exact ((T x).norm_apply_le α).trans (T.le_opNorm x)
  obtain ⟨φ, hφ, hn⟩ := exists_extension_norm_eq (filterNullSubmodule 𝕜 F) ψ
  exact ⟨φ, hn.trans_le hψ, hφ⟩

def filterCoordinateExtension
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜 :=
  (filter_coordinate_extension_exists F T α).choose

theorem norm_filterCoordinateExtension_le
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    ‖filterCoordinateExtension F T α‖ ≤ ‖T‖ :=
  (filter_coordinate_extension_exists F T α).choose_spec.1

theorem filterCoordinateExtension_apply
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ)
    (x : FilterNullSpace 𝕜 F) : filterCoordinateExtension F T α x.val = T x α :=
  (filter_coordinate_extension_exists F T α).choose_spec.2 x

theorem filterCoordinateExtension_variation_le
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) (A : Set Γ) :
    (functionalCharge (filterCoordinateExtension F T α)).variation A ≤ ‖T‖ :=
  (functionalCharge_variation_le _ A).trans (norm_filterCoordinateExtension_le F T α)

theorem filterCoordinateExtension_uniformlyBounded
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) :
    BoundedScalarCharge.UniformlyBounded
      (fun α => functionalCharge (filterCoordinateExtension F T α)) :=
  ⟨‖T‖, fun α => filterCoordinateExtension_variation_le F T α Set.univ⟩

end ThesisCommon
