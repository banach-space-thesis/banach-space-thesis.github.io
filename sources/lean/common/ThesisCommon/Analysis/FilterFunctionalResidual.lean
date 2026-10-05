import ThesisCommon.Analysis.FilterFunctionalExtension
import ThesisCommon.Analysis.FilterFunctionalSupport
import ThesisCommon.Analysis.SequenceCoordinates

/-! Removing the diagonal atom at the level of actual bounded functionals.
The resulting constructed charges have zero diagonal atom, a uniform norm
bound, and the genuine support estimate needed in the filter criterion. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ : Type*} [RCLike 𝕜]

theorem functionalCharge_apply_norm_le
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (A : Set Γ) :
    ‖functionalCharge φ A‖ ≤ ‖φ‖ := by
  exact (φ.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_infinityIndicator_le (𝕜 := 𝕜) A)
      (norm_nonneg φ)).trans_eq (mul_one _))

def functionalResidual (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ) :
    lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜 :=
  φ - φ (infinityIndicator {α}) • lpCoordinate (𝕜 := 𝕜) ∞ α

@[simp] theorem functionalResidual_apply
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ)
    (x : lp (fun _ : Γ => 𝕜) ∞) :
    functionalResidual φ α x = φ x - φ (infinityIndicator {α}) * x α := rfl

theorem norm_functionalResidual_le
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ) :
    ‖functionalResidual φ α‖ ≤ 2 * ‖φ‖ := by
  have hc : ‖φ (infinityIndicator {α})‖ ≤ ‖φ‖ := by
    exact (φ.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (norm_infinityIndicator_le (𝕜 := 𝕜) {α})
        (norm_nonneg φ)).trans_eq (mul_one _))
  have hcoord := norm_lpCoordinate_le (𝕜 := 𝕜) (X := 𝕜) (ι := Γ) ∞ α
  calc
    _ ≤ ‖φ‖ + ‖φ (infinityIndicator {α}) • lpCoordinate (𝕜 := 𝕜) ∞ α‖ := norm_sub_le _ _
    _ = ‖φ‖ + ‖φ (infinityIndicator {α})‖ * ‖lpCoordinate (𝕜 := 𝕜) (X := 𝕜) ∞ α‖ := by
      rw [norm_smul]
    _ ≤ ‖φ‖ + ‖φ‖ * 1 := add_le_add_left
      (mul_le_mul hc hcoord (norm_nonneg _) (norm_nonneg φ)) _
    _ = _ := by ring

theorem functionalResidual_diagonal_zero
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ) :
    functionalCharge (functionalResidual φ α) {α} = 0 := by
  rw [functionalCharge_apply, functionalResidual_apply, infinityIndicator_apply]
  simp

/-- The exact source formula λ(A) − λ({α})δα(A), including arbitrary A. -/
theorem functionalResidual_charge_apply
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ) (A : Set Γ) :
    functionalCharge (functionalResidual φ α) A =
      functionalCharge φ A - functionalCharge φ {α} * (if α ∈ A then 1 else 0) := by
  rw [functionalCharge_apply, functionalResidual_apply, infinityIndicator_apply]
  rfl

theorem functionalResidual_variation_le
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ) (A : Set Γ) :
    (functionalCharge (functionalResidual φ α)).variation A ≤ 2 * ‖φ‖ :=
  (functionalCharge_variation_le _ A).trans (norm_functionalResidual_le φ α)

theorem functionalResidual_support_bound
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜) (α : Γ)
    (x : lp (fun _ : Γ => 𝕜) ∞) {A : Set Γ} (hsupp : ∀ γ ∉ A, x γ = 0) :
    ‖φ x - functionalCharge φ {α} * x α‖ ≤
      (functionalCharge (functionalResidual φ α)).variation A * ‖x‖ :=
  functionalCharge_support_bound (functionalResidual φ α) x hsupp

variable (F : Filter Γ)

theorem filterCoordinateExtension_indicator_norm_le
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) (A : Set Γ) :
    ‖functionalCharge (filterCoordinateExtension F T α) A‖ ≤ ‖T‖ :=
  (functionalCharge_apply_norm_le _ A).trans (norm_filterCoordinateExtension_le F T α)

def filterCoordinateResidual
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜 := functionalResidual (filterCoordinateExtension F T α) α

theorem filterCoordinateResidual_apply
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ)
    (x : FilterNullSpace 𝕜 F) :
    filterCoordinateResidual F T α x.val = T x α -
      functionalCharge (filterCoordinateExtension F T α) {α} * x α := by
  change functionalResidual (filterCoordinateExtension F T α) α x.val = _
  rw [functionalResidual_apply, filterCoordinateExtension_apply]
  rfl

theorem filterCoordinateResidual_diagonal_zero
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    functionalCharge (filterCoordinateResidual F T α) {α} = 0 :=
  functionalResidual_diagonal_zero _ α

theorem filterCoordinateResidual_uniformlyBounded
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) :
    BoundedScalarCharge.UniformlyBounded
      (fun α => functionalCharge (filterCoordinateResidual F T α)) := by
  refine ⟨2 * ‖T‖, fun α => ?_⟩
  exact (functionalResidual_variation_le (filterCoordinateExtension F T α) α Set.univ).trans
    (mul_le_mul_of_nonneg_left (norm_filterCoordinateExtension_le F T α) (by norm_num))

theorem filterCoordinateResidual_support_bound
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ)
    (x : FilterNullSpace 𝕜 F) {A : Set Γ} (hsupp : ∀ γ ∉ A, x γ = 0) :
    ‖T x α - functionalCharge (filterCoordinateExtension F T α) {α} * x α‖ ≤
      (functionalCharge (filterCoordinateResidual F T α)).variation A * ‖x‖ := by
  have h := functionalCharge_support_bound (filterCoordinateResidual F T α) x.val hsupp
  rw [filterCoordinateResidual_apply] at h
  exact h

end ThesisCommon
