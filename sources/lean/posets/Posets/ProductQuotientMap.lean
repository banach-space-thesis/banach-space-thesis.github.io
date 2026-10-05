import Posets.ProductQuotientDiagonal
import Posets.CountableSeparableBlocks

/-! The product quotient is read from the diagonal operator blocks. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
open scoped ENNReal
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜] {P : Type*}
  {X C : P → Type*}
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, NormedAddCommGroup (C p)] [∀ p, NormedSpace 𝕜 (C p)]
  (θ : ∀ p, (X p →L[𝕜] X p) →L[𝕜] C p)
  (hθ : ∀ p, ‖θ p‖ ≤ 1)

include hθ

theorem productQuotient_coord_bound
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (p : P) :
    ‖θ p (operatorBlock 𝕜 X X T p p)‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖θ p‖ * ‖operatorBlock 𝕜 X X T p p‖ := (θ p).le_opNorm _
    _ ≤ 1 * ‖operatorBlock 𝕜 X X T p p‖ :=
      mul_le_mul_of_nonneg_right (hθ p) (norm_nonneg _)
    _ ≤ ‖T‖ := by simpa using product_operatorBlock_norm_le T p p

/-- Linearity of the diagonal coordinate quotient. -/
def productQuotientLinearMap :
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) →ₗ[𝕜] lp C ∞ :=
  { toFun := fun T => ⟨fun p => θ p (operatorBlock 𝕜 X X T p p), memℓp_infty
       ⟨‖T‖, by rintro _ ⟨p, rfl⟩; exact productQuotient_coord_bound θ hθ T p⟩⟩
    map_add' := by
       intro S T
       apply lp.ext
       funext p
       change θ p (operatorBlock 𝕜 X X (S + T) p p) = _
       have heq : operatorBlock 𝕜 X X (S + T) p p =
           operatorBlock 𝕜 X X S p p + operatorBlock 𝕜 X X T p p := by
         ext x
         simp [operatorBlock]
       rw [heq, map_add]
       rfl
    map_smul' := by
       intro r T
       apply lp.ext
       funext p
       change θ p (operatorBlock 𝕜 X X (r • T) p p) = _
       have heq : operatorBlock 𝕜 X X (r • T) p p =
           r • operatorBlock 𝕜 X X T p p := by
         ext x
         simp [operatorBlock]
       rw [heq, map_smul]
       rfl }

/-- The diagonal coordinate quotients form a uniformly bounded family. -/
def productQuotientMap :
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) →L[𝕜] lp C ∞ := by
  refine LinearMap.mkContinuous (productQuotientLinearMap θ hθ) 1 ?_
  intro T
  simpa only [one_mul] using lp.norm_le_of_forall_le
    (f := productQuotientLinearMap θ hθ T) (norm_nonneg T) (productQuotient_coord_bound θ hθ T)

theorem productQuotientMap_apply
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (p : P) :
    productQuotientMap θ hθ T p = θ p (operatorBlock 𝕜 X X T p p) := rfl

theorem productQuotientMap_norm_le : ‖productQuotientMap θ hθ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa using lp.norm_le_of_forall_le (norm_nonneg T) (productQuotient_coord_bound θ hθ T)

theorem productQuotientMap_contracts
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    ‖productQuotientMap θ hθ T‖ ≤ ‖T‖ :=
  lp.norm_le_of_forall_le (norm_nonneg T) (productQuotient_coord_bound θ hθ T)

variable (ρ : ∀ p, C p →L[𝕜] (X p →L[𝕜] X p))
  (hρ : ∀ p a, ‖ρ p a‖ ≤ ‖a‖)

theorem productQuotientMap_rightInverse
    (hsection : ∀ p, Function.RightInverse (ρ p) (θ p)) :
    Function.RightInverse (productSectionMap ρ hρ) (productQuotientMap θ hθ) := by
  intro a
  apply lp.ext
  funext p
  rw [productQuotientMap_apply, productSectionMap_diagonal, hsection p]

theorem productSectionMap_norm
    (hsection : ∀ p, Function.RightInverse (ρ p) (θ p)) (a : lp C ∞) :
    ‖productSectionMap ρ hρ a‖ = ‖a‖ := by
  apply le_antisymm (productSectionValue_norm_le ρ hρ a)
  have hb := productQuotientMap_contracts θ hθ (productSectionMap ρ hρ a)
  rwa [productQuotientMap_rightInverse θ hθ ρ hρ hsection a] at hb

theorem productSectionMap_isometry
    (hsection : ∀ p, Function.RightInverse (ρ p) (θ p)) :
    Isometry (productSectionMap ρ hρ) :=
  AddMonoidHomClass.isometry_of_norm (productSectionMap ρ hρ)
    (productSectionMap_norm θ hθ ρ hρ hsection)

omit ρ hρ in
theorem productQuotientMap_eq_zero_iff [Countable P]
    (hker : ∀ p T, θ p T = 0 ↔ HasSeparableRange 𝕜 (X p) (X p) T)
    (hoff : ∀ s t, s ≠ t → ∀ T : X t →L[𝕜] X s, HasSeparableRange 𝕜 (X t) (X s) T)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    productQuotientMap θ hθ T = 0 ↔
      HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 X) (DependentCZeroSum 𝕜 X) T := by
  rw [countable_blocks_separable_iff X X T]
  constructor
  · intro h s t
    by_cases hst : s = t
    · subst t
      apply (hker s _).mp
      exact congrArg (fun a : lp C ∞ => a s) h
    · exact hoff s t hst _
  · intro h
    apply lp.ext
    funext p
    exact (hker p _).mpr (h p p)

end Posets
