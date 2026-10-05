import Posets.ProductQuotientMap
import PosetsCommon.MultiplicativeSection
import PosetsCommon.SeparableOperatorIdeal

/-! The generic product strong-splitting construction used in Theorem 1.5. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
open ThesisCommon
open scoped ENNReal
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜] {P : Type*}
  {X C : P → Type*}
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, NormedRing (C p)] [∀ p, NormedAlgebra 𝕜 (C p)]

section Section
variable (ρ : ∀ p, BoundedHom 𝕜 (C p) (X p →L[𝕜] X p))
  (hρ : ∀ p a, ‖ρ p a‖ ≤ ‖a‖)

theorem productSectionMap_mul (a b : lp C ∞) :
    productSectionMap (fun p => (ρ p).toContinuousLinearMap) hρ (a * b) =
      productSectionMap (fun p => (ρ p).toContinuousLinearMap) hρ a *
        productSectionMap (fun p => (ρ p).toContinuousLinearMap) hρ b := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext p
  change ρ p (a p * b p) (x.val p) = ρ p (a p) (ρ p (b p) (x.val p))
  rw [(ρ p).map_mul']
  rfl

/-- The product section is a bounded algebra homomorphism. -/
def productDiagonalHom : BoundedHom 𝕜 (lp C ∞)
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) where
  toContinuousLinearMap := productSectionMap (fun p => (ρ p).toContinuousLinearMap) hρ
  map_mul' := productSectionMap_mul ρ hρ

end Section

section Quotient
variable [Countable P]
  (θ : ∀ p, BoundedHom 𝕜 (X p →L[𝕜] X p) (C p))
  (ρ : ∀ p, BoundedHom 𝕜 (C p) (X p →L[𝕜] X p))
  (hθ : ∀ p, ‖(θ p).toContinuousLinearMap‖ ≤ 1)
  (hρ : ∀ p a, ‖ρ p a‖ ≤ ‖a‖)
  (hsplit : ∀ p, StrongSplit 𝕜 (X p) (C p) (θ p) (ρ p))
  (hoff : ∀ s t, s ≠ t → ∀ T : X t →L[𝕜] X s, HasSeparableRange 𝕜 (X t) (X s) T)

include hρ hsplit hoff in
theorem productQuotientMap_mul
    (S T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    productQuotientMap (fun p => (θ p).toContinuousLinearMap) hθ (S * T) =
      productQuotientMap (fun p => (θ p).toContinuousLinearMap) hθ S *
        productQuotientMap (fun p => (θ p).toContinuousLinearMap) hθ T := by
  apply multiplicative_of_section
    (productQuotientMap (fun p => (θ p).toContinuousLinearMap) hθ).toLinearMap
    (separableOperatorIdeal 𝕜 (DependentCZeroSum 𝕜 X))
    (fun U => (productQuotientMap_eq_zero_iff
      (fun p => (θ p).toContinuousLinearMap) hθ (fun p => (hsplit p).2.1) hoff U).trans
        (mem_separableOperatorIdeal _ _ U).symm)
    (productSectionMap (fun p => (ρ p).toContinuousLinearMap) hρ)
    (productSectionMap_mul ρ hρ)
    (productQuotientMap_rightInverse (fun p => (θ p).toContinuousLinearMap) hθ
      (fun p => (ρ p).toContinuousLinearMap) hρ (fun p => (hsplit p).2.2))

/-- The quotient homomorphism is the diagonal block map. Multiplicativity follows
from the separable-range kernel and the multiplicative diagonal section. -/
def productQuotientHom : BoundedHom 𝕜
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (lp C ∞) where
  toContinuousLinearMap := productQuotientMap (fun p => (θ p).toContinuousLinearMap) hθ
  map_mul' := productQuotientMap_mul θ ρ hθ hρ hsplit hoff

theorem productQuotientHom_apply
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (p : P) :
    productQuotientHom θ ρ hθ hρ hsplit hoff T p = θ p (operatorBlock 𝕜 X X T p p) := rfl

theorem product_strongSplit :
    StrongSplit 𝕜 (DependentCZeroSum 𝕜 X) (lp C ∞)
      (productQuotientHom θ ρ hθ hρ hsplit hoff) (productDiagonalHom ρ hρ) := by
  have hr : Function.RightInverse (productDiagonalHom ρ hρ)
      (productQuotientHom θ ρ hθ hρ hsplit hoff) :=
    productQuotientMap_rightInverse (fun p => (θ p).toContinuousLinearMap) hθ
      (fun p => (ρ p).toContinuousLinearMap) hρ (fun p => (hsplit p).2.2)
  exact ⟨hr.surjective, productQuotientMap_eq_zero_iff
    (fun p => (θ p).toContinuousLinearMap) hθ (fun p => (hsplit p).2.1) hoff, hr⟩

include hθ hsplit in
theorem productDiagonalHom_isometry : Isometry (productDiagonalHom ρ hρ) :=
  productSectionMap_isometry (fun p => (θ p).toContinuousLinearMap) hθ
    (fun p => (ρ p).toContinuousLinearMap) hρ (fun p => (hsplit p).2.2)

theorem productQuotientHom_norm_le :
    ‖(productQuotientHom θ ρ hθ hρ hsplit hoff).toContinuousLinearMap‖ ≤ 1 :=
  productQuotientMap_norm_le (fun p => (θ p).toContinuousLinearMap) hθ

theorem productQuotientHom_norm_eq_one [Nontrivial (lp C ∞)] :
    ‖(productQuotientHom θ ρ hθ hρ hsplit hoff).toContinuousLinearMap‖ = 1 := by
  apply le_antisymm (productQuotientHom_norm_le θ ρ hθ hρ hsplit hoff)
  obtain ⟨a, ha⟩ := exists_ne (0 : lp C ∞)
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb := (productQuotientHom θ ρ hθ hρ hsplit hoff).toContinuousLinearMap.le_opNorm
    (productDiagonalHom ρ hρ a)
  have hr := (product_strongSplit θ ρ hθ hρ hsplit hoff).2.2 a
  have hn := productSectionMap_norm (fun p => (θ p).toContinuousLinearMap) hθ
    (fun p => (ρ p).toContinuousLinearMap) hρ (fun p => (hsplit p).2.2) a
  change ‖productDiagonalHom ρ hρ a‖ = ‖a‖ at hn
  change ‖productQuotientHom θ ρ hθ hρ hsplit hoff (productDiagonalHom ρ hρ a)‖ ≤ _ at hb
  rw [hr, hn] at hb
  exact (mul_le_mul_right ha').mp (by simpa using hb)

end Quotient

/-- Countable product assembly, independent of the poset-family construction.
The hypotheses allow zero coordinates and the empty index type. -/
theorem exists_product_strongSplit [Countable P]
    (θ : ∀ p, BoundedHom 𝕜 (X p →L[𝕜] X p) (C p))
    (ρ : ∀ p, BoundedHom 𝕜 (C p) (X p →L[𝕜] X p))
    (hsplit : ∀ p, StrongSplit 𝕜 (X p) (C p) (θ p) (ρ p))
    (hθ : ∀ p, ‖(θ p).toContinuousLinearMap‖ ≤ 1)
    (hρ : ∀ p, Isometry (ρ p))
    (hoff : ∀ s t, s ≠ t → ∀ T : X t →L[𝕜] X s, HasSeparableRange 𝕜 (X t) (X s) T) :
    ∃ Θ : BoundedHom 𝕜 (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (lp C ∞),
    ∃ R : BoundedHom 𝕜 (lp C ∞) (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 X) (lp C ∞) Θ R ∧ Isometry R ∧
        ‖Θ.toContinuousLinearMap‖ ≤ 1 ∧
        (Nontrivial (lp C ∞) → ‖Θ.toContinuousLinearMap‖ = 1) := by
  have hρ' : ∀ p a, ‖ρ p a‖ ≤ ‖a‖ := fun p a => le_of_eq
    ((AddMonoidHomClass.isometry_iff_norm (ρ p).toContinuousLinearMap).mp (hρ p) a)
  refine ⟨productQuotientHom θ ρ hθ hρ' hsplit hoff, productDiagonalHom ρ hρ',
    product_strongSplit θ ρ hθ hρ' hsplit hoff,
    productDiagonalHom_isometry θ ρ hθ hρ' hsplit,
    productQuotientHom_norm_le θ ρ hθ hρ' hsplit hoff, ?_⟩
  intro hnontrivial
  letI := hnontrivial
  exact productQuotientHom_norm_eq_one θ ρ hθ hρ' hsplit hoff

end Posets
