import ThesisCommon.Analysis.BooleanContentExtension
import ThesisCommon.Analysis.ALFragmentMetric

/-! Strict Boolean contents obtained from genuine AL fragment norms.
Content-preserving Boolean isomorphisms preserve the actual norm metric,
because symmetric-difference content equals distance. -/
noncomputable section
open Set
open scoped symmDiff
namespace ThesisCommon

namespace StrictBooleanContent
variable {B : Type*} [BooleanAlgebra B]

def scale (w : StrictBooleanContent B) (c : ℝ) (hc : 0 < c) : StrictBooleanContent B where
  toFun a := c * w a
  nonneg a := mul_nonneg hc.le (w.nonneg a)
  eq_zero_iff a := by rw [mul_eq_zero, or_iff_right hc.ne', w.eq_zero_iff]
  add_disjoint a b hab := by rw [w.add_disjoint a b hab, mul_add]

theorem scale_apply (w : StrictBooleanContent B) (c : ℝ) (hc : 0 < c) (a : B) :
    w.scale c hc a = c * w a := rfl

def restrict (w : StrictBooleanContent B) (S : BooleanSubalgebra B) : StrictBooleanContent S where
  toFun a := w a.val
  nonneg a := w.nonneg a.val
  eq_zero_iff a := by
    rw [w.eq_zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  add_disjoint a b hab := by
    apply w.add_disjoint
    apply disjoint_iff.mpr
    exact congrArg Subtype.val hab.eq_bot

theorem restrict_apply (w : StrictBooleanContent B) (S : BooleanSubalgebra B) (a : S) :
    w.restrict S a = w a.val := rfl

end StrictBooleanContent

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

def alFragmentStrictContent : StrictBooleanContent (PositiveFragmentAlgebra e) where
  toFun a := ‖positiveFragmentValue a‖
  nonneg a := norm_nonneg _
  eq_zero_iff a := by
    rw [norm_eq_zero]
    exact ⟨fun h => positiveFragmentValue_injective e
      (h.trans (positiveFragmentValue_bot e).symm),
      fun h => h ▸ positiveFragmentValue_bot e⟩
  add_disjoint a b hab := by
    rw [positiveFragmentValue_sup_of_disjoint a b hab]
    exact hE _ _ (positiveFragmentValue_nonneg a) (positiveFragmentValue_nonneg b)

theorem alFragmentStrictContent_apply (a : PositiveFragmentAlgebra e) :
    alFragmentStrictContent hE e a = ‖positiveFragmentValue a‖ := rfl

theorem alFragmentStrictContent_top :
    alFragmentStrictContent hE e ⊤ = ‖e‖ := rfl

variable [HasSolidNorm E]

theorem alFragmentStrictContent_symmDiff (a b : PositiveFragmentAlgebra e) :
    alFragmentStrictContent hE e (a ∆ b) = dist a b := by
  rw [alFragmentStrictContent_apply, positiveFragmentValue_symmDiff, norm_abs_eq_norm]
  exact (dist_eq_norm (positiveFragmentValue a) (positiveFragmentValue b)).symm

variable {F : Type*} [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [HasSolidNorm F]
variable (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (f : F) [Fact (0 ≤ f)]

theorem isometry_of_preserves_alFragmentStrictContent
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f)) (φ : S ≃o T)
    (hφ : ∀ a : S, alFragmentStrictContent hF f (φ a).val = alFragmentStrictContent hE e a.val) :
    Isometry φ := by
  apply Isometry.of_dist_eq
  intro a b
  change dist (φ a).val (φ b).val = dist a.val b.val
  rw [← alFragmentStrictContent_symmDiff hF f, ← alFragmentStrictContent_symmDiff hE e]
  have h := hφ (a ∆ b)
  simpa only [symmDiff_def, map_sup, map_sdiff', BooleanSubalgebra.val_sup,
    BooleanSubalgebra.val_sdiff] using h

def alFragmentContentIsometryEquiv
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (T : BooleanSubalgebra (PositiveFragmentAlgebra f)) (φ : S ≃o T)
    (hφ : ∀ a : S, alFragmentStrictContent hF f (φ a).val = alFragmentStrictContent hE e a.val) :
    S ≃ᵢ T where
  toEquiv := φ.toEquiv
  isometry_toFun := isometry_of_preserves_alFragmentStrictContent hE e hF f S T φ hφ

end ThesisCommon
