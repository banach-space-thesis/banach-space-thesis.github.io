import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Tactic

/-! The positive-cone order on actual continuous real linear maps. The
instances are scoped, so unrelated orders on operators are unaffected. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E] [IsOrderedAddMonoid E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]

omit [PartialOrder F] [IsOrderedAddMonoid F] in
theorem continuousLinearMap_ext_of_nonneg (S T : E →L[ℝ] F)
    (h : ∀ x, 0 ≤ x → S x = T x) : S = T := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    S x = S x⁺ - S x⁻ := by rw [← map_sub, posPart_sub_negPart]
    _ = T x⁺ - T x⁻ := by rw [h _ (posPart_nonneg x), h _ (negPart_nonneg x)]
    _ = T x := by rw [← map_sub, posPart_sub_negPart]

namespace PositiveOperatorOrder
scoped instance partialOrder : PartialOrder (E →L[ℝ] F) where
  le S T := ∀ x, 0 ≤ x → S x ≤ T x
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ hST hTR x hx := (hST x hx).trans (hTR x hx)
  le_antisymm S T hST hTS := continuousLinearMap_ext_of_nonneg S T
    (fun x hx => le_antisymm (hST x hx) (hTS x hx))

scoped instance orderedAdd : IsOrderedAddMonoid (E →L[ℝ] F) where
  add_le_add_left _ _ h U x hx := add_le_add_left (h x hx) (U x)

scoped instance orderedModule [IsOrderedModule ℝ F] : IsOrderedModule ℝ (E →L[ℝ] F) :=
  IsOrderedModule.of_smul_nonneg fun _ hr _ hS x hx => smul_nonneg hr (hS x hx)
end PositiveOperatorOrder

open scoped PositiveOperatorOrder

omit [IsOrderedAddMonoid F] in
theorem operator_le_iff (S T : E →L[ℝ] F) : S ≤ T ↔ ∀ x, 0 ≤ x → S x ≤ T x := Iff.rfl

omit [IsOrderedAddMonoid F] in
theorem operator_nonneg_iff (S : E →L[ℝ] F) : 0 ≤ S ↔ ∀ x, 0 ≤ x → 0 ≤ S x := Iff.rfl

theorem positive_operator_monotone {S : E →L[ℝ] F} (hS : 0 ≤ S) : Monotone S := by
  intro x y hxy
  have h := hS (y - x) (sub_nonneg.mpr hxy)
  change 0 ≤ S (y - x) at h
  simpa only [map_sub, sub_nonneg] using h

end ThesisCommon
