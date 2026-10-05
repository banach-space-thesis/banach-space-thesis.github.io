import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! A norm-bounded additive map on the positive cone extends to an actual
continuous real linear map. This is used for operator suprema and projections. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (P : (x : E) → 0 ≤ x → F)
variable (hadd : ∀ x y hx hy, P (x + y) (add_nonneg hx hy) = P x hx + P y hy)

def positiveConeExtensionFn (x : E) : F := P x⁺ (posPart_nonneg x) - P x⁻ (negPart_nonneg x)

include hadd in
omit [NormedSpace ℝ E] [HasSolidNorm E] [NormedSpace ℝ F] in
theorem positiveConeMap_zero : P 0 le_rfl = 0 := by
  have h := hadd 0 0 le_rfl le_rfl
  simp only [zero_add] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

include hadd in
omit [NormedSpace ℝ E] [HasSolidNorm E] [NormedSpace ℝ F] in
theorem positiveConeExtensionFn_sub (a b : E) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    positiveConeExtensionFn P (a - b) = P a ha - P b hb := by
  have heq : (a - b)⁺ + b = a + (a - b)⁻ :=
    sub_eq_sub_iff_add_eq_add.mp (posPart_sub_negPart (a - b))
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← hadd _ _ (posPart_nonneg _) hb, ← hadd _ _ ha (negPart_nonneg _)]
  have heq' : (⟨(a - b)⁺ + b, add_nonneg (posPart_nonneg _) hb⟩ : {x : E // 0 ≤ x}) =
      ⟨a + (a - b)⁻, add_nonneg ha (negPart_nonneg _)⟩ := Subtype.ext heq
  exact congrArg (fun q : {x : E // 0 ≤ x} => P q.1 q.2) heq'

include hadd in
omit [NormedSpace ℝ E] [HasSolidNorm E] [NormedSpace ℝ F] in
theorem positiveConeExtensionFn_add (x y : E) :
    positiveConeExtensionFn P (x + y) = positiveConeExtensionFn P x + positiveConeExtensionFn P y := by
  have heq : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    calc
      x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
  rw [heq, positiveConeExtensionFn_sub P hadd _ _
    (add_nonneg (posPart_nonneg _) (posPart_nonneg _))
    (add_nonneg (negPart_nonneg _) (negPart_nonneg _)),
    hadd _ _ (posPart_nonneg x) (posPart_nonneg y),
    hadd _ _ (negPart_nonneg x) (negPart_nonneg y)]
  dsimp [positiveConeExtensionFn]
  abel

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem norm_positiveConeExtensionFn_le {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x hx, ‖P x hx‖ ≤ C * ‖x‖) (x : E) :
    ‖positiveConeExtensionFn P x‖ ≤ (2 * C) * ‖x‖ := by
  have hp : ‖x⁺‖ ≤ ‖x‖ := by simpa only [posPart_def, norm_zero, add_zero] using norm_sup_le_add x 0
  have hn : ‖x⁻‖ ≤ ‖x‖ := by simpa only [negPart_def, norm_zero, add_zero, norm_neg] using norm_sup_le_add (-x) 0
  calc
    ‖positiveConeExtensionFn P x‖ ≤ ‖P x⁺ (posPart_nonneg x)‖ + ‖P x⁻ (negPart_nonneg x)‖ := norm_sub_le _ _
    _ ≤ C * ‖x⁺‖ + C * ‖x⁻‖ := add_le_add (hbound _ _) (hbound _ _)
    _ ≤ C * ‖x‖ + C * ‖x‖ := add_le_add (mul_le_mul_of_nonneg_left hp hC) (mul_le_mul_of_nonneg_left hn hC)
    _ = (2 * C) * ‖x‖ := by ring

def positiveConeExtension {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x hx, ‖P x hx‖ ≤ C * ‖x‖) :
    E →L[ℝ] F :=
  let A : E →+ F :=
    { toFun := positiveConeExtensionFn P
      map_zero' := by simp [positiveConeExtensionFn]
      map_add' := positiveConeExtensionFn_add P hadd }
  A.toRealLinearMap (AddMonoidHomClass.continuous_of_bound A (2 * C)
    (norm_positiveConeExtensionFn_le P hC hbound))

theorem positiveConeExtension_apply_of_nonneg {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x hx, ‖P x hx‖ ≤ C * ‖x‖) (x : E) (hx : 0 ≤ x) :
    positiveConeExtension P hadd hC hbound x = P x hx := by
  change positiveConeExtensionFn P x = P x hx
  have h := positiveConeExtensionFn_sub P hadd x 0 hx le_rfl
  simpa only [sub_zero, positiveConeMap_zero P hadd] using h

end ThesisCommon
