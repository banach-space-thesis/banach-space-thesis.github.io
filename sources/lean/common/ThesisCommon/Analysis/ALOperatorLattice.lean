import ThesisCommon.Analysis.PositiveOperatorOrder
import ThesisCommon.Analysis.OperatorModulus

/-! The lattice of bounded real operators between AL lattices, constructed
from the proved modulus. No operator supremum is assumed. -/
noncomputable section
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] [HasSolidNorm F]
variable [CompleteSpace F] [OrderClosedTopology F]
variable (hALE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
variable (hALF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)

def alOperatorSup (S T : E →L[ℝ] F) : E →L[ℝ] F :=
  (1 / 2 : ℝ) • (S + T + operatorModulus hALE hALF (S - T))

theorem le_alOperatorSup_left (S T : E →L[ℝ] F) : S ≤ alOperatorSup hALE hALF S T := by
  intro x hx
  have h := (le_abs_self ((S - T) x)).trans (operatorModulus_dominates hALE hALF (S - T) x hx)
  apply sub_nonneg.mp
  have heq : alOperatorSup hALE hALF S T x - S x =
      (1 / 2 : ℝ) • (operatorModulus hALE hALF (S - T) x - (S - T) x) := by
    simp only [alOperatorSup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    module
  rw [heq]
  exact smul_nonneg (by norm_num) (sub_nonneg.mpr h)

theorem le_alOperatorSup_right (S T : E →L[ℝ] F) : T ≤ alOperatorSup hALE hALF S T := by
  intro x hx
  have h := (neg_le_abs ((S - T) x)).trans (operatorModulus_dominates hALE hALF (S - T) x hx)
  apply sub_nonneg.mp
  have heq : alOperatorSup hALE hALF S T x - T x =
      (1 / 2 : ℝ) • (operatorModulus hALE hALF (S - T) x + (S - T) x) := by
    simp only [alOperatorSup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    module
  rw [heq]
  exact smul_nonneg (by norm_num) (neg_le_iff_add_nonneg.mp h)

theorem alOperatorSup_le (S T R : E →L[ℝ] F) (hS : S ≤ R) (hT : T ≤ R) :
    alOperatorSup hALE hALF S T ≤ R := by
  have hbound : operatorModulus hALE hALF (S - T) ≤ (R - S) + (R - T) := by
    apply operatorModulus_least
    intro x hx
    change |S x - T x| ≤ (R x - S x) + (R x - T x)
    rw [abs]
    apply sup_le
    · exact (sub_le_sub_right (hS x hx) _).trans
        (le_add_of_nonneg_left (sub_nonneg.mpr (hS x hx)))
    · rw [neg_sub]
      exact (sub_le_sub_right (hT x hx) _).trans
        (le_add_of_nonneg_right (sub_nonneg.mpr (hT x hx)))
  intro x hx
  apply sub_nonneg.mp
  have heq : R x - alOperatorSup hALE hALF S T x =
      (1 / 2 : ℝ) • (((R - S) + (R - T)) x - operatorModulus hALE hALF (S - T) x) := by
    simp only [alOperatorSup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    module
  rw [heq]
  exact smul_nonneg (by norm_num) (sub_nonneg.mpr (hbound x hx))

theorem alOperatorSup_neg (T : E →L[ℝ] F) :
    alOperatorSup hALE hALF T (-T) = operatorModulus hALE hALF T := by
  apply le_antisymm
  · apply alOperatorSup_le hALE hALF
    · intro x hx
      exact (le_abs_self _).trans (operatorModulus_dominates hALE hALF T x hx)
    · intro x hx
      exact (neg_le_abs _).trans (operatorModulus_dominates hALE hALF T x hx)
  · intro x hx
    apply operatorModulus_least hALE hALF T (alOperatorSup hALE hALF T (-T)) ?_ x hx
    intro y hy
    exact sup_le (le_alOperatorSup_left hALE hALF T (-T) y hy)
      (le_alOperatorSup_right hALE hALF T (-T) y hy)

def alOperatorLattice : Lattice (E →L[ℝ] F) where
  __ := PositiveOperatorOrder.partialOrder
  sup := alOperatorSup hALE hALF
  le_sup_left := le_alOperatorSup_left hALE hALF
  le_sup_right := le_alOperatorSup_right hALE hALF
  sup_le := alOperatorSup_le hALE hALF
  inf S T := -alOperatorSup hALE hALF (-S) (-T)
  inf_le_left S T := neg_le.mp (le_alOperatorSup_left hALE hALF (-S) (-T))
  inf_le_right S T := neg_le.mp (le_alOperatorSup_right hALE hALF (-S) (-T))
  le_inf S T R hST hSR := by
    apply le_neg.mpr
    exact alOperatorSup_le hALE hALF (-T) (-R) (-S) (neg_le_neg hST) (neg_le_neg hSR)

end ThesisCommon
