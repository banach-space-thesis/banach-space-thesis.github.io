import ThesisCommon.Analysis.DualLatticeModulus

/-! The actual lattice and solid operator norm on the continuous dual of a
real normed lattice. The order is the existing positive-cone order. -/
noncomputable section
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

def dualSup (φ ψ : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (φ + ψ + dualModulus (φ - ψ))

theorem le_dualSup_left (φ ψ : E →L[ℝ] ℝ) : φ ≤ dualSup φ ψ := by
  intro x hx
  have h := (le_abs_self ((φ - ψ) x)).trans (dualModulus_dominates (φ - ψ) x hx)
  change φ x - ψ x ≤ dualModulus (φ - ψ) x at h
  change φ x ≤ (1 / 2 : ℝ) * (φ x + ψ x + dualModulus (φ - ψ) x)
  linarith

theorem le_dualSup_right (φ ψ : E →L[ℝ] ℝ) : ψ ≤ dualSup φ ψ := by
  intro x hx
  have h := (neg_le_abs ((φ - ψ) x)).trans (dualModulus_dominates (φ - ψ) x hx)
  change -(φ x - ψ x) ≤ dualModulus (φ - ψ) x at h
  change ψ x ≤ (1 / 2 : ℝ) * (φ x + ψ x + dualModulus (φ - ψ) x)
  linarith

theorem dualSup_le (φ ψ R : E →L[ℝ] ℝ) (hφ : φ ≤ R) (hψ : ψ ≤ R) :
    dualSup φ ψ ≤ R := by
  have hbound : dualModulus (φ - ψ) ≤ (R - φ) + (R - ψ) := by
    apply dualModulus_least
    intro x hx
    change |φ x - ψ x| ≤ (R x - φ x) + (R x - ψ x)
    apply abs_le.mpr
    constructor <;> linarith [hφ x hx, hψ x hx]
  intro x hx
  have h := hbound x hx
  change dualModulus (φ - ψ) x ≤ (R x - φ x) + (R x - ψ x) at h
  change (1 / 2 : ℝ) * (φ x + ψ x + dualModulus (φ - ψ) x) ≤ R x
  linarith

theorem dualSup_neg (φ : E →L[ℝ] ℝ) : dualSup φ (-φ) = dualModulus φ := by
  apply le_antisymm
  · apply dualSup_le
    · intro x hx
      exact (le_abs_self _).trans (dualModulus_dominates φ x hx)
    · intro x hx
      exact (neg_le_abs _).trans (dualModulus_dominates φ x hx)
  · apply dualModulus_least
    intro x hx
    exact sup_le (le_dualSup_left φ (-φ) x hx) (le_dualSup_right φ (-φ) x hx)

namespace DualLattice
/-- Open `ThesisCommon.DualLattice` together with `PositiveOperatorOrder`
to use the genuine lattice on the continuous scalar dual. -/
scoped instance lattice : Lattice (E →L[ℝ] ℝ) where
  __ := PositiveOperatorOrder.partialOrder
  sup := dualSup
  le_sup_left := le_dualSup_left
  le_sup_right := le_dualSup_right
  sup_le := dualSup_le
  inf φ ψ := -dualSup (-φ) (-ψ)
  inf_le_left φ ψ := neg_le.mp (le_dualSup_left (-φ) (-ψ))
  inf_le_right φ ψ := neg_le.mp (le_dualSup_right (-φ) (-ψ))
  le_inf φ ψ R hφψ hφR := by
    apply le_neg.mpr
    exact dualSup_le (-ψ) (-R) (-φ) (neg_le_neg hφψ) (neg_le_neg hφR)
end DualLattice

open scoped DualLattice

theorem dual_abs_eq_modulus (φ : E →L[ℝ] ℝ) : |φ| = dualModulus φ := dualSup_neg φ

theorem norm_dual_abs (φ : E →L[ℝ] ℝ) : ‖|φ|‖ = ‖φ‖ := by
  rw [dual_abs_eq_modulus, norm_dualModulus]

theorem norm_positive_functional_mono {φ ψ : E →L[ℝ] ℝ}
    (hφ : 0 ≤ φ) (hφψ : φ ≤ ψ) : ‖φ‖ ≤ ‖ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
  intro x
  rw [Real.norm_eq_abs]
  calc
    |φ x| ≤ φ |x| := positive_functional_abs_apply_le hφ x
    _ ≤ ψ |x| := hφψ _ (abs_nonneg x)
    _ ≤ ‖ψ |x|‖ := le_abs_self _
    _ ≤ ‖ψ‖ * ‖|x|‖ := ψ.le_opNorm _
    _ = ‖ψ‖ * ‖x‖ := by rw [norm_abs_eq_norm]

namespace DualLattice
scoped instance solidNorm : HasSolidNorm (E →L[ℝ] ℝ) where
  solid φ ψ h := by
    rw [← norm_dual_abs φ, ← norm_dual_abs ψ]
    exact norm_positive_functional_mono (abs_nonneg φ) h
end DualLattice

end ThesisCommon
