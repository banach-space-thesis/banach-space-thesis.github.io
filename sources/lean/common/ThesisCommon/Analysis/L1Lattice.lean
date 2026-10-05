import ThesisCommon.Analysis.LpCodingOrder
import ThesisCommon.Analysis.RealALModel

/-! The genuine real L¹ space as a Banach lattice with its AL norm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X]

/-- Positive scalar multiplication for mathlib's actual order on real Lp. -/
instance realLp_orderedModule (μ : Measure X) (p : ℝ≥0∞) : IsOrderedModule ℝ (Lp ℝ p μ) :=
  IsOrderedModule.of_smul_nonneg fun r hr u hu => by
    apply (Lp.coeFn_nonneg (r • u)).mp
    filter_upwards [Lp.coeFn_smul r u, (Lp.coeFn_nonneg u).mpr hu] with x hx hux
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    rw [hx]
    exact mul_nonneg hr hux

def realL1BanachLattice (μ : Measure X) : RealBanachLattice where
  Carrier := Lp ℝ 1 μ
  lattice := inferInstance
  orderedAdd := inferInstance
  orderedModule := inferInstance
  solidNorm := inferInstance

theorem realL1BanachLattice_isAL (μ : Measure X) : (realL1BanachLattice μ).IsAL :=
  lOne_norm_add_of_nonneg μ

/-- The concrete L¹ lattice satisfies the intrinsic predicate used in the
paper's abstract AL-space targets. No measure representation is assumed. -/
theorem realL1_isALSpace (μ : Measure X) : IsALSpace ℝ (Lp ℝ 1 μ) :=
  isALSpace_of_real_lattice _ (lOne_norm_add_of_nonneg μ)

end ThesisCommon
