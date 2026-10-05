import ThesisCommon.Analysis.ALFragmentScaling
import ThesisCommon.Analysis.OrderIsoDensity
import ThesisCommon.Analysis.PrincipalBandScaling

/-! Actual norm-one positive generators and the induced fragment geometry.
Normalization preserves the principal band and density homogeneity. -/
noncomputable section
open Set
namespace ThesisCommon

section NormalizedVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedPositiveVector (e : E) : E := ‖e‖⁻¹ • e

theorem norm_normalizedPositiveVector (e : E) (he : e ≠ 0) :
    ‖normalizedPositiveVector e‖ = 1 := by
  rw [normalizedPositiveVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)]

variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

theorem normalizedPositiveVector_nonneg {e : E} (he : 0 ≤ e) :
    0 ≤ normalizedPositiveVector e := smul_nonneg (inv_nonneg.mpr (norm_nonneg e)) he

instance normalizedPositiveVectorNonneg (e : E) [Fact (0 ≤ e)] :
    Fact (0 ≤ normalizedPositiveVector e) := ⟨normalizedPositiveVector_nonneg Fact.out⟩

variable (e : E) [Fact (0 ≤ e)]

def positiveFragmentNormalizeOrderIso (he : e ≠ 0) :
    PositiveFragmentAlgebra e ≃o PositiveFragmentAlgebra (normalizedPositiveVector e) := by
  letI : Fact (0 ≤ ‖e‖⁻¹ • e) := normalizedPositiveVectorNonneg e
  exact positiveFragmentSmulOrderIso e ‖e‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr he))

theorem positiveFragmentValue_normalizeOrderIso (he : e ≠ 0) (a : PositiveFragmentAlgebra e) :
    positiveFragmentValue (positiveFragmentNormalizeOrderIso e he a) =
      ‖e‖⁻¹ • positiveFragmentValue a := rfl

theorem norm_positiveFragmentNormalizeOrderIso (he : e ≠ 0) (a : PositiveFragmentAlgebra e) :
    ‖positiveFragmentValue (positiveFragmentNormalizeOrderIso e he a)‖ =
      ‖positiveFragmentValue a‖ / ‖e‖ := by
  rw [positiveFragmentValue_normalizeOrderIso, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e)), div_eq_mul_inv, mul_comm]

theorem topologicalDensity_positiveFragment_normalized (he : e ≠ 0) :
    topologicalDensity (PositiveFragmentAlgebra (normalizedPositiveVector e)) =
      topologicalDensity (PositiveFragmentAlgebra e) := by
  letI : Fact (0 ≤ ‖e‖⁻¹ • e) := normalizedPositiveVectorNonneg e
  exact topologicalDensity_positiveFragment_smul e ‖e‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr he))

variable [HasSolidNorm E]

theorem principalDensity_positiveFragmentSmulOrderIso (c : ℝ) (hc : 0 < c)
    [Fact (0 ≤ c • e)] (a : PositiveFragmentAlgebra e) :
    principalDensity (positiveFragmentSmulOrderIso e c hc a) = principalDensity a :=
  principalDensity_orderIso (positiveFragmentSmulOrderIso e c hc)
    (continuous_positiveFragmentSmulOrderIso e c hc)
    (continuous_positiveFragmentSmulOrderIso_symm e c hc) a

theorem isDensityHomogeneous_positiveFragmentSmulOrderIso_iff (c : ℝ) (hc : 0 < c)
    [Fact (0 ≤ c • e)] (a : PositiveFragmentAlgebra e) :
    IsDensityHomogeneous (positiveFragmentSmulOrderIso e c hc a) ↔ IsDensityHomogeneous a :=
  isDensityHomogeneous_orderIso_iff (positiveFragmentSmulOrderIso e c hc)
    (continuous_positiveFragmentSmulOrderIso e c hc)
    (continuous_positiveFragmentSmulOrderIso_symm e c hc) a

theorem isDensityHomogeneous_positiveFragment_normalized_iff (he : e ≠ 0)
    (a : PositiveFragmentAlgebra e) :
    IsDensityHomogeneous (positiveFragmentNormalizeOrderIso e he a) ↔ IsDensityHomogeneous a := by
  letI : Fact (0 ≤ ‖e‖⁻¹ • e) := normalizedPositiveVectorNonneg e
  exact isDensityHomogeneous_positiveFragmentSmulOrderIso_iff e ‖e‖⁻¹
    (inv_pos.mpr (norm_pos_iff.mpr he)) a

theorem isDensityHomogeneous_top_normalized_iff (he : e ≠ 0) :
    IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra (normalizedPositiveVector e)) ↔
      IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra e) := by
  simpa only [map_top] using isDensityHomogeneous_positiveFragment_normalized_iff e he ⊤

end NormalizedVector

section PrincipalBand
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem principalBand_normalizedPositiveVector (e : E) (he : e ≠ 0) :
    principalBand (normalizedPositiveVector e) = principalBand e := principalBand_norm_inv_smul e he

end PrincipalBand
end ThesisCommon
