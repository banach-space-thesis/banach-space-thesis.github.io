import ThesisCommon.Analysis.JamesSequenceLpRetraction
import ThesisCommon.Analysis.QuantitativeDecompositionDefinitions

/-! The concrete complemented scalar lp subspace of James space. Its range
has the inherited James norm, the equivalence is even-coordinate insertion,
and its inverse reads adjacent differences. Both the distortion and the
projection norm are at most two. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesLpRange : Submodule 𝕜 (JamesSequenceSpace 𝕜 p) :=
  LinearMap.range (jamesLpInsert (𝕜 := 𝕜) p hp).toLinearMap

@[simp] theorem jamesLpRead_insert (a : SequenceSum p 𝕜) :
    jamesLpRead (𝕜 := 𝕜) p hp (jamesLpInsert (𝕜 := 𝕜) p hp a) = a :=
  DFunLike.congr_fun (jamesLpRead_comp_insert p hp) a

def jamesLpRangeRetraction :
    JamesSequenceSpace 𝕜 p →L[𝕜] jamesLpRange (𝕜 := 𝕜) p hp :=
  (jamesLpInsert p hp).rangeRestrict.comp (jamesLpRead p hp)

theorem jamesLpRangeRetraction_fixes (x : jamesLpRange (𝕜 := 𝕜) p hp) :
    jamesLpRangeRetraction (𝕜 := 𝕜) p hp (x : JamesSequenceSpace 𝕜 p) = x := by
  apply Subtype.ext
  obtain ⟨a, ha⟩ := x.property
  change jamesLpInsert (𝕜 := 𝕜) p hp (jamesLpRead (𝕜 := 𝕜) p hp x.val) = x.val
  change jamesLpInsert (𝕜 := 𝕜) p hp a = x.val at ha
  rw [← ha, jamesLpRead_insert]

theorem jamesLpRange_closedComplemented :
    (jamesLpRange (𝕜 := 𝕜) p hp).ClosedComplemented :=
  ⟨jamesLpRangeRetraction p hp, jamesLpRangeRetraction_fixes p hp⟩

def jamesLpRangeEquiv : SequenceSum p 𝕜 ≃L[𝕜] jamesLpRange (𝕜 := 𝕜) p hp :=
  ContinuousLinearEquiv.equivOfInverse (jamesLpInsert (𝕜 := 𝕜) p hp).rangeRestrict
    ((jamesLpRead (𝕜 := 𝕜) p hp).comp (jamesLpRange (𝕜 := 𝕜) p hp).subtypeL)
    (jamesLpRead_insert (𝕜 := 𝕜) p hp) (jamesLpRangeRetraction_fixes (𝕜 := 𝕜) p hp)

theorem norm_jamesLpRangeEquiv_le :
    ‖(jamesLpRangeEquiv (𝕜 := 𝕜) p hp).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖jamesLpInsert (𝕜 := 𝕜) p hp a‖ ≤ 2 * ‖a‖
  exact (ContinuousLinearMap.le_opNorm _ a).trans
    (mul_le_mul_of_nonneg_right (norm_jamesLpInsert_le p hp) (norm_nonneg a))

theorem norm_jamesLpRangeEquiv_symm_le :
    ‖(jamesLpRangeEquiv (𝕜 := 𝕜) p hp).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖jamesLpRead (𝕜 := 𝕜) p hp x.val‖ ≤ 1 * ‖x‖
  exact (ContinuousLinearMap.le_opNorm _ x.val).trans
    (mul_le_mul_of_nonneg_right (norm_jamesLpRead_le p hp) (norm_nonneg x))

theorem norm_jamesLpRangeRetraction_le :
    ‖jamesLpRangeRetraction (𝕜 := 𝕜) p hp‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖jamesLpProjection (𝕜 := 𝕜) p hp x‖ ≤ 2 * ‖x‖
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (norm_jamesLpProjection_le p hp) (norm_nonneg x))

include hp in
/-- For every finite p ≥ 1, James space contains an actual two-complemented
copy of scalar lp, with attained isomorphism distortion at most two. -/
theorem jamesSequence_hasComplementedLp_withBound :
    HasComplementedCopyWithBound 𝕜 (JamesSequenceSpace 𝕜 p) (SequenceSum p 𝕜) 2 2 := by
  refine ⟨jamesLpRange p hp, (jamesLpRange_closedComplemented p hp).isClosed,
    jamesLpRangeRetraction p hp, jamesLpRangeRetraction_fixes p hp,
    norm_jamesLpRangeRetraction_le p hp, jamesLpRangeEquiv p hp, ?_⟩
  have h := mul_le_mul (norm_jamesLpRangeEquiv_le (𝕜 := 𝕜) p hp)
    (norm_jamesLpRangeEquiv_symm_le (𝕜 := 𝕜) p hp)
    (norm_nonneg (jamesLpRangeEquiv (𝕜 := 𝕜) p hp).symm.toContinuousLinearMap)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_one] using h

include hp in
theorem jamesSequence_hasComplementedLp :
    HasComplementedCopy 𝕜 (JamesSequenceSpace 𝕜 p) (SequenceSum p 𝕜) :=
  (jamesSequence_hasComplementedLp_withBound (𝕜 := 𝕜) p hp).hasComplementedCopy

end ThesisCommon
