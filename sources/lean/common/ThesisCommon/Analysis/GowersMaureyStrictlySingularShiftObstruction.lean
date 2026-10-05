import ThesisCommon.Analysis.GowersMaureyStrictlySingularRepresentatives
import ThesisCommon.Analysis.GowersMaureyInfiniteDimensional

/-! Genuine lower-bound obstructions to strict singularity for Laurent
operators near a nonzero monomial. The proof uses the actual isometric
right shifts and their contractive left inverses. This is a partial
Laurent obstruction, not the general converse kernel theorem. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem not_strictlySingular_of_close_integerShift (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) (d : ℤ) (c : 𝕜)
    (h : ‖T-c • integerShift D d‖ < ‖c‖) : ¬ IsStrictlySingularOperator T := by
  intro hT
  cases d with
  | ofNat n =>
    let L := completedSpread D n 0
    have hid : L.comp (c • integerShift D (.ofNat n)) =
        c • ContinuousLinearMap.id 𝕜 (ShiftSpace D) := by
      rw [ContinuousLinearMap.comp_smul]
      exact congrArg (fun A => c • A) (completedSpread_left_right D n)
    apply not_strictlySingular_of_norm_sub_smul_id_lt (shiftSpace_infiniteDimensional D)
      (L.comp T) c _ (hT.comp_left L)
    rw [← hid, ← ContinuousLinearMap.comp_sub]
    have hn := mul_le_mul_of_nonneg_right (norm_completedSpread_le D n 0)
      (norm_nonneg (T-c • integerShift D (.ofNat n)))
    rw [one_mul] at hn
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans hn).trans_lt h
  | negSucc n =>
    let R := completedSpread D 0 (n+1)
    have hid : (c • integerShift D (.negSucc n)).comp R =
        c • ContinuousLinearMap.id 𝕜 (ShiftSpace D) := by
      rw [ContinuousLinearMap.smul_comp]
      exact congrArg (fun A => c • A) (completedSpread_left_right D (n+1))
    apply not_strictlySingular_of_norm_sub_smul_id_lt (shiftSpace_infiniteDimensional D)
      (T.comp R) c _ (hT.comp_right R)
    rw [← hid, ← ContinuousLinearMap.sub_comp]
    have hn := mul_le_mul_of_nonneg_left (norm_completedSpread_le D 0 (n+1))
      (norm_nonneg (T-c • integerShift D (.negSucc n)))
    rw [mul_one] at hn
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans hn).trans_lt h

theorem not_strictlySingular_integerShift (D : ConstructionData 𝕜) (d : ℤ) :
    ¬ IsStrictlySingularOperator (integerShift D d) := by
  apply not_strictlySingular_of_close_integerShift D _ d (1 : 𝕜)
  simp

theorem not_strictlySingular_laurent_of_dominant_coefficient
    (D : ConstructionData 𝕜) (a : WienerSequences 𝕜) (d : ℤ)
    (h : ‖a-lp.single 1 d (a d)‖ < ‖a d‖) :
    ¬ IsStrictlySingularOperator (laurentOperator D a) := by
  apply not_strictlySingular_of_close_integerShift D _ d (a d)
  rw [← laurentOperator_single_scalar, ← map_sub]
  have hn := mul_le_mul_of_nonneg_right (norm_laurentOperator_le D)
    (norm_nonneg (a-lp.single 1 d (a d)))
  rw [one_mul] at hn
  exact (((laurentOperator D).le_opNorm _).trans hn).trans_lt h

theorem not_strictlySingular_of_dominant_laurent_representative
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (a : WienerSequences 𝕜) (ha : spaceOperatorSeminorm D (T-laurentOperator D a) = 0)
    (d : ℤ) (h : ‖a-lp.single 1 d (a d)‖ < ‖a d‖) :
    ¬ IsStrictlySingularOperator T := fun hT =>
  not_strictlySingular_laurent_of_dominant_coefficient D a d h
    ((strictlySingular_iff_laurent_of_representative D T a ha).mp hT)

end ThesisCommon.GowersMaurey
