import ThesisCommon.Analysis.GowersMaureySpreadLaurentReduction
import ThesisCommon.Analysis.WienerContinuousConvolution

/-! Actual Laurent composition agrees with literal convolution modulo the
block-seminorm kernel. Unilateral shifts have boundary terms, so this is
deliberately not an equality of endomorphisms. Finite shift defects vanish
on a tail, and norm-density extends the result to all Wiener sequences. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem integerShift_basis_tail (D : ConstructionData 𝕜)
    (d : ℤ) (j : ℕ) (hj : d.natAbs ≤ j) :
    integerShift D d (basisVector D j) = basisVector D ((j : ℤ)+d).toNat := by
  cases d with
  | ofNat n =>
    rw [integerShift, completedSpread_basisVector, if_pos (Nat.zero_le _)]
    congr 1
  | negSucc n =>
    have hn : n+1 ≤ j := hj
    rw [integerShift, completedSpread_basisVector, if_pos hn]
    congr 1
    omega

theorem spaceOperatorSeminorm_integerShift_product_defect
    (D : ConstructionData 𝕜) (a b : ℤ) :
    spaceOperatorSeminorm D
      ((integerShift D a).comp (integerShift D b) - integerShift D (a+b)) = 0 := by
  apply spaceOperatorSeminorm_eq_zero_of_basis_tail D _ (a.natAbs+b.natAbs)
  intro j hj
  have hb : b.natAbs ≤ j := by omega
  have hbneg : -b ≤ (b.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -b))
  have ha : a.natAbs ≤ ((j : ℤ)+b).toNat := by omega
  have hab : (a+b).natAbs ≤ j := (Int.natAbs_add_le a b).trans (by omega)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    integerShift_basis_tail D b j hb, integerShift_basis_tail D a _ ha,
    integerShift_basis_tail D (a+b) j hab]
  apply sub_eq_zero.mpr
  congr 1
  omega

def laurentProductDefectRight (D : ConstructionData 𝕜) (a : WienerSequences 𝕜) :
    WienerSequences 𝕜 →L[𝕜] (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  (ContinuousLinearMap.compL 𝕜 (ShiftSpace D) (ShiftSpace D) (ShiftSpace D)
      (laurentOperator D a)).comp (laurentOperator D) -
    (laurentOperator D).comp (wienerConvolutionBilinear a)

theorem laurentProductDefectRight_apply (D : ConstructionData 𝕜)
    (a b : WienerSequences 𝕜) :
    laurentProductDefectRight D a b =
      (laurentOperator D a).comp (laurentOperator D b) -
        laurentOperator D (wienerConvolution a b) := rfl

def laurentProductDefectLeft (D : ConstructionData 𝕜) (b : WienerSequences 𝕜) :
    WienerSequences 𝕜 →L[𝕜] (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  ((ContinuousLinearMap.compL 𝕜 (ShiftSpace D) (ShiftSpace D) (ShiftSpace D)).flip
      (laurentOperator D b)).comp (laurentOperator D) -
    (laurentOperator D).comp (wienerConvolutionBilinear.flip b)

theorem laurentProductDefectLeft_apply (D : ConstructionData 𝕜)
    (a b : WienerSequences 𝕜) :
    laurentProductDefectLeft D b a =
      (laurentOperator D a).comp (laurentOperator D b) -
        laurentOperator D (wienerConvolution a b) := rfl

theorem spaceOperatorSeminorm_laurent_single_product_defect
    (D : ConstructionData 𝕜) (i j : ℤ) (a b : 𝕜) :
    spaceOperatorSeminorm D
      (laurentProductDefectRight D (lp.single 1 i a) (lp.single 1 j b)) = 0 := by
  rw [laurentProductDefectRight_apply, wienerConvolution_single_single,
    laurentOperator_single_scalar, laurentOperator_single_scalar, laurentOperator_single_scalar,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
    ← smul_sub, map_smul_eq_mul, spaceOperatorSeminorm_integerShift_product_defect, mul_zero]

theorem spaceOperatorSeminorm_laurent_product_defect
    (D : ConstructionData 𝕜) (a b : WienerSequences 𝕜) :
    spaceOperatorSeminorm D ((laurentOperator D a).comp (laurentOperator D b) -
      laurentOperator D (wienerConvolution a b)) = 0 := by
  apply wiener_map_seminorm_zero_of_single (spaceOperatorSeminorm D)
    (spaceOperatorSeminorm_continuous D) (laurentProductDefectLeft D b) _ a
  intro i c
  apply wiener_map_seminorm_zero_of_single (spaceOperatorSeminorm D)
    (spaceOperatorSeminorm_continuous D) (laurentProductDefectRight D (lp.single 1 i c)) _ b
  intro j d
  exact spaceOperatorSeminorm_laurent_single_product_defect D i j c d

theorem spaceOperatorSeminorm_laurent_comp_eq
    (D : ConstructionData 𝕜) (a b : WienerSequences 𝕜) :
    spaceOperatorSeminorm D ((laurentOperator D a).comp (laurentOperator D b)) =
      ‖wienerConvolution a b‖ := by
  rw [spaceOperatorSeminorm_eq_of_sub_eq_zero D
    (spaceOperatorSeminorm_laurent_product_defect D a b),
    spaceOperatorSeminorm_laurentOperator]

theorem spaceOperatorSeminorm_laurent_comp_le
    (D : ConstructionData 𝕜) (a b : WienerSequences 𝕜) :
    spaceOperatorSeminorm D ((laurentOperator D a).comp (laurentOperator D b)) ≤
      spaceOperatorSeminorm D (laurentOperator D a) *
        spaceOperatorSeminorm D (laurentOperator D b) := by
  rw [spaceOperatorSeminorm_laurent_comp_eq, spaceOperatorSeminorm_laurentOperator,
    spaceOperatorSeminorm_laurentOperator]
  exact norm_wienerConvolution_le a b

end ThesisCommon.GowersMaurey
