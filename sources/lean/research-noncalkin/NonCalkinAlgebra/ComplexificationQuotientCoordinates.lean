import NonCalkinAlgebra.ComplexificationQuotientMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem extractOperator_I_realPart
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    extractOperator X 1 (Complex.I • U) = extractOperator X Complex.I U := by
  ext x
  change toRealMap (U (embedding X x)) (Complex.I * 1) =
    toRealMap (U (embedding X x)) Complex.I
  rw [mul_one]

omit [CompleteSpace X] in
theorem extractOperator_I_imagCoordinate
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    extractOperator X Complex.I (Complex.I • U) = -extractOperator X 1 U := by
  ext x
  change toRealMap (U (embedding X x)) (Complex.I * Complex.I) =
    -toRealMap (U (embedding X x)) 1
  rw [Complex.I_mul_I, map_neg]

theorem quotientRealPart_I_smul (k : QuotientConvention)
    (a : OperatorQuotient (BanachComplexification X) k) :
    quotientRealPart X k (Complex.I • a) = quotientImagCoordinate X k a := by
  induction a using Submodule.Quotient.induction_on with
  | H U =>
    change quotientRealPart X k (operatorQuotientMap (BanachComplexification X) k
      (Complex.I • U)) =
      quotientImagCoordinate X k (operatorQuotientMap (BanachComplexification X) k U)
    rw [quotientRealPart_mk, quotientImagCoordinate_mk, extractOperator_I_realPart]

theorem quotientImagCoordinate_I_smul (k : QuotientConvention)
    (a : OperatorQuotient (BanachComplexification X) k) :
    quotientImagCoordinate X k (Complex.I • a) = -quotientRealPart X k a := by
  induction a using Submodule.Quotient.induction_on with
  | H U =>
    change quotientImagCoordinate X k (operatorQuotientMap (BanachComplexification X) k
      (Complex.I • U)) =
      -quotientRealPart X k (operatorQuotientMap (BanachComplexification X) k U)
    rw [quotientImagCoordinate_mk, quotientRealPart_mk,
      extractOperator_I_imagCoordinate, map_neg]

/-- Every complex quotient class has real coordinate classes. This proves
the required surjectivity statement for the full operator quotient. -/
theorem quotient_decomposition (k : QuotientConvention)
    (a : OperatorQuotient (BanachComplexification X) k) :
    a = quotientMap X k (quotientRealPart X k a) -
      Complex.I • quotientMap X k (quotientImagCoordinate X k a) := by
  induction a using Submodule.Quotient.induction_on with
  | H U =>
    have hneg : map X (-extractOperator X Complex.I U) =
        -map X (extractOperator X Complex.I U) :=
      (mapOperator X (Y := X)).map_neg (extractOperator X (Y := X) Complex.I U)
    have hU : U = map X (extractOperator X 1 U) -
        Complex.I • map X (extractOperator X Complex.I U) := by
      have h := from_to_operatorParts X U
      rw [operatorParts_apply, fromOperatorParts_apply, hneg, smul_neg, ← sub_eq_add_neg] at h
      exact h.symm
    change operatorQuotientMap (BanachComplexification X) k U =
      quotientMap X k (realOperatorQuotientMap X k (extractOperator X 1 U)) -
        Complex.I • quotientMap X k (realOperatorQuotientMap X k (extractOperator X Complex.I U))
    rw [quotientMap_mk, quotientMap_mk]
    simpa only [map_sub, map_smul, RingHom.id_apply] using
      congrArg (operatorQuotientMap (BanachComplexification X) k) hU

def quotientParts (k : QuotientConvention) :
    OperatorQuotient (BanachComplexification X) k →L[ℝ]
      (RealOperatorQuotient X k × RealOperatorQuotient X k) :=
  (quotientRealPart X k).prod (-(quotientImagCoordinate X k))

def quotientFromParts (k : QuotientConvention) :
    (RealOperatorQuotient X k × RealOperatorQuotient X k) →L[ℝ]
      OperatorQuotient (BanachComplexification X) k :=
  (quotientMap X k).comp (ContinuousLinearMap.fst ℝ _ _) +
    ((Complex.I • ContinuousLinearMap.id ℂ (OperatorQuotient (BanachComplexification X) k)).restrictScalars ℝ).comp
      ((quotientMap X k).comp (ContinuousLinearMap.snd ℝ _ _))

theorem quotient_from_to_parts (k : QuotientConvention)
    (a : OperatorQuotient (BanachComplexification X) k) :
    quotientFromParts X k (quotientParts X k a) = a := by
  change quotientMap X k (quotientRealPart X k a) +
    Complex.I • quotientMap X k (-quotientImagCoordinate X k a) = a
  rw [map_neg, smul_neg, ← sub_eq_add_neg]
  exact (quotient_decomposition X k a).symm

theorem quotient_to_from_parts (k : QuotientConvention)
    (p : RealOperatorQuotient X k × RealOperatorQuotient X k) :
    quotientParts X k (quotientFromParts X k p) = p := by
  apply Prod.ext
  · change quotientRealPart X k (quotientMap X k p.1 + Complex.I • quotientMap X k p.2) = p.1
    rw [map_add, quotientRealPart_map, quotientRealPart_I_smul,
      quotientImagCoordinate_map, add_zero]
  · change -quotientImagCoordinate X k (quotientMap X k p.1 + Complex.I • quotientMap X k p.2) = p.2
    rw [map_add, quotientImagCoordinate_map, quotientImagCoordinate_I_smul,
      quotientRealPart_map, zero_add, neg_neg]

/-- Complexification commutes with the two actual operator quotients at the
level of Banach spaces, with bounded coordinate maps and bounded inverse.
The multiplicative splitting used for the real theorem remains separate. -/
def quotientCoordinates (k : QuotientConvention) :
    OperatorQuotient (BanachComplexification X) k ≃L[ℝ]
      (RealOperatorQuotient X k × RealOperatorQuotient X k) where
  toFun := quotientParts X k
  invFun := quotientFromParts X k
  map_add' := (quotientParts X k).map_add
  map_smul' := (quotientParts X k).map_smul
  left_inv := quotient_from_to_parts X k
  right_inv := quotient_to_from_parts X k
  continuous_toFun := (quotientParts X k).continuous
  continuous_invFun := (quotientFromParts X k).continuous

end NonCalkinAlgebra.BanachComplexification
