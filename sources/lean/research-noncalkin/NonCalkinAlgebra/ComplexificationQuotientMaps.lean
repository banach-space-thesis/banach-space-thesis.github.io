import NonCalkinAlgebra.ComplexificationIdealParts
import NonCalkinAlgebra.RealQuotientAlgebra
import NonCalkinAlgebra.QuotientAlgebra
import NonCalkinAlgebra.NormedQuotientMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/- Keep the pointwise real scalar structure in the coordinate construction.
It agrees with complex restriction by the scalar-tower identities; choosing
it explicitly avoids non-definitional diamonds through NormedAlgebra. -/
instance (priority := 1100) operatorPointwiseRealNormedSpace :
    NormedSpace ℝ (BanachComplexification X →L[ℂ] BanachComplexification X) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)

instance (priority := 1100) quotientPointwiseRealNormedSpace (k : QuotientConvention) :
    NormedSpace ℝ (OperatorQuotient (BanachComplexification X) k) :=
  Submodule.Quotient.normedSpace (operatorIdeal (BanachComplexification X) k) ℝ

omit [CompleteSpace X] in
theorem map_mem_operatorIdeal_iff (k : QuotientConvention) (T : X →L[ℝ] X) :
    map X T ∈ operatorIdeal (BanachComplexification X) k ↔ T ∈ realOperatorIdeal X k := by
  cases k
  · exact approximable_map_iff X T
  · exact compact_map_iff X T

/-- The real operator quotient embeds boundedly into the corresponding
complex operator quotient by complexifying representatives. -/
def quotientMap (k : QuotientConvention) :
    RealOperatorQuotient X k →L[ℝ] OperatorQuotient (BanachComplexification X) k :=
  normedQuotientMap (𝕜 := ℝ) (E := X →L[ℝ] X)
    (F := BanachComplexification X →L[ℂ] BanachComplexification X) (realOperatorIdeal X k)
    ((operatorIdeal (BanachComplexification X) k).restrictScalars ℝ)
    (mapOperator X (Y := X)) (by
      intro T hT
      change map X T ∈ operatorIdeal (BanachComplexification X) k
      exact (map_mem_operatorIdeal_iff X k T).mpr hT)

/-- The first real coordinate descends to the actual quotients. -/
def quotientRealPart (k : QuotientConvention) :
    OperatorQuotient (BanachComplexification X) k →L[ℝ] RealOperatorQuotient X k :=
  normedQuotientMap (𝕜 := ℝ)
    (E := BanachComplexification X →L[ℂ] BanachComplexification X) (F := X →L[ℝ] X)
    ((operatorIdeal (BanachComplexification X) k).restrictScalars ℝ)
    (realOperatorIdeal X k) (extractOperator X (Y := X) 1) (by
      intro U hU
      change extractOperator X 1 U ∈ realOperatorIdeal X k
      exact ((operatorIdeal_operatorParts_iff X k U).mp hU).1)

/-- The second coordinate, with the sign convention f(i)=-Im(f), descends. -/
def quotientImagCoordinate (k : QuotientConvention) :
    OperatorQuotient (BanachComplexification X) k →L[ℝ] RealOperatorQuotient X k :=
  normedQuotientMap (𝕜 := ℝ)
    (E := BanachComplexification X →L[ℂ] BanachComplexification X) (F := X →L[ℝ] X)
    ((operatorIdeal (BanachComplexification X) k).restrictScalars ℝ)
    (realOperatorIdeal X k) (extractOperator X (Y := X) Complex.I) (by
      intro U hU
      change extractOperator X Complex.I U ∈ realOperatorIdeal X k
      exact ((operatorIdeal_operatorParts_iff X k U).mp hU).2)

@[simp] theorem quotientMap_mk (k : QuotientConvention) (T : X →L[ℝ] X) :
    quotientMap X k (realOperatorQuotientMap X k T) =
      operatorQuotientMap (BanachComplexification X) k (map X T) := rfl

@[simp] theorem quotientRealPart_mk (k : QuotientConvention)
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    quotientRealPart X k (operatorQuotientMap (BanachComplexification X) k U) =
      realOperatorQuotientMap X k (extractOperator X 1 U) := rfl

@[simp] theorem quotientImagCoordinate_mk (k : QuotientConvention)
    (U : BanachComplexification X →L[ℂ] BanachComplexification X) :
    quotientImagCoordinate X k (operatorQuotientMap (BanachComplexification X) k U) =
      realOperatorQuotientMap X k (extractOperator X Complex.I U) := rfl

theorem quotientRealPart_map (k : QuotientConvention) (a : RealOperatorQuotient X k) :
    quotientRealPart X k (quotientMap X k a) = a := by
  induction a using Submodule.Quotient.induction_on with
  | H T =>
    change quotientRealPart X k (quotientMap X k (realOperatorQuotientMap X k T)) = _
    rw [quotientMap_mk, quotientRealPart_mk, extractOperator_map, Complex.one_re, one_smul]
    rfl

theorem quotientImagCoordinate_map (k : QuotientConvention) (a : RealOperatorQuotient X k) :
    quotientImagCoordinate X k (quotientMap X k a) = 0 := by
  induction a using Submodule.Quotient.induction_on with
  | H T =>
    change quotientImagCoordinate X k (quotientMap X k (realOperatorQuotientMap X k T)) = _
    rw [quotientMap_mk, quotientImagCoordinate_mk, extractOperator_map, Complex.I_re,
      zero_smul, map_zero]

theorem quotientMap_mul (k : QuotientConvention) (a b : RealOperatorQuotient X k) :
    quotientMap X k (a * b) = quotientMap X k a * quotientMap X k b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change quotientMap X k (realOperatorQuotientMap X k (S * T)) = _
  rw [quotientMap_mk]
  have hmul : map X (S * T) = map X S * map X T := map_comp X T S
  rw [hmul, operatorQuotientMap_mul]
  rfl

theorem quotientMap_one (k : QuotientConvention) : quotientMap X k 1 = 1 := by
  change quotientMap X k (realOperatorQuotientMap X k 1) = _
  rw [quotientMap_mk]
  change operatorQuotientMap (BanachComplexification X) k
    (map X (ContinuousLinearMap.id ℝ X)) = 1
  rw [map_id]
  exact operatorQuotientMap_one _ _

end NonCalkinAlgebra.BanachComplexification
