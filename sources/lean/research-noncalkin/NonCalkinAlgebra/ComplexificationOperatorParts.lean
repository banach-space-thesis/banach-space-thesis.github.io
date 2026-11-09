import NonCalkinAlgebra.ComplexificationApproximable

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u v
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem self_decomposition (f : BanachComplexification X) :
    f = embedding X (toRealMap f 1) - Complex.I • embedding X (toRealMap f Complex.I) := by
  simpa only [map_id, ContinuousLinearMap.id_apply] using
    map_decomposition X (ContinuousLinearMap.id ℝ X) f

/-- Complex linearity and the real embedding determine an operator on the
whole complexification. -/
theorem operator_ext (U V : BanachComplexification X →L[ℂ] BanachComplexification Y)
    (h : ∀ x : X, U (embedding X x) = V (embedding X x)) : U = V := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    U f = U (embedding X (toRealMap f 1) -
        Complex.I • embedding X (toRealMap f Complex.I)) := congrArg U (self_decomposition X f)
    _ = U (embedding X (toRealMap f 1)) -
        Complex.I • U (embedding X (toRealMap f Complex.I)) := by rw [map_sub, map_smul]
    _ = V (embedding X (toRealMap f 1)) -
        Complex.I • V (embedding X (toRealMap f Complex.I)) := by rw [h, h]
    _ = V (embedding X (toRealMap f 1) -
        Complex.I • embedding X (toRealMap f Complex.I)) := by rw [map_sub, map_smul]
    _ = V f := congrArg V (self_decomposition X f).symm

def operatorParts :
    (BanachComplexification X →L[ℂ] BanachComplexification Y) →L[ℝ]
      ((X →L[ℝ] Y) × (X →L[ℝ] Y)) :=
  (extractOperator X 1).prod (-(extractOperator X Complex.I))

def fromOperatorParts : ((X →L[ℝ] Y) × (X →L[ℝ] Y)) →L[ℝ]
    (BanachComplexification X →L[ℂ] BanachComplexification Y) :=
  (mapOperator X).comp (ContinuousLinearMap.fst ℝ _ _) +
    ((Complex.I • ContinuousLinearMap.id ℂ
      (BanachComplexification X →L[ℂ] BanachComplexification Y)).restrictScalars ℝ).comp
      ((mapOperator X).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem operatorParts_apply
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y) :
    operatorParts X U = (extractOperator X 1 U, -extractOperator X Complex.I U) := rfl

@[simp] theorem fromOperatorParts_apply (p : (X →L[ℝ] Y) × (X →L[ℝ] Y)) :
    fromOperatorParts X p = map X p.1 + Complex.I • map X p.2 := rfl

theorem from_to_operatorParts
    (U : BanachComplexification X →L[ℂ] BanachComplexification Y) :
    fromOperatorParts X (operatorParts X U) = U := by
  apply operator_ext X
  intro x
  change map X (extractOperator X 1 U) (embedding X x) +
    Complex.I • map X (-extractOperator X Complex.I U) (embedding X x) = U (embedding X x)
  rw [map_embedding, map_embedding]
  change fromCoordinates Y (toCoordinates Y (U (embedding X x))) = U (embedding X x)
  exact from_to_coordinates Y _

theorem to_from_operatorParts (p : (X →L[ℝ] Y) × (X →L[ℝ] Y)) :
    operatorParts X (fromOperatorParts X p) = p := by
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    change toRealMap (map X p.1 (embedding X x) +
      Complex.I • map X p.2 (embedding X x)) 1 = p.1 x
    rw [toRealMap_add, ContinuousLinearMap.add_apply, toRealMap_smul_apply,
      map_embedding, map_embedding, embedding_apply, embedding_apply]
    simp
  · apply ContinuousLinearMap.ext
    intro x
    change -toRealMap (map X p.1 (embedding X x) +
      Complex.I • map X p.2 (embedding X x)) Complex.I = p.2 x
    rw [toRealMap_add, ContinuousLinearMap.add_apply, toRealMap_smul_apply,
      map_embedding, map_embedding, embedding_apply, embedding_apply]
    simp

/-- The full operator-space complexification identification, as a bounded
real-linear equivalence. Multiplicativity is a further property. -/
def operatorCoordinates :
    (BanachComplexification X →L[ℂ] BanachComplexification Y) ≃L[ℝ]
      ((X →L[ℝ] Y) × (X →L[ℝ] Y)) where
  toFun := operatorParts X
  invFun := fromOperatorParts X
  map_add' := (operatorParts X).map_add
  map_smul' := (operatorParts X).map_smul
  left_inv := from_to_operatorParts X
  right_inv := to_from_operatorParts X
  continuous_toFun := (operatorParts X).continuous
  continuous_invFun := (fromOperatorParts X).continuous

end NonCalkinAlgebra.BanachComplexification
