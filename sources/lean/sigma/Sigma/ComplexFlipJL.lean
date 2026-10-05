import Sigma.ComplexFinalFamilies
import Sigma.ComplexJLEvaluation
import Sigma.FlipJL

/-! The coordinate interchange preserves the split ComplexJL space and swaps each
pair of generating split pieces. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem complexFlip_eq_two_average_sub (f : ComplexAmbient) : complexFlip f = (2 : ℂ) • complexAverage f - f := by
  ext p
  simp only [complexFlip_apply,complexAverage_apply,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply,smul_eq_mul]
  ring

theorem complexFlip_characteristic_split {J : Set ℕ} {b : Set Point} (h : Splits J b) :
    complexFlip (complexCharacteristic b) = complexCharacteristic (cylinder J \ b) := by
  rw [complexFlip_eq_two_average_sub,complexAverage_complexCharacteristic_split h,smul_smul]
  norm_num
  rw [complexCharacteristic_partition h.1]
  abel

theorem complexFlip_characteristic_other_split {J : Set ℕ} {b : Set Point} (h : Splits J b) :
    complexFlip (complexCharacteristic (cylinder J \ b)) = complexCharacteristic b := by
  have ht := congrArg complexFlip (complexFlip_characteristic_split h)
  rw [complexFlip_complexFlip] at ht
  exact ht.symm

theorem complexFlip_characteristic_singleton (p : Point) :
    complexFlip (complexCharacteristic {p}) = complexCharacteristic {(p.1,!p.2)} := by
  classical
  rcases p with ⟨n,bit⟩
  ext ⟨m,bit'⟩
  cases bit <;> cases bit' <;> simp

theorem complexFlip_characteristic_univ : complexFlip (complexCharacteristic Set.univ) = complexCharacteristic Set.univ := by
  ext p
  simp

theorem complexFlip_mem_splitJL {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) {f : ComplexAmbient} (hf : f ∈ ComplexJL (splitFamily J b)) :
    complexFlip f ∈ ComplexJL (splitFamily J b) := by
  rw [complexFlip_eq_two_average_sub]
  exact (ComplexJL _).sub_mem ((ComplexJL _).smul_mem _
    (complexCylinderJL_le_complexSplitJL J b hs (complexAverage_mem_complexCylinderJL J b hs hf))) hf

def ComplexEnumeratedConstruction.flipJL (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexJL (D.family side) →L[ℂ] ComplexJL (D.family side) :=
  (complexFlip.comp (D.family side |> ComplexJL).subtypeL).codRestrict _
    (fun f => complexFlip_mem_splitJL _ _ (D.splits side) f.property)

@[simp] theorem ComplexEnumeratedConstruction.flipJL_apply (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) : (D.flipJL side f).val = complexFlip f.val := rfl

end SigmaNonprimarity

