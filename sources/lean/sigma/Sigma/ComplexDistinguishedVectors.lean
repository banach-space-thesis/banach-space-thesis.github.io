import Sigma.ComplexSplitting

/-! The actual antisymmetric split generators and the images of all JL
generators under the complementary averaging projection. -/
noncomputable section
namespace SigmaNonprimarity

theorem complex_split_difference_mem {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (i : I) :
    complexCharacteristic (b i) - complexCharacteristic (cylinder (J i) \ b i) ∈ complexAntisymmetricJL (splitFamily J b) := by
  constructor
  · exact (ComplexJL _).sub_mem (complexCharacteristic_mem_ComplexJL (Or.inl ⟨i,rfl⟩))
      (complexCharacteristic_mem_ComplexJL (Or.inr ⟨i,rfl⟩))
  · change complexAverage _ = 0
    rw [map_sub,complexAverage_complexCharacteristic_split (hs i),complexAverage_complexCharacteristic_other_split (hs i),sub_self]

def complexSplitVector {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (i : I) : complexAntisymmetricJL (splitFamily J b) :=
  ⟨complexCharacteristic (b i) - complexCharacteristic (cylinder (J i) \ b i),complex_split_difference_mem J b hs i⟩

theorem complexAntiAverage_complexCharacteristic_split {J : Set ℕ} {b : Set Point} (hs : Splits J b) :
    complexAntiAverage (complexCharacteristic b) =
      (1/2 : ℂ) • (complexCharacteristic b - complexCharacteristic (cylinder J \ b)) := by
  change complexCharacteristic b - complexAverage (complexCharacteristic b) = _
  rw [complexAverage_complexCharacteristic_split hs,complexCharacteristic_partition hs.1]
  module

theorem complexAntiAverage_complexCharacteristic_other_split {J : Set ℕ} {b : Set Point} (hs : Splits J b) :
    complexAntiAverage (complexCharacteristic (cylinder J \ b)) =
      (-1/2 : ℂ) • (complexCharacteristic b - complexCharacteristic (cylinder J \ b)) := by
  change complexCharacteristic (cylinder J \ b) - complexAverage (complexCharacteristic (cylinder J \ b)) = _
  rw [complexAverage_complexCharacteristic_other_split hs,complexCharacteristic_partition hs.1]
  module

theorem complexAntiAverage_complexCharacteristic_univ : complexAntiAverage (complexCharacteristic Set.univ) = 0 := by
  change complexCharacteristic Set.univ - complexAverage (complexCharacteristic Set.univ) = 0
  rw [complexAverage_complexCharacteristic_univ,sub_self]

end SigmaNonprimarity


