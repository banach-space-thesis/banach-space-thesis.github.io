import Sigma.Splitting

/-! The actual antisymmetric split generators and the images of all JL
generators under the complementary averaging projection. -/
noncomputable section
namespace SigmaNonprimarity

theorem split_difference_mem {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (i : I) :
    characteristic (b i) - characteristic (cylinder (J i) \ b i) ∈ antisymmetricJL (splitFamily J b) := by
  constructor
  · exact (JL _).sub_mem (characteristic_mem_JL (Or.inl ⟨i,rfl⟩))
      (characteristic_mem_JL (Or.inr ⟨i,rfl⟩))
  · change average _ = 0
    rw [map_sub,average_characteristic_split (hs i),average_characteristic_other_split (hs i),sub_self]

def splitVector {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) (i : I) : antisymmetricJL (splitFamily J b) :=
  ⟨characteristic (b i) - characteristic (cylinder (J i) \ b i),split_difference_mem J b hs i⟩

theorem antiAverage_characteristic_split {J : Set ℕ} {b : Set Point} (hs : Splits J b) :
    antiAverage (characteristic b) =
      (1/2 : ℝ) • (characteristic b - characteristic (cylinder J \ b)) := by
  change characteristic b - average (characteristic b) = _
  rw [average_characteristic_split hs,characteristic_partition hs.1]
  module

theorem antiAverage_characteristic_other_split {J : Set ℕ} {b : Set Point} (hs : Splits J b) :
    antiAverage (characteristic (cylinder J \ b)) =
      (-1/2 : ℝ) • (characteristic b - characteristic (cylinder J \ b)) := by
  change characteristic (cylinder J \ b) - average (characteristic (cylinder J \ b)) = _
  rw [average_characteristic_other_split hs,characteristic_partition hs.1]
  module

theorem antiAverage_characteristic_univ : antiAverage (characteristic Set.univ) = 0 := by
  change characteristic Set.univ - average (characteristic Set.univ) = 0
  rw [average_characteristic_univ,sub_self]

end SigmaNonprimarity
