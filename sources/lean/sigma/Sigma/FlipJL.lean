import Sigma.FinalFamilies
import Sigma.JLEvaluation

/-! The coordinate interchange preserves the split JL space and swaps each
pair of generating split pieces. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem flip_eq_two_average_sub (f : Ambient) : flip f = (2 : ℝ) • average f - f := by
  ext p
  simp only [flip_apply,average_apply,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply,smul_eq_mul]
  ring

theorem flip_characteristic_split {J : Set ℕ} {b : Set Point} (h : Splits J b) :
    flip (characteristic b) = characteristic (cylinder J \ b) := by
  rw [flip_eq_two_average_sub,average_characteristic_split h,smul_smul]
  norm_num
  rw [characteristic_partition h.1]
  abel

theorem flip_characteristic_other_split {J : Set ℕ} {b : Set Point} (h : Splits J b) :
    flip (characteristic (cylinder J \ b)) = characteristic b := by
  have ht := congrArg flip (flip_characteristic_split h)
  rw [flip_flip] at ht
  exact ht.symm

theorem flip_characteristic_singleton (p : Point) :
    flip (characteristic {p}) = characteristic {(p.1,!p.2)} := by
  classical
  rcases p with ⟨n,bit⟩
  ext ⟨m,bit'⟩
  cases bit <;> cases bit' <;> simp

theorem flip_characteristic_univ : flip (characteristic Set.univ) = characteristic Set.univ := by
  ext p
  simp

theorem flip_mem_splitJL {I : Type} (J : I → Set ℕ) (b : I → Set Point)
    (hs : ∀ i, Splits (J i) (b i)) {f : Ambient} (hf : f ∈ JL (splitFamily J b)) :
    flip f ∈ JL (splitFamily J b) := by
  rw [flip_eq_two_average_sub]
  exact (JL _).sub_mem ((JL _).smul_mem _
    (cylinderJL_le_splitJL J b hs (average_mem_cylinderJL J b hs hf))) hf

def EnumeratedConstruction.flipJL (D : EnumeratedConstruction) (side : Bool) :
    JL (D.family side) →L[ℝ] JL (D.family side) :=
  (flip.comp (D.family side |> JL).subtypeL).codRestrict _
    (fun f => flip_mem_splitJL _ _ (D.splits side) f.property)

@[simp] theorem EnumeratedConstruction.flipJL_apply (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) : (D.flipJL side f).val = flip f.val := rfl

def bitFlipEquiv (I : Type) : (I × Bool) ≃ (I × Bool) where
  toFun p := (p.1,!p.2)
  invFun p := (p.1,!p.2)
  left_inv p := by rcases p with ⟨i,b⟩; simp
  right_inv p := by rcases p with ⟨i,b⟩; simp

def indexedAtomFlip : IndexedAtom (ConstructionIndex × Bool) ≃ IndexedAtom (ConstructionIndex × Bool) :=
  Equiv.sumCongr (bitFlipEquiv ℕ) (Equiv.sumCongr (bitFlipEquiv ConstructionIndex) (Equiv.refl Unit))

theorem indexedAtomFlip_involutive : Function.Involutive indexedAtomFlip := by
  rintro (⟨n,bit⟩ | (⟨i,bit⟩ | u)) <;> simp [indexedAtomFlip,bitFlipEquiv]

end SigmaNonprimarity
