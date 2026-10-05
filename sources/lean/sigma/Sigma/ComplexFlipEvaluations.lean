import Sigma.ComplexFlipJL
import Sigma.FlipEvaluations

/-! The ComplexJL coordinate interchange acts on compactum evaluations by the
corresponding permutation of the isolated, family and infinity atoms. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem ComplexEnumeratedConstruction.flipJL_singleton (D : ComplexEnumeratedConstruction) (side : Bool) (p : Point) :
    D.flipJL side ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL _ p⟩ =
      ⟨complexCharacteristic {(p.1,!p.2)},complexCharacteristic_singleton_mem_ComplexJL _ _⟩ :=
  Subtype.ext (complexFlip_characteristic_singleton p)

theorem ComplexEnumeratedConstruction.flipJL_family (D : ComplexEnumeratedConstruction) (side : Bool)
    (q : ConstructionIndex × Bool) :
    D.flipJL side ⟨complexCharacteristic (D.familyEquiv side q).val,complexCharacteristic_mem_ComplexJL (D.familyEquiv side q).property⟩ =
      ⟨complexCharacteristic (D.familyEquiv side (bitFlipEquiv _ q)).val,
        complexCharacteristic_mem_ComplexJL (D.familyEquiv side (bitFlipEquiv _ q)).property⟩ := by
  apply Subtype.ext
  rcases q with ⟨i,bit⟩
  cases bit
  · exact complexFlip_characteristic_split (D.splits side i)
  · exact complexFlip_characteristic_other_split (D.splits side i)

theorem ComplexEnumeratedConstruction.flipJL_one (D : ComplexEnumeratedConstruction) (side : Bool) :
    D.flipJL side ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL _⟩ =
      ⟨complexCharacteristic Set.univ,complexConstant_mem_ComplexJL _⟩ := Subtype.ext complexFlip_characteristic_univ

theorem ComplexEnumeratedConstruction.complexJLEvaluation_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (p : IndexedAtom (ConstructionIndex × Bool)) :
    (complexJLEvaluation (D.family_almostDisjoint side) (D.family_infinite side)
      (compactumAtomEquiv (D.familyEquiv side) p)).comp (D.flipJL side) =
    complexJLEvaluation (D.family_almostDisjoint side) (D.family_infinite side)
      (compactumAtomEquiv (D.familyEquiv side) (indexedAtomFlip p)) := by
  classical
  have hOne : complexJLContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side)
      ⟨1, by simpa only [complexCharacteristic_univ] using complexConstant_mem_ComplexJL (D.family side)⟩ = 1 := by
    simpa only [complexCharacteristic_univ] using complexJLContinuous_one (D.family_almostDisjoint side) (D.family_infinite side)
  rcases p with ⟨n,bit⟩ | (i | u)
  · apply ContinuousLinearMap.ext
    intro f
    change complexJLEvaluation _ _ (↑(Sum.inl (n,bit) : MrowkaBase (D.family side))) (D.flipJL side f) =
      complexJLEvaluation _ _ (↑(Sum.inl (n,!bit) : MrowkaBase (D.family side))) f
    rw [complexJLEvaluation_base,complexJLEvaluation_base]
    rfl
  · apply complexJLFunctional_ext
    · intro n
      change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_singleton]
      simp only [complexJLEvaluation_apply,complexJLContinuous_singleton,compactumAtomEquiv_family,complexLiftRealContinuous_apply,singletonFunction_apply]
      simp [indexedAtomFlip]
    · intro b
      obtain ⟨j,rfl⟩ := (D.familyEquiv side).surjective b
      change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_family]
      simp only [complexJLEvaluation_apply,complexJLContinuous_family,compactumAtomEquiv_family,complexLiftRealContinuous_apply]
      change (tailFunction (D.family_almostDisjoint side) (D.familyEquiv side (bitFlipEquiv _ j))
          (↑(Sum.inr (D.familyEquiv side i) : MrowkaBase (D.family side))) : ℂ) =
        (tailFunction (D.family_almostDisjoint side) (D.familyEquiv side j)
          (↑(Sum.inr (D.familyEquiv side (bitFlipEquiv _ i)) : MrowkaBase (D.family side))) : ℂ)
      rw [tailFunction_inr,tailFunction_inr]
      apply congrArg Complex.ofReal
      simp only [Equiv.apply_eq_iff_eq]
      simp only [bitFlip_eq_iff]
    · change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_one]
      simp only [complexJLEvaluation_apply,complexCharacteristic_univ,hOne]
      rfl
  · cases u
    apply complexJLFunctional_ext
    · intro n
      change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_singleton]
      simp [complexJLEvaluation_apply,complexJLContinuous_singleton,indexedAtomFlip]
    · intro b
      obtain ⟨j,rfl⟩ := (D.familyEquiv side).surjective b
      change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_family]
      simp [complexJLEvaluation_apply,complexJLContinuous_family,indexedAtomFlip]
    · change complexJLEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_one]
      simp only [complexJLEvaluation_apply,complexCharacteristic_univ,hOne]
      rfl

theorem ComplexEnumeratedConstruction.complexJLContinuous_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) (p : IndexedAtom (ConstructionIndex × Bool)) :
    complexJLContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.flipJL side f)
      (compactumAtomEquiv (D.familyEquiv side) p) =
    complexJLContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) f
      (compactumAtomEquiv (D.familyEquiv side) (indexedAtomFlip p)) :=
  congrArg (fun φ : ComplexJL (D.family side) →L[ℂ] ℂ => φ f) (D.complexJLEvaluation_flip side p)

end SigmaNonprimarity


