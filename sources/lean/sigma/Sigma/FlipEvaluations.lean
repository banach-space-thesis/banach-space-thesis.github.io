import Sigma.FlipJL

/-! The JL coordinate interchange acts on compactum evaluations by the
corresponding permutation of the isolated, family and infinity atoms. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem EnumeratedConstruction.flipJL_singleton (D : EnumeratedConstruction) (side : Bool) (p : Point) :
    D.flipJL side ⟨characteristic {p},characteristic_singleton_mem_JL _ p⟩ =
      ⟨characteristic {(p.1,!p.2)},characteristic_singleton_mem_JL _ _⟩ :=
  Subtype.ext (flip_characteristic_singleton p)

theorem EnumeratedConstruction.flipJL_family (D : EnumeratedConstruction) (side : Bool)
    (q : ConstructionIndex × Bool) :
    D.flipJL side ⟨characteristic (D.familyEquiv side q).val,characteristic_mem_JL (D.familyEquiv side q).property⟩ =
      ⟨characteristic (D.familyEquiv side (bitFlipEquiv _ q)).val,
        characteristic_mem_JL (D.familyEquiv side (bitFlipEquiv _ q)).property⟩ := by
  apply Subtype.ext
  rcases q with ⟨i,bit⟩
  cases bit
  · exact flip_characteristic_split (D.splits side i)
  · exact flip_characteristic_other_split (D.splits side i)

theorem EnumeratedConstruction.flipJL_one (D : EnumeratedConstruction) (side : Bool) :
    D.flipJL side ⟨characteristic Set.univ,constant_mem_JL _⟩ =
      ⟨characteristic Set.univ,constant_mem_JL _⟩ := Subtype.ext flip_characteristic_univ

theorem bitFlip_eq_iff (I : Type) (p q : I × Bool) : bitFlipEquiv I p = q ↔ p = bitFlipEquiv I q := by
  constructor
  · intro h
    have hh := congrArg (bitFlipEquiv I) h
    simpa [bitFlipEquiv] using hh
  · intro h
    rw [h]
    simp [bitFlipEquiv]

theorem EnumeratedConstruction.jlEvaluation_flip (D : EnumeratedConstruction) (side : Bool)
    (p : IndexedAtom (ConstructionIndex × Bool)) :
    (jlEvaluation (D.family_almostDisjoint side) (D.family_infinite side)
      (compactumAtomEquiv (D.familyEquiv side) p)).comp (D.flipJL side) =
    jlEvaluation (D.family_almostDisjoint side) (D.family_infinite side)
      (compactumAtomEquiv (D.familyEquiv side) (indexedAtomFlip p)) := by
  classical
  have hOne : jlContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side)
      ⟨1, by simpa only [characteristic_univ] using constant_mem_JL (D.family side)⟩ = 1 := by
    simpa only [characteristic_univ] using jlContinuous_one (D.family_almostDisjoint side) (D.family_infinite side)
  rcases p with ⟨n,bit⟩ | (i | u)
  · apply ContinuousLinearMap.ext
    intro f
    change jlEvaluation _ _ (↑(Sum.inl (n,bit) : MrowkaBase (D.family side))) (D.flipJL side f) =
      jlEvaluation _ _ (↑(Sum.inl (n,!bit) : MrowkaBase (D.family side))) f
    rw [jlEvaluation_base,jlEvaluation_base]
    rfl
  · apply jlFunctional_ext
    · intro n
      change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_singleton]
      simp only [jlEvaluation_apply,jlContinuous_singleton,compactumAtomEquiv_family,singletonFunction_apply]
      simp [indexedAtomFlip]
    · intro b
      obtain ⟨j,rfl⟩ := (D.familyEquiv side).surjective b
      change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_family]
      simp only [jlEvaluation_apply,jlContinuous_family,compactumAtomEquiv_family]
      change tailFunction (D.family_almostDisjoint side) (D.familyEquiv side (bitFlipEquiv _ j))
          (↑(Sum.inr (D.familyEquiv side i) : MrowkaBase (D.family side))) =
        tailFunction (D.family_almostDisjoint side) (D.familyEquiv side j)
          (↑(Sum.inr (D.familyEquiv side (bitFlipEquiv _ i)) : MrowkaBase (D.family side)))
      rw [tailFunction_inr,tailFunction_inr]
      change (if D.familyEquiv side i = D.familyEquiv side (bitFlipEquiv _ j) then 1 else 0) =
        (if D.familyEquiv side (bitFlipEquiv _ i) = D.familyEquiv side j then 1 else 0)
      simp only [Equiv.apply_eq_iff_eq]
      simp only [bitFlip_eq_iff]
    · change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_one]
      simp only [jlEvaluation_apply,characteristic_univ,hOne]
      rfl
  · cases u
    apply jlFunctional_ext
    · intro n
      change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_singleton]
      simp [jlEvaluation_apply,jlContinuous_singleton,indexedAtomFlip]
    · intro b
      obtain ⟨j,rfl⟩ := (D.familyEquiv side).surjective b
      change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_family]
      simp [jlEvaluation_apply,jlContinuous_family,indexedAtomFlip]
    · change jlEvaluation _ _ _ (D.flipJL side _) = _
      rw [D.flipJL_one]
      simp only [jlEvaluation_apply,characteristic_univ,hOne]
      rfl

theorem EnumeratedConstruction.jlContinuous_flip (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) (p : IndexedAtom (ConstructionIndex × Bool)) :
    jlContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) (D.flipJL side f)
      (compactumAtomEquiv (D.familyEquiv side) p) =
    jlContinuousEquiv (D.family_almostDisjoint side) (D.family_infinite side) f
      (compactumAtomEquiv (D.familyEquiv side) (indexedAtomFlip p)) :=
  congrArg (fun φ : JL (D.family side) →L[ℝ] ℝ => φ f) (D.jlEvaluation_flip side p)

end SigmaNonprimarity
