import Posets.IdealCorrespondence
import Posets.ProductIdealClosed

/-! Passing from quotient closed ideals to nontrivial operator ideals removes
the whole operator algebra and adds its minimal nonzero compact ideal. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem mrowka_compactOperators_ne_univ (h𝒜 : IsAlmostDisjoint 𝒜) :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ≠ Set.univ := by
  obtain ⟨P, _, hP⟩ := mrowka_exists_separable_noncompact (𝕜 := 𝕜) h𝒜
  intro h
  apply hP
  change P ∈ {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T}
  rw [h]
  exact Set.mem_univ P

private theorem compact_ssubset_univ (h𝒜 : IsAlmostDisjoint 𝒜) :
    {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ⊂ Set.univ :=
  Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, mrowka_compactOperators_ne_univ h𝒜⟩

private theorem aboveCompact_ne_zero (I : IdealsAboveCompact 𝕜 (Space 𝕜 𝒜)) :
    I.val ≠ {0} := by
  intro h
  apply mrowka_compactOperators_ne_zero (𝕜 := 𝕜) (𝒜 := 𝒜)
  apply Set.Subset.antisymm (h ▸ I.property.2.subset)
  intro T hT
  have hT0 := Set.mem_singleton_iff.mp hT
  subst T
  exact isCompactOperator_zero

/-- The endpoint exchange is a bijection even when the quotient is zero. -/
def aboveCompactNontrivialEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) ≃
      NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) := by
  classical
  let K : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) := {T | IsCompactOperator T}
  have hK : IsClosedIdeal 𝕜 K := JFA.compactOperators_closedIdeal
  have hK0 : K ≠ {0} := mrowka_compactOperators_ne_zero
  have hKtop : K ≠ Set.univ := mrowka_compactOperators_ne_univ h𝒜
  let f : IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) →
      NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) := fun I =>
    if h : I.val = Set.univ then ⟨K, hK, hK0, hKtop⟩
    else ⟨I.val, I.property.1, aboveCompact_ne_zero I, h⟩
  let g : NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) →
      IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) := fun I =>
    if h : I.val = K then
      ⟨Set.univ, (⊤ : ClosedIdeal 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)).property,
        compact_ssubset_univ h𝒜⟩
    else ⟨I.val, I.property.1, Set.ssubset_iff_subset_ne.mpr
      ⟨mrowka_compactOperators_minimal h𝒜 I.property.1 I.property.2.1,
        fun he => h he.symm⟩⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro I
    apply Subtype.ext
    have hne : I.val ≠ K := fun he => I.property.2.ne he.symm
    by_cases ht : I.val = Set.univ
    · simp [f, g, ht]
    · simp [f, g, ht, hne]
  · intro I
    apply Subtype.ext
    by_cases h : I.val = K
    · simp [f, g, h]
    · simp [f, g, h, I.property.2.2]

/-- Actual closed ideals of the Banach quotient and nontrivial operator ideals
have the same cardinality, with an explicit equivalence. -/
def quotientNontrivialIdealEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    ClosedIdeal 𝕜 (SeparableQuotient 𝕜 (Space 𝕜 𝒜)) ≃
      NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) :=
  (quotientClosedIdealOrderIso 𝕜 (Space 𝕜 𝒜)).symm.toEquiv.trans
    ((mrowkaQuotientIdealOrderIso h𝒜).toEquiv.trans (aboveCompactNontrivialEquiv h𝒜))

section Split
variable {C : Type} [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    [CompleteSpace C]
    (θ : BoundedHom 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) C)
    (ρ : BoundedHom 𝕜 C (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜))
    (hs : StrongSplit 𝕜 (Space 𝕜 𝒜) C θ ρ)

def strongSplitIdealsAboveCompact (h𝒜 : IsAlmostDisjoint 𝒜) :
    ClosedIdeal 𝕜 C ≃o IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) :=
  (closedIdealQuotientOrderIso θ hs.1).trans
    { toFun := fun I => ⟨I.val, I.property.1,
        (mrowka_strictlyAboveCompact_iff_contains_separable h𝒜 I.property.1).mpr
          (fun T hT => I.property.2 ((hs.2.1 T).mpr hT))⟩
      invFun := fun I => ⟨I.val, I.property.1, fun T hT =>
        (mrowka_strictlyAboveCompact_iff_contains_separable h𝒜 I.property.1).mp
          I.property.2 ((hs.2.1 T).mp hT)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_rel_iff' := Iff.rfl }

@[simp] theorem strongSplitIdealsAboveCompact_apply (h𝒜 : IsAlmostDisjoint 𝒜)
    (I : ClosedIdeal 𝕜 C) :
    (strongSplitIdealsAboveCompact θ ρ hs h𝒜 I).val = θ ⁻¹' I.val := rfl

/-- The literal ideal-count transfer for every realization in Theorem 1.5. -/
def strongSplitNontrivialIdealEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    ClosedIdeal 𝕜 C ≃ NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) :=
  (strongSplitIdealsAboveCompact θ ρ hs h𝒜).toEquiv.trans
    (aboveCompactNontrivialEquiv h𝒜)

end Split

end Posets
