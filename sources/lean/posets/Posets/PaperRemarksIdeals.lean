import Posets.IdealCorrespondence

/-! Remark 1.4: the entire closed-ideal lattice consists of zero, the compact
ideal, and the inverse images of the closed ideals of the separable quotient. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem remark_1_4_closed_ideal_cases (h𝒜 : IsAlmostDisjoint 𝒜)
    (I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)) (hI : IsClosedIdeal 𝕜 I) :
    I = {0} ∨ I = {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ∨
      ∃ J : QuotientClosedIdeals 𝕜 (Space 𝕜 𝒜),
        I = (quotientMap 𝕜 (Space 𝕜 𝒜)) ⁻¹' J.val := by
  by_cases hzero : I = {0}
  · exact Or.inl hzero
  by_cases hcompact : I = {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T}
  · exact Or.inr (Or.inl hcompact)
  have habove : {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ⊂ I :=
    Set.ssubset_iff_subset_ne.mpr
      ⟨mrowka_compactOperators_minimal h𝒜 hI hzero, Ne.symm hcompact⟩
  let J := (mrowkaQuotientIdealOrderIso h𝒜).symm ⟨I, hI, habove⟩
  refine Or.inr (Or.inr ⟨J, ?_⟩)
  have h := congrArg Subtype.val ((mrowkaQuotientIdealOrderIso h𝒜).apply_symm_apply
    ⟨I, hI, habove⟩)
  exact h.symm

theorem remark_1_4_strict_chain (h𝒜 : IsAlmostDisjoint 𝒜)
    (J : QuotientClosedIdeals 𝕜 (Space 𝕜 𝒜)) :
    ({0} : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)) ⊂
        {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ∧
      {T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜 | IsCompactOperator T} ⊂
        (quotientMap 𝕜 (Space 𝕜 𝒜)) ⁻¹' J.val := by
  refine ⟨Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩,
    (mrowkaQuotientIdealOrderIso h𝒜 J).property.2⟩
  · intro T hT
    have hT0 := Set.mem_singleton_iff.mp hT
    subst T
    exact isCompactOperator_zero
  · exact Ne.symm mrowka_compactOperators_ne_zero

end Posets
