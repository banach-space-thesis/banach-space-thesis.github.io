import Posets.IdealCorrespondenceGeneral
import Posets.IdealCorrespondenceCompact

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

/-- On every Mrówka space, containing the separable kernel is exactly being
strictly above the compact ideal. -/
def mrowkaIdealsAboveKernelOrderIso (h𝒜 : IsAlmostDisjoint 𝒜) :
    ClosedIdealsAboveKernel (quotientMapBoundedHom 𝕜 (Space 𝕜 𝒜)) ≃o
      IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) where
  toFun I := by
    refine ⟨I.val, I.property.1, ?_⟩
    apply (mrowka_strictlyAboveCompact_iff_contains_separable h𝒜 I.property.1).mpr
    intro T hT
    apply I.property.2
    exact (quotientMap_eq_zero_iff 𝕜 (Space 𝕜 𝒜) T).mpr hT
  invFun I := by
    refine ⟨I.val, I.property.1, ?_⟩
    intro T hT
    apply (mrowka_strictlyAboveCompact_iff_contains_separable h𝒜 I.property.1).mp I.property.2
    exact (quotientMap_eq_zero_iff 𝕜 (Space 𝕜 𝒜) T).mp hT
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- The exact inverse-image correspondence in Proposition 1.3. -/
def mrowkaQuotientIdealOrderIso (h𝒜 : IsAlmostDisjoint 𝒜) :
    QuotientClosedIdeals 𝕜 (Space 𝕜 𝒜) ≃o IdealsAboveCompact 𝕜 (Space 𝕜 𝒜) :=
  (quotientClosedIdealOrderIso 𝕜 (Space 𝕜 𝒜)).trans
    ((closedIdealQuotientOrderIso (quotientMapBoundedHom 𝕜 (Space 𝕜 𝒜))
      (quotientMap_surjective 𝕜 (Space 𝕜 𝒜))).trans (mrowkaIdealsAboveKernelOrderIso h𝒜))

@[simp] theorem mrowkaQuotientIdealOrderIso_apply (h𝒜 : IsAlmostDisjoint 𝒜)
    (I : QuotientClosedIdeals 𝕜 (Space 𝕜 𝒜)) :
    (mrowkaQuotientIdealOrderIso h𝒜 I).val =
      (quotientMap 𝕜 (Space 𝕜 𝒜)) ⁻¹' I.val := rfl

/-- Proposition 1.3, including compact minimality and the literal preimage
map. Empty and countable almost disjoint families require no separate assumption. -/
theorem proposition_1_3_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) :
    Proposition_1_3 𝕜 𝒜 := by
  intro h𝒜
  refine ⟨JFA.compactOperators_closedIdeal, mrowka_compactOperators_ne_zero,
    (fun I hI hIne => mrowka_compactOperators_minimal h𝒜 hI hIne),
    mrowkaQuotientIdealOrderIso h𝒜, ?_⟩
  intro I
  rfl

end Posets
