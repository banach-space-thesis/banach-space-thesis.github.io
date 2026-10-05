import ThesisCommon.Analysis.JamesOperatorCharacter
import ThesisCommon.Analysis.WeakCompactProjectionRange
import ThesisCommon.Analysis.PrimaryDirectSum

/-! In every bounded two-summand decomposition of the concrete James space,
one summand is reflexive. This is a necessary structural step toward
Casazza's primarity theorem, not the primarity conclusion. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (hpl : 1 < p.val.toReal)

include hp hpl in
theorem james_projection_one_range_reflexive
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (hP : P.comp P = P) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (LinearMap.range P.toLinearMap)) ∨
      Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜
        (LinearMap.range (ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) - P).toLinearMap)) := by
  rcases james_projection_weaklyCompact_or_complement p hp hpl P hP with h | h
  · exact Or.inl (weaklyCompact_projection_range_canonical_surjective P hP h)
  · exact Or.inr (weaklyCompact_projection_range_canonical_surjective _
      (complementary_projection hP) h)

include hp hpl in
theorem james_projection_weaklyCompact_iff_complement_not
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (hP : P.comp P = P) :
    IsWeaklyCompactOperator P ↔
      ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) - P) := by
  constructor
  · intro h h'
    have hz := (james_weaklyCompact_iff_scalar_eq_zero p hp hpl P).mp h
    have hz' := (james_weaklyCompact_iff_scalar_eq_zero p hp hpl _).mp h'
    rw [jamesOperatorScalar_sub, jamesOperatorScalar_id, hz, sub_zero] at hz'
    exact one_ne_zero hz'
  · intro h
    rcases james_projection_weaklyCompact_or_complement p hp hpl P hP with h' | h'
    · exact h'
    · exact (h h').elim

include hp hpl in
/-- Exactly one of the two actual complementary ranges is reflexive. -/
theorem james_projection_range_reflexive_iff_complement_nonreflexive
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (hP : P.comp P = P) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 (LinearMap.range P.toLinearMap)) ↔
      ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜
        (LinearMap.range (ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) - P).toLinearMap)) := by
  rw [← weaklyCompact_projection_iff_range_canonical_surjective P hP,
    ← weaklyCompact_projection_iff_range_canonical_surjective _ (complementary_projection hP)]
  exact james_projection_weaklyCompact_iff_complement_not p hp hpl P hP

end ThesisCommon
