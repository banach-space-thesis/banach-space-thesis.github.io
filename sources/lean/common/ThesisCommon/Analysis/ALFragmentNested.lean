import ThesisCommon.Analysis.ALFragmentHomogeneity
import ThesisCommon.Analysis.PrincipalDensityNested

/-! Fragments of a fragment are exactly the original fragments below it,
with their actual order and norm metric. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E]
variable (e : E) [Fact (0 ≤ e)]

instance positiveFragmentValueNonnegFact (a : PositiveFragmentAlgebra e) :
    Fact (0 ≤ positiveFragmentValue a) := ⟨positiveFragmentValue_nonneg a⟩

def positiveFragmentNestedOrderIso (a : PositiveFragmentAlgebra e) :
    PositiveFragmentAlgebra (positiveFragmentValue a) ≃o Iic a where
  toFun b := ⟨positiveFragmentOf
    ((positiveFragmentValue_isFragment b).trans (positiveFragmentValue_isFragment a)),
      positiveFragmentValue_le b⟩
  invFun b := positiveFragmentOf ⟨positiveFragmentValue_nonneg b.val, b.property, by
    apply le_antisymm
    · exact (inf_le_inf_left _ (sub_le_sub_right (positiveFragmentValue_le a) _)).trans_eq
        (positiveFragmentValue_isFragment b.val).2.2
    · exact le_inf (positiveFragmentValue_nonneg b.val) (sub_nonneg.mpr b.property)⟩
  left_inv b := positiveFragmentValue_injective _ rfl
  right_inv b := Subtype.ext (positiveFragmentValue_injective _ rfl)
  map_rel_iff' := Iff.rfl

theorem positiveFragmentNestedOrderIso_value (a : PositiveFragmentAlgebra e)
    (b : PositiveFragmentAlgebra (positiveFragmentValue a)) :
    positiveFragmentValue (positiveFragmentNestedOrderIso e a b).val = positiveFragmentValue b := rfl

theorem positiveFragmentNestedOrderIso_isometry (a : PositiveFragmentAlgebra e) :
    Isometry (positiveFragmentNestedOrderIso e a) := by
  apply isometry_iff_dist_eq.mpr
  intro b c
  rfl

def positiveFragmentNestedIsometryEquiv (a : PositiveFragmentAlgebra e) :
    PositiveFragmentAlgebra (positiveFragmentValue a) ≃ᵢ Iic a :=
  ⟨(positiveFragmentNestedOrderIso e a).toEquiv, positiveFragmentNestedOrderIso_isometry e a⟩

theorem topologicalDensity_positiveFragmentValue (a : PositiveFragmentAlgebra e) :
    topologicalDensity (PositiveFragmentAlgebra (positiveFragmentValue a)) = principalDensity a :=
  topologicalDensity_eq_of_homeomorph (positiveFragmentNestedIsometryEquiv e a).toHomeomorph

theorem isDensityHomogeneous_top_positiveFragmentValue_iff [HasSolidNorm E]
    (a : PositiveFragmentAlgebra e) :
    IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra (positiveFragmentValue a)) ↔
      IsDensityHomogeneous a := by
  letI nestedIicContinuousInf : ContinuousInf (Iic a) := ⟨by
    exact ((continuous_subtype_val.comp continuous_fst).inf
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have h := isDensityHomogeneous_orderIso_iff (positiveFragmentNestedOrderIso e a)
    (positiveFragmentNestedIsometryEquiv e a).continuous
    (positiveFragmentNestedIsometryEquiv e a).symm.continuous ⊤
  simpa only [map_top, isDensityHomogeneous_Iic_top_iff] using h.symm

end ThesisCommon
