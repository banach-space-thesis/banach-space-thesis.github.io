import ThesisCommon.Analysis.ALTotalBandProperty
import ThesisCommon.Analysis.ALFragmentNested

/-! Every real normed lattice admits a total disjoint family of positive
vectors whose fragment algebras are density homogeneous. This uses actual
local homogeneous fragments and a maximal-family construction. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]

def IsHomogeneousPositiveVector (x : E) : Prop :=
  ∃ hx : 0 ≤ x, letI : Fact (0 ≤ x) := ⟨hx⟩
    IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra x)

theorem exists_homogeneous_positive_vector_le (x : E) (hx : 0 ≤ x) (hx0 : x ≠ 0) :
    ∃ y : E, 0 ≤ y ∧ y ≤ x ∧ y ≠ 0 ∧ IsHomogeneousPositiveVector y := by
  letI : Fact (0 ≤ x) := ⟨hx⟩
  have htop : (⊤ : PositiveFragmentAlgebra x) ≠ ⊥ := by
    intro h
    apply hx0
    simpa only [positiveFragmentValue_top, positiveFragmentValue_bot] using
      congrArg positiveFragmentValue h
  obtain ⟨a, _, ha⟩ := exists_homogeneous_positiveFragment_le htop
  have hapos := positiveFragmentValue_nonneg a
  refine ⟨positiveFragmentValue a, hapos, (positiveFragmentValue_isFragment a).2.1, ?_, ?_⟩
  · intro hz
    apply ha.1
    apply positiveFragmentValue_injective x
    simpa only [positiveFragmentValue_bot] using hz
  · refine ⟨hapos, ?_⟩
    exact (isDensityHomogeneous_top_positiveFragmentValue_iff x a).mpr ha

theorem exists_total_homogeneous_positive_family :
    ∃ S : Set E, (∀ e ∈ S, 0 ≤ e ∧ e ≠ 0 ∧ IsHomogeneousPositiveVector e) ∧
      S.Pairwise (fun e f => e ⊓ f = 0) ∧
      ∀ x : E, 0 ≤ x → (∀ e ∈ S, x ⊓ e = 0) → x = 0 :=
  exists_total_positive_disjoint_family_of_cofinal_property IsHomogeneousPositiveVector
    exists_homogeneous_positive_vector_le

end ThesisCommon

