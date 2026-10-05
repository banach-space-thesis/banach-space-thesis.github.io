import ThesisCommon.Analysis.BooleanClosureDensity
import ThesisCommon.Analysis.ALFragmentHomogeneity

/-! Metric closure and generated-density control for the actual fragment
Boolean algebra, with continuity of complement derived from its ambient
normed lattice. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u
variable {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]
variable (e : E) [Fact (0 ≤ e)]

theorem continuous_positiveFragment_compl :
    Continuous (fun a : PositiveFragmentAlgebra e => aᶜ) := by
  apply (isometry_positiveFragmentValue e).isEmbedding.continuous_iff.mpr
  simpa only [Function.comp_def, positiveFragmentValue_compl] using
    continuous_const.sub (isometry_positiveFragmentValue e).continuous

def alFragmentSubalgebraTopologicalClosure
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    BooleanSubalgebra (PositiveFragmentAlgebra e) :=
  booleanSubalgebraTopologicalClosure S (continuous_positiveFragment_compl e)

theorem alFragmentSubalgebraTopologicalClosure_coe
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    (alFragmentSubalgebraTopologicalClosure e S : Set (PositiveFragmentAlgebra e)) =
      closure (S : Set (PositiveFragmentAlgebra e)) := rfl

theorem le_alFragmentSubalgebraTopologicalClosure
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    S ≤ alFragmentSubalgebraTopologicalClosure e S := subset_closure

theorem isClosed_alFragmentSubalgebraTopologicalClosure
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    IsClosed (alFragmentSubalgebraTopologicalClosure e S : Set (PositiveFragmentAlgebra e)) :=
  isClosed_closure

theorem topologicalDensity_alFragmentGeneratedClosure_lt
    (C : Set (PositiveFragmentAlgebra e)) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hC : #C < κ) :
    topologicalDensity (alFragmentSubalgebraTopologicalClosure e (BooleanSubalgebra.closure C)) < κ :=
  topologicalDensity_booleanGeneratedClosure_lt C (continuous_positiveFragment_compl e) κ hκ hC

theorem topologicalDensity_alFragmentGeneratedClosure_lt_aleph0_of_finite
    {C : Set (PositiveFragmentAlgebra e)} (hC : C.Finite) :
    topologicalDensity (alFragmentSubalgebraTopologicalClosure e (BooleanSubalgebra.closure C)) < ℵ₀ :=
  topologicalDensity_booleanGeneratedClosure_lt_aleph0_of_finite hC
    (continuous_positiveFragment_compl e)

end ThesisCommon
