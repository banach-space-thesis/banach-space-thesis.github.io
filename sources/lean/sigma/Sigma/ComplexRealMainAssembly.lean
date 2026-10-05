import Sigma.ConstructedAssembly
import ThesisCommon.Analysis.SigmaComplexRealDualOrderedModel

/-! The real ordered-dual input, now proved by the spectral renorming and
atomic representation, also closes the original real assembly. No additional
ordered representation hypothesis remains in these declarations. -/
noncomputable section
universe u
open scoped ThesisCommon.PositiveOperatorOrder
namespace SigmaNonprimarity
open ThesisCommon

theorem sigma_ordered_dual_models (F : RealBanachLattice.{u})
    (h : ∃ I : Type u, Nonempty ((F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)) :
    ∃ J : Type u, ∃ a : (F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : J => ℝ) 1,
      ∀ φ : F →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ j, 0 ≤ a φ j := by
  obtain ⟨I,⟨d⟩⟩ := h
  exact exists_ordered_dual_ellOne_of_equiv d

theorem proposition_3_4_completed (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] : Proposition_3_4 E :=
  proposition_3_4_of_ordered_dual_models E sigma_ordered_dual_models

theorem EnumeratedConstruction.not_lattice_completed
    (D : EnumeratedConstruction) (side : Bool) :
    ¬ IsomorphicToBanachLattice (FinalCandidate D side) :=
  D.not_lattice_of_ordered_dual_models sigma_ordered_dual_models side

theorem theorem_1_1_completed : Theorem_1_1.{u} :=
  theorem_1_1_of_ordered_dual_models sigma_ordered_dual_models

theorem ckCounterexample_completed : CKCounterexample.{u} :=
  ckCounterexample_of_theorem_1_1 theorem_1_1_completed

theorem latticeClass_not_primary_completed :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToBanachLattice X) :=
  latticeClass_not_primary_of_theorem_1_1 theorem_1_1_completed

theorem ckClass_not_primary_completed :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToCK X) :=
  ckClass_not_primary_of_theorem_1_1 theorem_1_1_completed

end SigmaNonprimarity

