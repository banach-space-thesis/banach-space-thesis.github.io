import Sigma.ComplexModulusEmbedding
import Sigma.ComplexProductNorming
import Sigma.ComplexFunctionSpaces

noncomputable section
open scoped BoundedContinuousFunction
namespace SigmaNonprimarity

theorem complex_countable_submodule_has_countable_norming {I : Type*} [TopologicalSpace I]
    [Countable I] [Nonempty I] (S : Submodule ℂ (I →ᵇ ℂ)) :
    ∃ e : ℕ → S →L[ℂ] ℂ, IsComplexCNorming e 1 := by
  obtain ⟨p,hp⟩ := exists_surjective_nat I
  exact ⟨_,complexSubmoduleEvaluation_oneNorming S p hp⟩

theorem complex_submodule_has_countable_norming (S : Submodule ℂ ComplexAmbient) :
    ∃ e : ℕ → S →L[ℂ] ℂ, IsComplexCNorming e 1 :=
  complex_countable_submodule_has_countable_norming S

theorem complex_candidate_has_countable_norming (B Atilde : Set (Set Point)) :
    ∃ e : ℕ → ComplexCandidateX B Atilde →L[ℂ] ℂ, IsComplexCNorming e 1 := by
  obtain ⟨a,ha⟩ := complex_submodule_has_countable_norming (ComplexCylinderJL Atilde)
  obtain ⟨b,hb⟩ := complex_submodule_has_countable_norming (complexAntisymmetricJL B)
  exact complex_product_has_one_norming ha hb

end SigmaNonprimarity

