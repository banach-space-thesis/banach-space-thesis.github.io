import Sigma.ComplexLatticeNorming
import Sigma.ComplexLatticeRealNorming
import Sigma.ComplexNormingTransport
import Sigma.ComplexModulusEmbedding
import ThesisCommon.Analysis.SigmaComplexLatticeRealLp
import ThesisCommon.Analysis.SigmaComplexRealDualOrderedModel
import ThesisCommon.Analysis.NormingTransport

/-! The general complex lattice implication. All ordered dual models are
obtained from the proved real representation theorem, after realifying the
complex dual and using the coordinatewise real product lattice. -/
noncomputable section
universe u v
namespace SigmaNonprimarity
open ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.SigmaComplexLatticeProduct

theorem complex_lattice_not_desiredProperty_of_dual_equiv
    (F : ComplexBanachLattice.{u}) {I : Type v}
    (d : (F →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1)
    (he : ∃ e : ℕ → F →L[ℂ] ℂ, IsComplexNorming e) :
    ¬ ComplexDesiredProperty F := by
  obtain ⟨e,he⟩ := exists_real_norming_of_complex_norming he
  let dP : ((F.RealPart × F.RealPart) →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I × Bool => ℝ) 1 :=
    (F.coordinates.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).symm.trans
      (complexDualLpOneRealEquiv d)
  obtain ⟨J,a,ha⟩ := exists_ordered_dual_ellOne_of_equiv dP
  exact complex_not_desiredProperty_of_ordered_real_product F a ha
    ⟨transportedNorming F.coordinates.symm e,transportedNorming_isNorming F.coordinates.symm he⟩

theorem complex_not_desiredProperty_of_lattice
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {I : Type v} (d : (E →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1)
    (he : ∃ e : ℕ → E →L[ℂ] ℂ, IsComplexNorming e)
    (h : IsomorphicToComplexBanachLattice E) : ¬ ComplexDesiredProperty E := by
  obtain ⟨F,⟨T⟩⟩ := h
  let dF : (F →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1 :=
    (T.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)).symm.trans d
  obtain ⟨e,he⟩ := he
  have heF : ∃ f : ℕ → F →L[ℂ] ℂ, IsComplexNorming f :=
    ⟨complexTransportedNorming T.symm e,complexTransportedNorming_isNorming T.symm he⟩
  exact not_complexDesiredProperty_of_equiv T
    (complex_lattice_not_desiredProperty_of_dual_equiv F dF heF)

theorem complex_not_lattice_of_desiredProperty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {I : Type v} (d : (E →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1)
    (he : ∃ e : ℕ → E →L[ℂ] ℂ, IsComplexNorming e)
    (hDP : ComplexDesiredProperty E) : ¬ IsomorphicToComplexBanachLattice E :=
  fun h => complex_not_desiredProperty_of_lattice d he h hDP

theorem complex_sublattice_of_lattice
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {I : Type v} (d : (E →L[ℂ] ℂ) ≃L[ℂ] lp (fun _ : I => ℂ) 1)
    (he : ∃ e : ℕ → E →L[ℂ] ℂ, IsComplexNorming e)
    (h : IsomorphicToComplexBanachLattice E) : IsomorphicToComplexSublatticeEllInfinity E :=
  complex_sublattice_of_not_desiredProperty E (complex_not_desiredProperty_of_lattice d he h)

end SigmaNonprimarity

