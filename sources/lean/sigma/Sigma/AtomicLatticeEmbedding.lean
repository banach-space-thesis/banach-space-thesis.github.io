import Sigma.SublatticeLattice
import ThesisCommon.Analysis.AtomicDualOrder

/-! The countable-support and atomic-functional part of Proposition 3.4.
The final theorem explicitly retains the outstanding ordered-dual
representation theorem as a hypothesis; it is not the completed proposition. -/
noncomputable section
universe u v
namespace SigmaNonprimarity
open ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder

theorem sublattice_of_ordered_dual (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
    {I : Type v} (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (horder : ∀ φ : E →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i)
    (he : ∃ e : ℕ → E →L[ℝ] ℝ, IsNorming e) :
    IsomorphicToSublatticeEllInfinity E :=
  sublattice_of_not_desiredProperty E (not_desiredProperty_of_ordered_dual d horder he)

/-- Conditional reduction of Proposition 3.4 to the independent lattice
representation theorem. All norming, atomic and isomorphism-transfer steps
are proved; existence of the ordered dual models remains an explicit input. -/
theorem proposition_3_4_of_ordered_dual_models (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (hmodels : ∀ F : RealBanachLattice.{u},
      (∃ I : Type u, Nonempty ((F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)) →
      ∃ I : Type u, ∃ d : (F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1,
        ∀ φ : F →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i) : Proposition_3_4 E := by
  intro he hd
  refine ⟨⟨?_,lattice_of_sublattice E⟩,sublattice_iff_not_desiredProperty E⟩
  rintro ⟨F,⟨T⟩⟩
  obtain ⟨I,⟨d⟩⟩ := hd
  let dF : (F →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1 :=
    (T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).symm.trans d
  obtain ⟨J,a,ha⟩ := hmodels F ⟨I,⟨dF⟩⟩
  obtain ⟨e,he⟩ := he
  have heF : ∃ f : ℕ → F →L[ℝ] ℝ, IsNorming f :=
    ⟨transportedNorming T.symm e,transportedNorming_isNorming T.symm he⟩
  exact sublattice_of_not_desiredProperty E
    (not_desiredProperty_of_equiv T (not_desiredProperty_of_ordered_dual a ha heF))

end SigmaNonprimarity
