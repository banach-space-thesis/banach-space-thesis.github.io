import ThesisCommon.Analysis.L1ModulusRestriction
import ThesisCommon.Analysis.L1ModulusPostcomp
import ThesisCommon.Analysis.SingularRankOne

/-! A concrete singularity-preserving reduction criterion. Only the two
operators S minus/plus the actual rank-one integral operator need their
moduli preserved. All embedding and rank-one compatibility hypotheses are
explicit; no singular-preserving reduction is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y X' Y' : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [IsFiniteMeasure μ'] [IsFiniteMeasure ν']

theorem isSingularOperator_of_modulus_preserving_restriction
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S)
    (R : Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 ν')
    (J : Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 μ)
    (L : Lp ℝ 1 ν' →L[ℝ] Lp ℝ 1 ν)
    (hinj : Function.Injective L) (habs : ∀ f, L |f| = |L f|)
    (hR : L.comp R = S.comp J)
    (hrank : L.comp (integralRankOne μ' ν') = (integralRankOne μ ν).comp J)
    (hminus : lOneOperatorModulus ((S - integralRankOne μ ν).comp J) =
      (lOneOperatorModulus (S - integralRankOne μ ν)).comp J)
    (hplus : lOneOperatorModulus ((S + integralRankOne μ ν).comp J) =
      (lOneOperatorModulus (S + integralRankOne μ ν)).comp J) :
    IsSingularOperator R := by
  apply (isSingularOperator_iff_abs_sub_rankOne_eq_abs_add R).mpr
  have hSm := (isSingularOperator_iff_abs_sub_rankOne_eq_abs_add S).mp hS
  have hRminus : L.comp (R - integralRankOne μ' ν') =
      (S - integralRankOne μ ν).comp J := by
    rw [ContinuousLinearMap.comp_sub, hR, hrank, ContinuousLinearMap.sub_comp]
  have hRplus : L.comp (R + integralRankOne μ' ν') =
      (S + integralRankOne μ ν).comp J := by
    rw [ContinuousLinearMap.comp_add, hR, hrank, ContinuousLinearMap.add_comp]
  have hm : L.comp |R - integralRankOne μ' ν'| =
      L.comp |R + integralRankOne μ' ν'| := by
    rw [← abs_lOneOperator_postcomp _ L habs, ← abs_lOneOperator_postcomp _ L habs,
      hRminus, hRplus, abs_lOneOperator_eq, abs_lOneOperator_eq, hminus, hplus]
    simpa only [abs_lOneOperator_eq] using
      congrArg (fun A : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν => A.comp J) hSm
  apply ContinuousLinearMap.ext
  intro f
  exact hinj (congrArg (fun A : Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 ν => A f) hm)

/-- One countable set of inputs suffices for singularity preservation in
every compatible finite L1 reduction. -/
theorem exists_countable_lOne_singular_restriction_witnesses
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    ∃ W : Set (Lp ℝ 1 μ), W.Countable ∧
      ∀ (R : Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 ν')
        (J : Lp ℝ 1 μ' →L[ℝ] Lp ℝ 1 μ) (L : Lp ℝ 1 ν' →L[ℝ] Lp ℝ 1 ν),
        (∀ f g, J f ≤ J g ↔ f ≤ g) →
        J (lOneIndicator μ' univ MeasurableSet.univ) =
          lOneIndicator μ univ MeasurableSet.univ →
        Function.Injective L → (∀ f, L |f| = |L f|) →
        L.comp R = S.comp J →
        L.comp (integralRankOne μ' ν') = (integralRankOne μ ν).comp J →
        W ⊆ range J → IsSingularOperator R := by
  obtain ⟨Wm, hcm, hWm, hsm⟩ := lOneOperatorModulus_countable_witnesses
    (S - integralRankOne μ ν) (lOneIndicator μ univ MeasurableSet.univ)
    (lOneIndicator_nonneg _ _)
  obtain ⟨Wp, hcp, hWp, hsp⟩ := lOneOperatorModulus_countable_witnesses
    (S + integralRankOne μ ν) (lOneIndicator μ univ MeasurableSet.univ)
    (lOneIndicator_nonneg _ _)
  refine ⟨Wm ∪ Wp, hcm.union hcp, ?_⟩
  intro R J L hJ hone hinj habs hR hrank hW
  apply isSingularOperator_of_modulus_preserving_restriction S hS R J L hinj habs hR hrank
  · exact lOneOperatorModulus_comp_eq_of_witnesses _ J hJ hone Wm hWm hsm
      (fun _ h => hW (mem_union_left _ h))
  · exact lOneOperatorModulus_comp_eq_of_witnesses _ J hJ hone Wp hWp hsp
      (fun _ h => hW (mem_union_right _ h))

end ThesisCommon
