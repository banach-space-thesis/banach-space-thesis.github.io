import ThesisCommon.Analysis.L1WeakUniformTight

/-! Every weakly compact operator into real L1 has its range supported on
one measurable sigma-finite part. The source can be any real normed space,
and the output measure is arbitrary. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {Y E : Type*} [MeasurableSpace Y] {ν : Measure Y}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsWeaklyCompactOperator.exists_sigmaFinite_range_part
    {T : E →L[ℝ] Lp ℝ 1 ν} (hT : IsWeaklyCompactOperator T) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  have hpos (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity
  choose A hA hfin hcut using fun n =>
    hT.exists_finite_measure_cut_compl_norm_le (hpos n)
  let Θ : Set Y := ⋃ n, A n
  have hΘ : MeasurableSet Θ := MeasurableSet.iUnion hA
  have hσ : SigmaFinite (ν.restrict Θ) := by
    refine ⟨⟨⟨fun n => A n ∪ Θᶜ, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hA n).union hΘ.compl)]
      apply lt_of_le_of_lt (measure_mono ?_) (hfin n)
      intro y hy
      exact hy.1.elim id (fun h => False.elim (h hy.2))
    · ext y
      simp only [mem_iUnion, mem_union, mem_compl_iff, mem_univ, iff_true]
      by_cases hy : y ∈ Θ
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hy
        exact ⟨n, Or.inl hn⟩
      · exact ⟨0, Or.inr hy⟩
  refine ⟨Θ, hΘ, hσ, fun f => ?_⟩
  have hn (n : ℕ) : ‖lpCut Θᶜ hΘ.compl (T f)‖ ≤
      ((1 : ℝ) / (n + 1)) * ‖f‖ := by
    have hm : ‖lpCut Θᶜ hΘ.compl (T f)‖ ≤
        ‖lpCut (A n)ᶜ (hA n).compl (T f)‖ := by
      rw [norm_lOneCut_eq_integral, norm_lOneCut_eq_integral]
      exact setIntegral_mono_set (L1.integrable_coeFn (T f)).norm.integrableOn
        (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall
          (compl_subset_compl.mpr (subset_iUnion A n)))
    exact hm.trans (((lpCutL (A n)ᶜ (hA n).compl).comp T).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right (hcut n) (norm_nonneg f)))
  have hzero : lpCut Θᶜ hΘ.compl (T f) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖f‖
    simpa only [zero_mul] using ge_of_tendsto ht (Eventually.of_forall hn)
  have hae := Lp.ext_iff.mp hzero
  change ∀ᵐ y ∂ν.restrict Θᶜ, T f y = 0
  rw [ae_restrict_iff' hΘ.compl]
  filter_upwards [hae, lpCut_coe Θᶜ hΘ.compl (T f), Lp.coeFn_zero ℝ 1 ν]
    with y hy hc hz
  intro hyΘ
  simpa only [hc, hz, indicator_of_mem hyΘ, Pi.zero_apply] using hy

end ThesisCommon
