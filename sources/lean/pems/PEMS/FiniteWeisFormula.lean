import PEMS.CountablyGeneratedWeisFormula
import PEMS.L1SubsigmaNoncompactness
import ThesisCommon.Analysis.L1SeparableReduction
import ThesisCommon.Analysis.IntegralKernelSubsigma
import ThesisCommon.Analysis.OperatorNormingSequence
import ThesisCommon.Analysis.L1AdjointOneKernel

/-! The real Weis norm and displayed essential-supremum formulas on arbitrary
finite measure spaces. Countable kernel generators and actual norming
vectors are retained in constructed singularity-preserving reductions.
No countable-generation assumption remains on the original spaces. -/
noncomputable section
open MeasureTheory MeasurableSpace Set ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem localizedWeakNoncompactness_le_of_subsigma_intertwines
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {m : MeasurableSpace X} {n : MeasurableSpace Y} (hm : m ≤ m₀) (hn : n ≤ n₀)
    (R : Lp ℝ 1 (μ.trim hm) →L[ℝ] Lp ℝ 1 (ν.trim hn))
    (hR : (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp R =
      T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) :
    localizedWeakNoncompactness R ≤ @localizedWeakNoncompactness ℝ _ X Y m₀ n₀ μ ν T := by
  have hmap : ∀ f, T (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n := by
    intro f
    have h := DFunLike.congr_fun hR f
    change lOneSubsigmaEmbedding ν hn (R f) = T (lOneSubsigmaEmbedding μ hm f) at h
    rw [← h]
    change lOneSubsigmaEmbedding ν hn (R f) ∈ (lOneSubsigma ν n : Set (Lp ℝ 1 ν))
    rw [← range_lOneSubsigmaEmbedding ν hn]
    exact mem_range_self (R f)
  have heq : lOneSubsigmaLift ν hn
      (T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap = R := by
    apply ContinuousLinearMap.ext
    intro f
    apply (lOneSubsigmaEmbedding ν hn).injective
    exact (DFunLike.congr_fun (lOneSubsigmaEmbedding_lift ν hn _ hmap) f).trans
      (DFunLike.congr_fun hR f).symm
  rw [← heq]
  exact localizedWeakNoncompactness_lOneSubsigmaLift_le T hm hn hmap

theorem truncationInf_le_localized_real_finite
    {k : X × Y → ℝ} (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    sInf (Set.range (fun j : ℕ => ‖S + hk.truncatedOperator j‖)) ≤
      localizedWeakNoncompactness (S + K) := by
  obtain ⟨C, hCc, hCm, hkC⟩ := exists_countable_left_generators_of_measurable hk.measurable
  obtain ⟨D, hDc, hDm, hkCD⟩ :=
    @exists_countable_right_generators_of_measurable X Y ℝ (generateFrom C) n₀
      (borel ℝ) _ k hkC
  have hC : generateFrom C ≤ m₀ := generateFrom_le hCm
  have hD : generateFrom D ≤ n₀ := generateFrom_le hDm
  have hCcg : @CountablyGenerated X (generateFrom C) :=
    @CountablyGenerated.mk X (generateFrom C) ⟨C, hCc, rfl⟩
  have hDcg : @CountablyGenerated Y (generateFrom D) :=
    @CountablyGenerated.mk Y (generateFrom D) ⟨D, hDc, rfl⟩
  choose f hf ht using fun j : ℕ => exists_operator_norming_sequence (S + hk.truncatedOperator j)
  obtain ⟨m, hm, n, hn, hCm', hDn', hmc, hnc, hM, _, hmapS, hsing⟩ :=
    @exists_countablyGenerated_singular_lOneSubsigma_reduction X Y m₀ n₀ μ ν _ _
      S hS (generateFrom C) hC hCcg (generateFrom D) hD hDcg
      (⋃ j : ℕ, range (f j)) (countable_iUnion (fun j => countable_range (f j))).isSeparable
      ∅ countable_empty.isSeparable
  have hkmn : @Measurable (X × Y) ℝ (m.prod n) (borel ℝ) k :=
    hkCD.mono (sup_le_sup (MeasurableSpace.comap_mono hCm')
      (MeasurableSpace.comap_mono hDn')) le_rfl
  obtain ⟨K', hk', hK', htr⟩ := hk.exists_subsigma_restriction hm hn hkmn
  let S' := lOneSubsigmaLift ν hn
    (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmapS
  have hS' : (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp S' =
      S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap :=
    lOneSubsigmaEmbedding_lift ν hn _ hmapS
  have hnorm (j : ℕ) : ‖S' + hk'.truncatedOperator j‖ =
      ‖S + @IsIntegralKernel.truncatedOperator X Y m₀ n₀ μ ν k K _ _ hk j‖ := by
    calc
      ‖S' + hk'.truncatedOperator j‖ =
          ‖(lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp
            (S' + hk'.truncatedOperator j)‖ :=
        (lOneSubsigmaEmbedding ν hn).norm_toContinuousLinearMap_comp.symm
      _ = ‖(S + @IsIntegralKernel.truncatedOperator X Y m₀ n₀ μ ν k K _ _ hk j).comp
          (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap‖ := by
        rw [ContinuousLinearMap.comp_add, hS', htr, ContinuousLinearMap.add_comp]
      _ = ‖S + @IsIntegralKernel.truncatedOperator X Y m₀ n₀ μ ν k K _ _ hk j‖ := by
        apply norm_comp_isometry_eq_of_norming_sequence _ (lOneSubsigmaEmbedding μ hm)
          (f j) (hf j) (ht j)
        intro l
        rw [range_lOneSubsigmaEmbedding]
        exact hM (mem_iUnion.mpr ⟨j, mem_range_self l⟩)
  have hR : (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp (S' + K') =
      (S + K).comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_add, hS', hK', ContinuousLinearMap.add_comp]
  have hphi := localizedWeakNoncompactness_le_of_subsigma_intertwines (S + K) hm hn (S' + K') hR
  have hformula := @real_countablyGenerated_weis_norm_formula X Y m n hmc hnc
    (μ.trim hm) (ν.trim hn) _ _ k S' K' hsing hk'
  have heq : localizedWeakNoncompactness (S' + K') =
      sInf (Set.range (fun j : ℕ =>
        ‖S + @IsIntegralKernel.truncatedOperator X Y m₀ n₀ μ ν k K _ _ hk j‖)) := by
    rw [← hformula.1, hformula.2]
    simp only [hnorm]
  exact heq.symm.trans_le hphi

theorem real_finite_weis_norm_formula
    {k : X × Y → ℝ} (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) =
      sInf (Set.range (fun j : ℕ => ‖S + hk.truncatedOperator j‖)) := by
  have h₁ := localizedWeakNoncompactness_le_weakEssentialNorm (S + K)
  have h₂ : weakEssentialNorm (S + K) ≤
      sInf (Set.range (fun j : ℕ => ‖S + hk.truncatedOperator j‖)) :=
    weakEssentialNorm_le_truncation_inf hk S
  have h₃ := truncationInf_le_localized_real_finite S K hS hk
  exact ⟨le_antisymm (h₂.trans h₃) h₁, le_antisymm h₂ (h₃.trans h₁)⟩

theorem weakEssentialNorm_eq_localized_real_finite
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨k, hk⟩ := integralBandProjection_isIntegral T
  have h := (real_finite_weis_norm_formula (T - integralBandProjection T)
    (integralBandProjection T) (integralBandProjection_residual_singular T) hk).1
  simpa only [sub_add_cancel] using h

theorem weakEssentialNorm_abs_real_finite (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    weakEssentialNorm |T| = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_finite, localizedWeakNoncompactness_abs,
    weakEssentialNorm_eq_localized_real_finite]

theorem real_finite_weis_essSup_formula
    {k : X × Y → ℝ} (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) = sInf (Set.range (fun j : ℕ =>
      essSup (fun x => positiveAdjointOne |S| (abs_nonneg S) x +
        ∫ y, |truncatedKernel (j : ℝ) k (x, y)| ∂ν) μ)) := by
  obtain ⟨hphi, hnorm⟩ := real_finite_weis_norm_formula S K hS hk
  exact ⟨hphi, hnorm.trans (congrArg sInf (congrArg Set.range (funext fun j =>
    singular_truncated_norm_eq_essSup_adjoint_column hk hS (j : ℝ))))⟩

end PEMS
