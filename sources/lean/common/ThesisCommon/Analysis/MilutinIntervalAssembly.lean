import ThesisCommon.Analysis.MilutinCantorAveraging
import ThesisCommon.Analysis.IntervalWeisAssembly

/-! The checked norm-one Milutin averaging lemma removes the independent
Milutin-isomorphism input from the C[0,1] assembly. The quantitative Weis
assertion remains explicit and unproved here. Its constant is preserved. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem FactorsIdentityWith.target_retract_contractively
    {E F Z W : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {T : E →L[𝕜] F} {C : ℝ} (h : FactorsIdentityWith T Z C)
    (A : Z →L[𝕜] W) (J : W →L[𝕜] Z) (hA : ‖A‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (hAJ : A.comp J = ContinuousLinearMap.id 𝕜 W) : FactorsIdentityWith T W C := by
  obtain ⟨U, V, hUV, hnorm⟩ := h
  refine ⟨A.comp U, V.comp J, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro w
    have hz := congrArg (fun L : Z →L[𝕜] Z => L (J w)) hUV
    change U (T (V (J w))) = J w at hz
    change A (U (T (V (J w)))) = w
    rw [hz]
    exact congrArg (fun L : W →L[𝕜] W => L w) hAJ
  · have hAU : ‖A.comp U‖ ≤ ‖U‖ := (ContinuousLinearMap.opNorm_comp_le A U).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (norm_nonneg U))
    have hVJ : ‖V.comp J‖ ≤ ‖V‖ := (ContinuousLinearMap.opNorm_comp_le V J).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hJ (norm_nonneg V))
    exact (mul_le_mul hAU hVJ (norm_nonneg _) (norm_nonneg _)).trans hnorm

theorem interval_hasCPFP_of_weis {C : ℝ} (hWeis : IntervalWeisBound 𝕜 C) :
    HasCPFP 𝕜 (IntervalContinuous 𝕜) C := by
  obtain ⟨q, _, A, hA, hAJ⟩ := milutin_binary_cantor_regular_averaging (𝕜 := 𝕜) UnitInterval
  intro T
  rcases interval_kernel_oscillation_continuity_dichotomy T with hT | hT
  · obtain ⟨t, ht, hc⟩ := hT
    exact Or.inl ((hWeis T t ht hc).target_retract_contractively A
      (continuousMapPullback q) hA.le (norm_continuousMapPullback_le q) hAJ)
  · obtain ⟨t, ht, hc⟩ := hT
    exact Or.inr ((hWeis _ t ht hc).target_retract_contractively A
      (continuousMapPullback q) hA.le (norm_continuousMapPullback_le q) hAJ)

theorem interval_hasUPFP_of_weis {C : ℝ} (hWeis : IntervalWeisBound 𝕜 C) :
    HasUPFP 𝕜 (IntervalContinuous 𝕜) := by
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro T
  rcases interval_hasCPFP_of_weis hWeis T with h | h
  · exact Or.inl (h.mono (le_max_right _ _))
  · exact Or.inr (h.mono (le_max_right _ _))

theorem interval_primary_of_weis {C : ℝ} (hWeis : IntervalWeisBound 𝕜 C) :
    IsPrimary 𝕜 (IntervalContinuous 𝕜) :=
  (interval_hasUPFP_of_weis hWeis).isPrimary_of_sequenceSelfSimilar interval_sequenceSelfSimilar

theorem interval_lp_upfp_primary_of_weis {C : ℝ}
    (hWeis : IntervalWeisBound 𝕜 C) (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) ∧
      IsPrimary 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) :=
  interval_lp_upfp_primary (interval_hasUPFP_of_weis hWeis) intervalCZeroEquiv p.val

end ThesisCommon
