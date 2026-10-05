import ThesisCommon.Analysis.OscillationCalculus
import ThesisCommon.Analysis.ContinuousMapEvaluationDistance
import ThesisCommon.Analysis.UnitIntervalClosedCopies
import ThesisCommon.Analysis.SemicontinuousBaire

/-! The norm oscillation of the representing dual kernel of a C[0,1]
operator. The identity has oscillation two; subadditivity and Baire
then select a closed nondegenerate interval with oscillation at least one
for T or I-T. This does not assert the subsequent Weis factorization. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalOperatorKernel (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (t : UnitInterval) : IntervalContinuous 𝕜 →L[𝕜] 𝕜 :=
  (ContinuousMap.evalCLM 𝕜 t).comp T

theorem intervalOperatorKernel_add (T S : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (t : UnitInterval) : intervalOperatorKernel (T+S) t =
      intervalOperatorKernel T t + intervalOperatorKernel S t := by
  ext f
  rfl

theorem intervalOperatorKernel_id (t : UnitInterval) :
    intervalOperatorKernel (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜)) t =
      ContinuousMap.evalCLM 𝕜 t := by
  ext f
  rfl

theorem interval_identity_oscillation (t : UnitInterval) :
    oscillation (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜))) t = 2 := by
  have hk : intervalOperatorKernel (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜)) =
      fun s => ContinuousMap.evalCLM (M := 𝕜) 𝕜 s := by
    funext s
    exact intervalOperatorKernel_id s
  rw [hk]
  rw [oscillation_eq_iInf_image]
  apply le_antisymm
  · apply (show (⨅ U ∈ 𝓝 t, EMetric.diam ((fun s => ContinuousMap.evalCLM (M := 𝕜) 𝕜 s) '' U)) ≤
        EMetric.diam ((fun s : UnitInterval => ContinuousMap.evalCLM (M := 𝕜) 𝕜 s) '' Set.univ) from
      iInf_le_of_le Set.univ (iInf_le_of_le (Filter.univ_mem : Set.univ ∈ 𝓝 t) le_rfl)).trans
    apply EMetric.diam_image_le_iff.2
    intro a ha b hb
    by_cases hab : a = b
    · simp [hab]
    · rw [edist_dist, dist_eq_norm (ContinuousMap.evalCLM (M := 𝕜) 𝕜 a)
        (ContinuousMap.evalCLM (M := 𝕜) 𝕜 b), norm_continuousMap_eval_sub a b hab]
      norm_num
  · apply le_iInf
    intro U
    apply le_iInf
    intro hU
    obtain ⟨V, hVU, hV, ht⟩ := mem_nhds_iff.1 hU
    obtain ⟨a, b, hab, habV⟩ := hV.exists_Ioo_subset ⟨t, ht⟩
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    obtain ⟨d, hcd, hdb⟩ := exists_between hcb
    have hc : c ∈ U := hVU (habV ⟨hac, hcb⟩)
    have hd : d ∈ U := hVU (habV ⟨hac.trans hcd, hdb⟩)
    have hdist : edist (ContinuousMap.evalCLM (M := 𝕜) 𝕜 c)
        (ContinuousMap.evalCLM (M := 𝕜) 𝕜 d) = 2 := by
      rw [edist_dist, dist_eq_norm (ContinuousMap.evalCLM (M := 𝕜) 𝕜 c)
        (ContinuousMap.evalCLM (M := 𝕜) 𝕜 d), norm_continuousMap_eval_sub c d (ne_of_lt hcd)]
      norm_num
    rw [← hdist]
    exact EMetric.edist_le_diam_of_mem (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd)

theorem interval_kernel_oscillation_dichotomy
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    1 ≤ oscillation (intervalOperatorKernel T) t ∨
      1 ≤ oscillation (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T)) t := by
  have h := oscillation_add_le (intervalOperatorKernel T)
    (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T)) t
  have heq : (fun s => intervalOperatorKernel T s +
      intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T) s) =
      intervalOperatorKernel (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜)) := by
    funext s
    rw [← intervalOperatorKernel_add]
    have ht : T + (ContinuousLinearMap.id 𝕜 _ - T) = ContinuousLinearMap.id 𝕜 _ := by abel
    rw [ht]
  rw [heq, interval_identity_oscillation] at h
  by_contra hn
  push_neg at hn
  have hlt := ENNReal.add_lt_add hn.1 hn.2
  norm_num at hlt
  exact (not_lt_of_ge h) hlt

theorem interval_kernel_oscillation_interval
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    ∃ (a b : UnitInterval), a < b ∧
      ((∀ t ∈ Set.Icc a b, 1 ≤ oscillation (intervalOperatorKernel T) t) ∨
       (∀ t ∈ Set.Icc a b, 1 ≤ oscillation
         (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T)) t)) := by
  let A : Bool → Set UnitInterval := fun k =>
    {t | 1 ≤ oscillation (intervalOperatorKernel (if k then T else ContinuousLinearMap.id 𝕜 _ - T)) t}
  have hA : ∀ k, IsClosed (A k) := fun k =>
    (upperSemicontinuous_oscillation _).isClosed_preimage 1
  have hcover : ⋃ k, A k = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    rcases interval_kernel_oscillation_dichotomy T t with ht | ht
    · exact Set.mem_iUnion.2 ⟨true, ht⟩
    · exact Set.mem_iUnion.2 ⟨false, ht⟩
  obtain ⟨k, a, b, hab, hsub⟩ := unitInterval_closed_cover_contains_interval A hA hcover
  refine ⟨a, b, hab, ?_⟩
  cases k
  · exact Or.inr (fun t ht => hsub ht)
  · exact Or.inl (fun t ht => hsub ht)

theorem interval_kernel_oscillation_continuity_dichotomy
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    (∃ t, 1 ≤ oscillation (intervalOperatorKernel T) t ∧
      ContinuousAt (oscillation (intervalOperatorKernel T)) t) ∨
    (∃ t, 1 ≤ oscillation (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T)) t ∧
      ContinuousAt (oscillation (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T))) t) := by
  obtain ⟨a, b, hab, hT | hT⟩ := interval_kernel_oscillation_interval T
  · obtain ⟨t, ht, hc⟩ := upperSemicontinuous_ennreal_exists_continuity_point
      (upperSemicontinuous_oscillation (intervalOperatorKernel T))
      isOpen_Ioo (Set.nonempty_Ioo.2 hab)
    exact Or.inl ⟨t, hT t (Set.Ioo_subset_Icc_self ht), hc⟩
  · obtain ⟨t, ht, hc⟩ := upperSemicontinuous_ennreal_exists_continuity_point
      (upperSemicontinuous_oscillation (intervalOperatorKernel (ContinuousLinearMap.id 𝕜 _ - T)))
      isOpen_Ioo (Set.nonempty_Ioo.2 hab)
    exact Or.inr ⟨t, hT t (Set.Ioo_subset_Icc_self ht), hc⟩

end ThesisCommon
