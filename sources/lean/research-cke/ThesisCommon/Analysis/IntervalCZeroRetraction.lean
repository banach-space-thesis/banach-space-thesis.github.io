import ThesisCommon.Analysis.IntervalWindowRead
import ThesisCommon.Analysis.IntervalWindowInsert

/-! The actual complemented c0(C[0,1]) copy inside C[0,1]. Disjoint
windows and cutoff identities make the read/insert composition exactly
the identity on every null sequence. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem intervalAnchor_comp_windowInsert (n : ℕ) :
    (intervalAnchor (𝕜 := 𝕜)).comp (intervalWindowInsert n) = 0 := by
  ext f t
  exact intervalWindowInsert_zero n f (zero_not_mem_intervalWindowOpen n)

theorem intervalRead_comp_windowInsert_off {m n : ℕ} (hmn : m ≠ n) :
    (intervalRead (𝕜 := 𝕜) (intervalWindow m)).comp (intervalWindowInsert n) = 0 := by
  ext f t
  let e := unitSubintervalHomeomorph (intervalWindowLeft m) (intervalWindowRight m) (intervalWindow m).property
  change intervalWindowInsert n f (e t).val = 0
  apply intervalWindowInsert_zero
  exact fun hn => Set.disjoint_left.1 (intervalWindowOpen_disjoint hmn)
    (intervalWindow_subset_open m (e t).property) hn

theorem intervalWindowRead_comp_windowInsert (m n : ℕ) :
    (intervalWindowRead (𝕜 := 𝕜) m).comp (intervalWindowInsert n) =
      if m = n then ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) else 0 := by
  ext f t
  have hz := intervalWindowInsert_zero n f (zero_not_mem_intervalWindowOpen n)
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    change intervalRead (intervalWindow n) (intervalWindowInsert n f) t - intervalWindowInsert n f 0 = f t
    rw [hz, sub_zero]
    exact congrArg (fun A : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 => A f t)
      (intervalRead_windowInsert n)
  · rw [if_neg hmn]
    change intervalRead (intervalWindow m) (intervalWindowInsert n f) t - intervalWindowInsert n f 0 = 0
    rw [hz, sub_zero]
    exact congrArg (fun A : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 => A f t)
      (intervalRead_comp_windowInsert_off hmn)

theorem intervalCZeroRead_comp_insert :
    (intervalCZeroRead (𝕜 := 𝕜)).comp (intervalCZeroInsert (𝕜 := 𝕜)) =
      ContinuousLinearMap.id 𝕜 (CZeroSum (IntervalContinuous 𝕜)) := by
  ext x n t
  have hs : Summable (fun i => intervalWindowInsert i (x i)) :=
    cZero_columns_summable (intervalWindowInsert (𝕜 := 𝕜)) zero_le_one
      (continuousMap_disjoint_finiteColumnBound (intervalWindowInsert (𝕜 := 𝕜))
        (norm_intervalWindowInsert_le (𝕜 := 𝕜)) (intervalWindowInsert_disjoint (𝕜 := 𝕜))) x
  have h : intervalWindowRead n (∑' i, intervalWindowInsert i (x i)) = x n := by
    rw [(intervalWindowRead (𝕜 := 𝕜) n).map_tsum hs, tsum_eq_single n]
    · rw [← ContinuousLinearMap.comp_apply, intervalWindowRead_comp_windowInsert, if_pos rfl,
        ContinuousLinearMap.id_apply]
    · intro i hin
      rw [← ContinuousLinearMap.comp_apply, intervalWindowRead_comp_windowInsert, if_neg hin.symm,
        ContinuousLinearMap.zero_apply]
  exact congrArg (fun f : IntervalContinuous 𝕜 => f t) h

end ThesisCommon
