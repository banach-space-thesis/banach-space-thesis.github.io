import JFA.SeparableCZeroFactorization
import JFA.CZeroCompactApproximation
import JFA.RankOneIdeal
import JFA.AmplifiedCZeroRetracts

/-! Compact first factors through c₀ give finite sums of rank-one
approximants on the actual amplified space. Thus every nonzero closed
two-sided ideal contains the compact operators. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem czeroTruncation_factor_rankOne_sum (t : Finset ℕ)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E) :
    B.comp ((czeroTruncation t).comp A) =
      ∑ a ∈ t, ((czeroEvaluation (𝕜 := 𝕜) a).comp A).smulRight (B (czeroDelta a)) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, czeroTruncation,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    map_sum, map_smul]

theorem compact_factor_approximant_mem_ideal
    {I : Set (E →L[𝕜] E)} (hI : IsClosedOperatorIdeal 𝕜 E I)
    {Q : E →L[𝕜] E} (hQI : Q ∈ I) (hQ : Q ≠ 0)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E)
    (hA : IsCompactOperator A) (ε : ℝ) (hε : 0 < ε) :
    ∃ R ∈ I, ‖B.comp A - R‖ < ε := by
  classical
  have hd : 0 < ‖B‖ + 1 := by positivity
  let δ := ε / (‖B‖ + 1)
  have hδ : 0 < δ := div_pos hε hd
  obtain ⟨t, ht⟩ := exists_czeroTruncation_compact_approx A hA δ hδ
  let W : Submodule 𝕜 (E →L[𝕜] E) := {
    carrier := I
    zero_mem' := hI.2.1
    add_mem' := fun hS hT => hI.2.2.1 _ hS _ hT
    smul_mem' := fun a T hT => hI.2.2.2.1 a T hT }
  refine ⟨B.comp ((czeroTruncation t).comp A), ?_, ?_⟩
  · change B.comp ((czeroTruncation t).comp A) ∈ W
    rw [czeroTruncation_factor_rankOne_sum]
    apply W.sum_mem
    intro a ha
    exact smulRight_mem_ideal_of_ne_zero hI hQI hQ _ _
  · rw [← ContinuousLinearMap.comp_sub]
    calc
      ‖B.comp (A - (czeroTruncation t).comp A)‖ ≤
          ‖B‖ * ‖A - (czeroTruncation t).comp A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ * δ := mul_le_mul_of_nonneg_left ht.le (norm_nonneg B)
      _ < (‖B‖ + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε := by dsimp [δ]; field_simp

variable {𝒜 : Set (Set ℕ)}

theorem amplified_compactOperators_minimal (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)}
    (hI : IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I) (hIne : I ≠ {0}) :
    compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I := by
  classical
  have hex : ∃ Q ∈ I, Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hIne
    apply subset_antisymm
    · intro Q hQ
      exact mem_singleton_iff.mpr (h Q hQ)
    · intro Q hQ
      rw [mem_singleton_iff] at hQ
      exact hQ.symm ▸ hI.2.1
  obtain ⟨Q, hQI, hQ⟩ := hex
  intro T hT
  obtain ⟨A, B, hAB, hc⟩ := amplified_separable_factors_cZero h𝒜 T
    (hasSeparableRange_of_isCompactOperator T hT)
  have hclosure : T ∈ closure I := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨R, hRI, hR⟩ := compact_factor_approximant_mem_ideal hI hQI hQ A B (hc hT) ε hε
    refine ⟨R, hRI, ?_⟩
    simpa only [hAB, dist_eq_norm] using hR
  rwa [hI.1.closure_eq] at hclosure

theorem amplified_zero_strictly_below_compact (h𝒜 : IsAlmostDisjoint 𝒜) :
    ({0} : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)) ⊂
      compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) := by
  obtain ⟨A, B, hBA, _, _⟩ := amplified_exists_cZero_retract (𝕜 := 𝕜) h𝒜
  let v := A (czeroDelta 0)
  let η := (czeroEvaluation (𝕜 := 𝕜) 0).comp B
  have hη : η v = 1 := by
    have h := congrArg (fun L => L (czeroDelta 0)) hBA
    change B (A (czeroDelta 0)) = czeroDelta 0 at h
    change B (A (czeroDelta 0)) 0 = 1
    rw [h, czeroDelta_apply]
    simp
  have hv : v ≠ 0 := by
    intro h
    have hh := hη
    rw [h, map_zero] at hh
    exact zero_ne_one hh
  let P := η.smulRight v
  have hP : P ∈ compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) := JLMS.isCompactOperator_smulRight _ _
  have hPne : P ≠ 0 := by
    intro h
    have hh := congrArg (fun L : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜 => L v) h
    change η v • v = 0 at hh
    rw [hη, one_smul] at hh
    exact hv hh
  refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro T hT
    rw [mem_singleton_iff] at hT
    exact hT.symm ▸ isCompactOperator_zero
  · intro heq
    exact hPne (mem_singleton_iff.mp (heq.symm ▸ hP))

end JFA
