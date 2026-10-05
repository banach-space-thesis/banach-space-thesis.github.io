import JFA.CZeroCompactApproximation
import JFA.RankOneIdeal
import JFA.CZeroFactorization

/-! The closed two-sided ideals of the actual scalar c₀ space are exactly
zero, the compact operators, and all operators. Finite coordinate
approximations prove minimality of the compact ideal; the checked scattered-C₀
factorisation puts the identity in every ideal with a noncompact member. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

theorem czeroTruncation_comp (t : Finset ℕ) (T : cZero 𝕜 →L[𝕜] cZero 𝕜) :
    (czeroTruncation t).comp T =
      ∑ a ∈ t, ((czeroEvaluation (𝕜 := 𝕜) a).comp T).smulRight (czeroDelta a) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro b
  simp only [czeroTruncation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, czero_sum_apply, ContinuousLinearMap.smulRight_apply]

theorem cZero_compactOperators_minimal
    {I : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)}
    (hI : IsClosedOperatorIdeal 𝕜 (cZero 𝕜) I) (hIne : I ≠ {0}) :
    compactOperators 𝕜 (cZero 𝕜) ⊆ I := by
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
  let W : Submodule 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) := {
    carrier := I
    zero_mem' := hI.2.1
    add_mem' := fun hS hT => hI.2.2.1 _ hS _ hT
    smul_mem' := fun a T hT => hI.2.2.2.1 a T hT }
  intro T hT
  have hclosure : T ∈ closure I := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := exists_czeroTruncation_compact_approx T hT ε hε
    refine ⟨(czeroTruncation t).comp T, ?_, ?_⟩
    · change (czeroTruncation t).comp T ∈ W
      rw [czeroTruncation_comp]
      apply W.sum_mem
      intro a ha
      exact smulRight_mem_ideal_of_ne_zero hI hQI hQ _ _
    · simpa only [dist_eq_norm] using ht
  rwa [hI.1.closure_eq] at hclosure

theorem cZero_noncompact_factors_identity (T : cZero 𝕜 →L[𝕜] cZero 𝕜)
    (hT : ¬ IsCompactOperator T) :
    ∃ U V : cZero 𝕜 →L[𝕜] cZero 𝕜,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  have hsc : JLMS.IsScattered ℕ := discrete_isScattered
  obtain ⟨U, V, hUV, _⟩ := JLMS.theorem_1_6_of_scatteredCZero
    (𝕜 := 𝕜) (K := ℕ) (L := ℕ) hsc hsc (JLMS.cZero_admissible hsc) T hT 1 zero_lt_one
  exact ⟨U, V, hUV⟩

theorem cZero_closedIdeal_classification (I : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) :
    IsClosedOperatorIdeal 𝕜 (cZero 𝕜) I ↔
      I = {0} ∨ I = compactOperators 𝕜 (cZero 𝕜) ∨ I = Set.univ := by
  classical
  constructor
  · intro hI
    by_cases hI0 : I = {0}
    · exact Or.inl hI0
    right
    by_cases hIK : I ⊆ compactOperators 𝕜 (cZero 𝕜)
    · exact Or.inl (subset_antisymm hIK (cZero_compactOperators_minimal hI hI0))
    · right
      obtain ⟨T, hTI, hT⟩ := Set.not_subset.mp hIK
      obtain ⟨U, V, hUV⟩ := cZero_noncompact_factors_identity T hT
      have hmul := hI.2.2.2.2
      have hid : ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∈ I :=
        hUV ▸ (hmul V (U.comp T) (hmul U T hTI).1).2
      apply Set.eq_univ_of_forall
      intro A
      simpa only [ContinuousLinearMap.comp_id] using (hmul A _ hid).1
  · rintro (rfl | rfl | rfl)
    · exact zeroOperators_closedIdeal
    · exact compactOperators_closedIdeal
    · exact allOperators_closedIdeal

theorem cZero_compact_ideal_strict :
    ({0} : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) ⊂ compactOperators 𝕜 (cZero 𝕜) ∧
      compactOperators 𝕜 (cZero 𝕜) ⊂ Set.univ := by
  let P : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
    (czeroEvaluation (𝕜 := 𝕜) 0).smulRight (czeroDelta 0)
  have hP : P ∈ compactOperators 𝕜 (cZero 𝕜) := JLMS.isCompactOperator_smulRight _ _
  have hPne : P ≠ 0 := by
    intro h
    have he := congrArg (fun Q : cZero 𝕜 →L[𝕜] cZero 𝕜 => Q (czeroDelta 0) 0) h
    simp [P, czeroEvaluation, czeroDelta_apply,
      ZeroAtInftyContinuousMap.smul_apply] at he
  have hidnot : ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∉ compactOperators 𝕜 (cZero 𝕜) :=
    fun h => JLMS.cZero_not_finiteDimensional 𝕜 (JLMS.finiteDimensional_of_compact_identity h)
  constructor
  · refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro T hT
      rw [mem_singleton_iff] at hT
      exact hT.symm ▸ isCompactOperator_zero
    · intro heq
      exact hPne (mem_singleton_iff.mp (heq.symm ▸ hP))
  · refine ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
    intro heq
    exact hidnot (heq.symm ▸ mem_univ _)

end JFA
