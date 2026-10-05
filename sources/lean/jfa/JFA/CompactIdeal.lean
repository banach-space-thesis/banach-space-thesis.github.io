import JFA.SeparableIdeal

/-! Compact operators and factorisations through separable spaces give the
ideal inclusions used in Theorem 1.6. These results concern the actual ranges
and operator norm, including the algebraic span in the factorisation ideal. -/

noncomputable section
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem zeroOperators_closedIdeal :
    IsClosedOperatorIdeal 𝕜 E ({0} : Set (E →L[𝕜] E)) := by
  refine ⟨isClosed_singleton, mem_singleton _, ?_, ?_, ?_⟩
  · intro S hS T hT
    simp_all only [mem_singleton_iff, add_zero]
  · intro a T hT
    simp_all only [mem_singleton_iff, smul_zero]
  · intro A T hT
    simp_all only [mem_singleton_iff, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, and_self]

theorem allOperators_closedIdeal :
    IsClosedOperatorIdeal 𝕜 E (Set.univ : Set (E →L[𝕜] E)) :=
  ⟨isClosed_univ, mem_univ _, fun _ _ _ _ => mem_univ _,
    fun _ _ _ => mem_univ _, fun _ _ _ => ⟨mem_univ _, mem_univ _⟩⟩

theorem compactOperators_closedIdeal [CompleteSpace E] :
    IsClosedOperatorIdeal 𝕜 E (compactOperators 𝕜 E) := by
  refine ⟨isClosed_setOf_isCompactOperator, isCompactOperator_zero, ?_, ?_, ?_⟩
  · intro S hS T hT
    exact hS.add hT
  · intro a T hT
    exact hT.smul a
  · intro A T hT
    exact ⟨hT.clm_comp A, hT.comp_clm A⟩

/-- A compact operator has separable range even when its source is nonseparable. -/
theorem hasSeparableRange_of_isCompactOperator (T : E →L[𝕜] F)
    (hT : IsCompactOperator T) : HasSeparableRange 𝕜 E F T := by
  have hlin : IsCompactOperator T.toLinearMap := hT
  have hs : IsSeparable (⋃ n : ℕ,
      closure (T.toLinearMap '' Metric.closedBall (0 : E) (n : ℝ))) :=
    IsSeparable.iUnion (fun n => (hlin.isCompact_closure_image_closedBall (n : ℝ)).isSeparable)
  apply hs.mono
  rintro y ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  apply mem_iUnion.mpr
  refine ⟨n, subset_closure ?_⟩
  exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn, rfl⟩

theorem compactOperators_subset_separableOperators :
    compactOperators 𝕜 E ⊆ separableOperators 𝕜 E := by
  intro T hT
  exact hasSeparableRange_of_isCompactOperator T hT

theorem factorizationOperators_subset_separableOperators [SeparableSpace F] :
    factorizationOperators 𝕜 E F ⊆ separableOperators 𝕜 E := by
  have hle : factorizationSpan 𝕜 E F ≤ separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E) := by
    apply Submodule.span_le.mpr
    rintro T ⟨A, B, rfl⟩
    have hB : HasSeparableRange 𝕜 F E B := isSeparable_range B.continuous
    exact hB.comp_right A
  exact hle

theorem closure_factorizationOperators_subset_separableOperators [SeparableSpace F] :
    closure (factorizationOperators 𝕜 E F) ⊆ separableOperators 𝕜 E :=
  closure_minimal factorizationOperators_subset_separableOperators isClosed_separableOperators

end JFA
