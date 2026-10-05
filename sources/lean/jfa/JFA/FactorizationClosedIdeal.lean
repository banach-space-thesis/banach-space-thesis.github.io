import JFA.CompactIdeal

/-! The algebraic span of factorisations is two-sided, and its norm closure
is a closed operator ideal. A complemented intermediate space gives inclusion
of factorisation ideals by inserting its two retract maps. -/

noncomputable section
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem factorizationOperators_comp_left (A : E →L[𝕜] E)
    {T : E →L[𝕜] E} (hT : T ∈ factorizationOperators 𝕜 E F) :
    A.comp T ∈ factorizationOperators 𝕜 E F := by
  change T ∈ factorizationSpan 𝕜 E F at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨U, V, rfl⟩ := hT
    exact Submodule.subset_span ⟨U, A.comp V, ContinuousLinearMap.comp_assoc _ _ _⟩
  | zero => simpa only [ContinuousLinearMap.comp_zero] using (factorizationSpan 𝕜 E F).zero_mem
  | add S T _ _ hS hT =>
    rw [ContinuousLinearMap.comp_add]
    exact (factorizationSpan 𝕜 E F).add_mem hS hT
  | smul a T _ hT =>
    rw [ContinuousLinearMap.comp_smul]
    exact (factorizationSpan 𝕜 E F).smul_mem a hT

theorem factorizationOperators_comp_right (A : E →L[𝕜] E)
    {T : E →L[𝕜] E} (hT : T ∈ factorizationOperators 𝕜 E F) :
    T.comp A ∈ factorizationOperators 𝕜 E F := by
  change T ∈ factorizationSpan 𝕜 E F at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨U, V, rfl⟩ := hT
    exact Submodule.subset_span ⟨U.comp A, V, (ContinuousLinearMap.comp_assoc _ _ _).symm⟩
  | zero => simpa only [ContinuousLinearMap.zero_comp] using (factorizationSpan 𝕜 E F).zero_mem
  | add S T _ _ hS hT =>
    rw [ContinuousLinearMap.add_comp]
    exact (factorizationSpan 𝕜 E F).add_mem hS hT
  | smul a T _ hT =>
    rw [ContinuousLinearMap.smul_comp]
    exact (factorizationSpan 𝕜 E F).smul_mem a hT

theorem closure_factorizationOperators_closedIdeal :
    IsClosedOperatorIdeal 𝕜 E (closure (factorizationOperators 𝕜 E F)) := by
  let W := (factorizationSpan 𝕜 E F).topologicalClosure
  refine ⟨isClosed_closure, W.zero_mem, ?_, ?_, ?_⟩
  · intro S hS T hT
    exact W.add_mem hS hT
  · intro a T hT
    exact W.smul_mem a hT
  · intro A T hT
    constructor
    · exact (Set.MapsTo.closure (fun Q hQ => factorizationOperators_comp_left A hQ)
        ((ContinuousLinearMap.compL 𝕜 E E E) A).continuous) hT
    · exact (Set.MapsTo.closure (fun Q hQ => factorizationOperators_comp_right A hQ)
        ((ContinuousLinearMap.compL 𝕜 E E E).flip A).continuous) hT

theorem factorizationOperators_subset_of_retract (U : F →L[𝕜] G) (V : G →L[𝕜] F)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 F) :
    factorizationOperators 𝕜 E F ⊆ factorizationOperators 𝕜 E G := by
  apply Submodule.span_le.mpr
  rintro T ⟨A, B, rfl⟩
  apply Submodule.subset_span
  refine ⟨U.comp A, B.comp V, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun L => L (A x)) hVU
  change V (U (A x)) = A x at hx
  change B (A x) = B (V (U (A x)))
  rw [hx]

end JFA
