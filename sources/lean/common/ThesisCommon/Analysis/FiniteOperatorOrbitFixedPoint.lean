import ThesisCommon.Analysis.CompactConvexOperatorFixedPoint
import ThesisCommon.Analysis.FiniteAbsoluteConvexOrbitCompact

/-! Kakutani's diagonal conclusion on the actual finite absolute-convex
operator orbit. Finite dimensionality is proved from its generators;
the ambient operator algebra may be infinite-dimensional. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [Fintype ι]

theorem finite_operator_orbit_fixed_point
    (U : ι → X →L[𝕜] X) (m : ℝ) (hm : 0 ≤ m) (T : X →L[𝕜] X)
    (y : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m → X) (hy : Continuous y) (r : ℝ)
    (hlocal : ∀ u : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m,
      ∃ v ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, ‖(T - v) (y u)‖ ≤ r) :
    ∃ u : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, ‖(T - u.val) (y u)‖ ≤ r := by
  let E : Submodule 𝕜 (X →L[𝕜] X) := Submodule.span 𝕜 (Set.range U)
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range U)
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ 𝕜 E
  have hmem : ∀ v ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, v ∈ E := by
    rintro v ⟨c, _, rfl⟩
    apply Submodule.sum_mem
    intro i hi
    exact E.smul_mem (c i) (Submodule.subset_span (Set.mem_range_self i))
  let A : Set E := {u | u.val ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m}
  have hA : Convex ℝ A := by
    rintro u hu v hv a b ha hb hab
    exact convex_finiteAbsoluteConvexOrbit U m hu hv ha hb hab
  have hcompact : IsCompact A :=
    (E.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal).isCompact_preimage
      (isCompact_finiteAbsoluteConvexOrbit U m)
  have hne : A.Nonempty :=
    ⟨0, zero_mem_finiteAbsoluteConvexOrbit U hm⟩
  let q : A → finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m :=
    fun u => ⟨u.val.val, u.property⟩
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hlocal' : ∀ u : A, ∃ v ∈ A,
      ‖(T - (E.subtypeL.restrictScalars ℝ) v) ((y ∘ q) u)‖ ≤ r := by
    intro u
    obtain ⟨v, hv, hbound⟩ := hlocal (q u)
    exact ⟨⟨v, hmem v hv⟩, hv, hbound⟩
  obtain ⟨u, hu⟩ := compact_convex_operator_fixed_point A hA hcompact hne
    (E.subtypeL.restrictScalars ℝ) T (y ∘ q) (hy.comp hq) r hlocal'
  exact ⟨q u, hu⟩

end ThesisCommon
