import ThesisCommon.Analysis.CompactConvexOperatorFixedPoint
import ThesisCommon.Analysis.FiniteAbsoluteConvexOrbitCompact
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Kakutani's operator conclusion for genuine operators between different
spaces. The compact-convex step reduces to the already checked endomorphism
theorem on the product space. This applies in particular to operators defined
on an actual Gowers--Maurey subspace. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 E F V ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def rectangularOperatorLift : (E →L[𝕜] F) →L[𝕜] (E × F →L[𝕜] E × F) :=
  (ContinuousLinearMap.compL 𝕜 (E × F) F (E × F)
    (ContinuousLinearMap.inr 𝕜 E F)).comp
      ((ContinuousLinearMap.compL 𝕜 (E × F) E F).flip
        (ContinuousLinearMap.fst 𝕜 E F))

@[simp] theorem rectangularOperatorLift_apply (T : E →L[𝕜] F) (z : E × F) :
    rectangularOperatorLift T z = (0, T z.1) := rfl

theorem norm_rectangularOperatorLift_apply (T : E →L[𝕜] F) (z : E × F) :
    ‖rectangularOperatorLift T z‖ = ‖T z.1‖ := by
  simp [Prod.norm_def]

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

theorem compact_convex_rectangular_operator_fixed_point
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Set V) (hA : Convex ℝ A) (hcompact : IsCompact A) (hne : A.Nonempty)
    (L : V →L[ℝ] (E →L[𝕜] F)) (T : E →L[𝕜] F)
    (y : A → E) (hy : Continuous y) (r : ℝ)
    (hlocal : ∀ u : A, ∃ v ∈ A, ‖(T - L v) (y u)‖ ≤ r) :
    ∃ u : A, ‖(T - L u.val) (y u)‖ ≤ r := by
  let L' := (rectangularOperatorLift (𝕜 := 𝕜) (E := E) (F := F)).restrictScalars ℝ
  let z : A → E × F := fun u => (y u, 0)
  have hz : Continuous z := hy.prodMk continuous_const
  have hlocal' : ∀ u : A, ∃ v ∈ A,
      ‖(rectangularOperatorLift T - (L'.comp L) v) (z u)‖ ≤ r := by
    intro u
    obtain ⟨v, hv, hbound⟩ := hlocal u
    refine ⟨v, hv, ?_⟩
    change ‖(rectangularOperatorLift T - rectangularOperatorLift (L v)) (y u, 0)‖ ≤ r
    rw [← map_sub, norm_rectangularOperatorLift_apply]
    exact hbound
  obtain ⟨u, hu⟩ := compact_convex_operator_fixed_point A hA hcompact hne
    (L'.comp L) (rectangularOperatorLift T) z hz r hlocal'
  refine ⟨u, ?_⟩
  change ‖(rectangularOperatorLift T - rectangularOperatorLift (L u.val)) (y u, 0)‖ ≤ r at hu
  rw [← map_sub, norm_rectangularOperatorLift_apply] at hu
  exact hu

theorem finite_rectangular_operator_orbit_fixed_point [Fintype ι]
    (U : ι → E →L[𝕜] F) (m : ℝ) (hm : 0 ≤ m) (T : E →L[𝕜] F)
    (y : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m → E) (hy : Continuous y) (r : ℝ)
    (hlocal : ∀ u : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m,
      ∃ v ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, ‖(T - v) (y u)‖ ≤ r) :
    ∃ u : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, ‖(T - u.val) (y u)‖ ≤ r := by
  let V : Submodule 𝕜 (E →L[𝕜] F) := Submodule.span 𝕜 (Set.range U)
  haveI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range U)
  haveI : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ 𝕜 V
  have hmem : ∀ v ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m, v ∈ V := by
    rintro v ⟨c, _, rfl⟩
    apply Submodule.sum_mem
    intro i hi
    exact V.smul_mem (c i) (Submodule.subset_span (Set.mem_range_self i))
  let A : Set V := {u | u.val ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m}
  have hA : Convex ℝ A := by
    rintro u hu v hv a b ha hb hab
    exact convex_finiteAbsoluteConvexOrbit U m hu hv ha hb hab
  have hcompact : IsCompact A :=
    (V.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal).isCompact_preimage
      (isCompact_finiteAbsoluteConvexOrbit U m)
  have hne : A.Nonempty := ⟨0, zero_mem_finiteAbsoluteConvexOrbit U hm⟩
  let q : A → finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m :=
    fun u => ⟨u.val.val, u.property⟩
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hlocal' : ∀ u : A, ∃ v ∈ A,
      ‖(T - (V.subtypeL.restrictScalars ℝ) v) ((y ∘ q) u)‖ ≤ r := by
    intro u
    obtain ⟨v, hv, hbound⟩ := hlocal (q u)
    exact ⟨⟨v, hmem v hv⟩, hv, hbound⟩
  obtain ⟨u, hu⟩ := compact_convex_rectangular_operator_fixed_point A hA hcompact hne
    (V.subtypeL.restrictScalars ℝ) T (y ∘ q) (hy.comp hq) r hlocal'
  exact ⟨q u, hu⟩

end ThesisCommon
