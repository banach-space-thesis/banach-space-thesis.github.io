import PL1.EnfloIntrinsic
import PL1.EnfloTwoMaps
import PL1.IntrinsicRealParts

/-! From dyadic decay to exclusion of arbitrary closed real L1 copies. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal

namespace PL1.EnfloBush

theorem exists_boundedBelow_of_containsIsomorphicCopy
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ContainsIsomorphicCopy ℝ E F) :
    ∃ (T : E →L[ℝ] F) (c : ℝ), 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖ := by
  obtain ⟨V, _, ⟨e⟩⟩ := h
  let N := ‖e.symm.toContinuousLinearMap‖
  have hN : 0 < N + 1 := by dsimp [N]; positivity
  refine ⟨V.subtypeL.comp e.toContinuousLinearMap, (N + 1)⁻¹, inv_pos.mpr hN, ?_⟩
  intro x
  change (N + 1)⁻¹ * ‖x‖ ≤ ‖e x‖
  rw [inv_mul_eq_div, div_le_iff₀ hN]
  have he : ‖x‖ ≤ N * ‖e x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_opNorm (e x)
  nlinarith [norm_nonneg (e x)]

theorem not_containsIsomorphicCopy_of_no_boundedBelow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ∀ (T : IntervalL1 ℝ →L[ℝ] E) (c : ℝ), 0 < c →
      (∀ f, c * ‖f‖ ≤ ‖T f‖) → False) :
    ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) E := by
  intro hc
  obtain ⟨T, c, hc, hlower⟩ := exists_boundedBelow_of_containsIsomorphicCopy hc
  exact h T c hc hlower

open Walsh Noise IntrinsicRealParts

theorem not_boundedBelow_scalarIntrinsic_of_operators (K : Type*) [RCLike K]
    (rates : ℕ → ℝ≥0)
    (hS : ∀ n (A : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar),
      DyadicVanishing (((dyadicSystem ℝ rates).operator n).comp A))
    (T : IntervalL1 ℝ →L[ℝ] (dyadicSystem K rates).IntrinsicSpace)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ f, c * ‖f‖ ≤ ‖T f‖) : False := by
  let : SFinite (IntervalModel.disjointMeasure haar) := by
    dsimp only [IntervalModel.disjointMeasure]
    infer_instance
  let F := (IntervalModel.flattenIsometry (𝕜 := ℝ) haar).toContinuousLinearMap
  let J := (dyadicSystem ℝ rates).inclusion.toContinuousLinearMap
  let A := (realPart K rates).comp T
  let B := (imagPart K rates).comp T
  apply not_boundedBelow_two_maps (IntervalModel.disjointMeasure haar)
    (F.comp (J.comp A)) (F.comp (J.comp B))
    (dyadicVanishing_intrinsic_flatten haar (dyadicSystem ℝ rates) hS A)
    (dyadicVanishing_intrinsic_flatten haar (dyadicSystem ℝ rates) hS B) hc
  intro f
  have hf := (hlower f).trans (norm_le_parts K rates (T f))
  simpa only [F, J, A, B, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using hf

theorem scalarIntrinsic_no_real_L1_of_operators (K : Type*) [RCLike K]
    (rates : ℕ → ℝ≥0)
    (hS : ∀ n (A : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar),
      DyadicVanishing (((dyadicSystem ℝ rates).operator n).comp A)) :
    ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) (dyadicSystem K rates).IntrinsicSpace :=
  not_containsIsomorphicCopy_of_no_boundedBelow (fun T _ hc hlower =>
    not_boundedBelow_scalarIntrinsic_of_operators K rates hS T hc hlower)

#print axioms scalarIntrinsic_no_real_L1_of_operators
end PL1.EnfloBush


