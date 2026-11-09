import SurveyStatements.P4DFJPReflexivity

/-! Reflexivity of an actual ℓ² sum of reflexive normed spaces. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048

open Set Finset Filter Topology
open scoped ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {ι : Type v} [DecidableEq ι]
variable {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

lemma lp2_adjoint_projection (s : Finset ι) (φ : StrongDual 𝕜 (lp E 2)) :
    banachAdjoint (lp2Projection (𝕜 := 𝕜) s) φ = lp2DualTruncation φ s := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [banachAdjoint_apply, lp2Projection_apply, map_sum, lp2DualTruncation,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, lp2DualCoordinate_apply]
  rfl

lemma lp2_bidual_projection_of_coordinate
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 (lp E 2))) (x : ∀ i, E i)
    (hx : ∀ i, NormedSpace.inclusionInDoubleDual 𝕜 (E i) (x i) =
      bidualMap (lp2Eval (𝕜 := 𝕜) i) ξ) (s : Finset ι) :
    NormedSpace.inclusionInDoubleDual 𝕜 (lp E 2) (∑ i ∈ s, lp.single 2 i (x i)) =
      bidualMap (lp2Projection (𝕜 := 𝕜) s) ξ := by
  apply ContinuousLinearMap.ext
  intro φ
  simp only [NormedSpace.dual_def, map_sum, bidualMap_apply, lp2_adjoint_projection,
    lp2DualTruncation, ContinuousLinearMap.sum_apply]
  apply sum_congr rfl
  intro i hi
  have h := congrArg (fun q => q (lp2DualCoordinate φ i)) (hx i)
  simpa only [NormedSpace.dual_def, lp2DualCoordinate_apply, bidualMap_apply,
    banachAdjoint] using h

lemma summable_sq_lp2_bidual_coordinates
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 (lp E 2))) (x : ∀ i, E i)
    (hx : ∀ i, NormedSpace.inclusionInDoubleDual 𝕜 (E i) (x i) =
      bidualMap (lp2Eval (𝕜 := 𝕜) i) ξ) : Summable (fun i => ‖x i‖ ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _)
  intro s
  have heq := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at heq
  rw [← heq]
  have hn : ‖∑ i ∈ s, lp.single 2 i (x i)‖ ≤ ‖ξ‖ := by
    have hb := norm_bidualMap_apply_le (lp2Projection (𝕜 := 𝕜) (E := E) s) ξ
    rw [← lp2_bidual_projection_of_coordinate ξ x hx s] at hb
    change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (∑ i ∈ s, lp.single 2 i (x i))‖ ≤ _ at hb
    rw [(NormedSpace.inclusionInDoubleDualLi 𝕜 (E := lp E 2)).norm_map] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right
      (norm_lp2Projection_le_one (𝕜 := 𝕜) (E := E) s) (norm_nonneg ξ)).trans_eq (one_mul _))
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The continuous bidual of an ℓ² sum is represented by genuine vectors
whenever every coordinate space has that property. -/
theorem lp2_reflexive (hE : ∀ i, IsReflexiveNormedSpace 𝕜 (E i)) :
    IsReflexiveNormedSpace 𝕜 (lp E 2) := by
  intro ξ
  choose x hx using fun i => hE i (bidualMap (lp2Eval (𝕜 := 𝕜) (E := E) i) ξ)
  let f : lp E 2 := ⟨x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_sq_lp2_bidual_coordinates ξ x hx)⟩
  refine ⟨f, ?_⟩
  apply ContinuousLinearMap.ext
  intro φ
  have heq (s : Finset ι) :
      (NormedSpace.inclusionInDoubleDual 𝕜 (lp E 2) f) (lp2DualTruncation φ s) =
        ξ (lp2DualTruncation φ s) := by
    simp only [NormedSpace.dual_def, lp2DualTruncation, ContinuousLinearMap.sum_apply,
      map_sum, ContinuousLinearMap.comp_apply]
    apply sum_congr rfl
    intro i hi
    have h := congrArg (fun q => q (lp2DualCoordinate φ i)) (hx i)
    change (lp2DualCoordinate φ i) (x i) = ξ ((lp2DualCoordinate φ i).comp (lp2Eval i))
    exact h
  have ht₁ := ((NormedSpace.inclusionInDoubleDual 𝕜 (lp E 2) f).continuous.tendsto φ).comp
    (tendsto_lp2DualTruncation φ)
  have ht₂ := (ξ.continuous.tendsto φ).comp (tendsto_lp2DualTruncation φ)
  have hfun : (fun s => (NormedSpace.inclusionInDoubleDual 𝕜 (lp E 2) f)
      (lp2DualTruncation φ s)) = fun s => ξ (lp2DualTruncation φ s) := funext heq
  simp only [Function.comp_def] at ht₁ ht₂
  rw [hfun] at ht₁
  exact tendsto_nhds_unique ht₁ ht₂

end SurveyStatements.P4
