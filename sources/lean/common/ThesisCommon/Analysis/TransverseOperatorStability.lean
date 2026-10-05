import ThesisCommon.Analysis.ClosedFiniteDimensionalSum
import Mathlib.Analysis.Normed.Operator.Banach

/-! Small operator perturbations preserve injectivity on a closed range
and on any fixed finite-dimensional transverse block. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem operator_injective_of_norm_sub_lt_lower_bound
    (f g : X →L[𝕜] Y) {c : ℝ} (_hc : 0 < c)
    (hf : ∀ x, c * ‖x‖ ≤ ‖f x‖) (hgf : ‖g-f‖ < c) :
    Function.Injective g := by
  have hz : ∀ x, g x = 0 → x = 0 := by
    intro x hx
    have h := (g-f).le_opNorm x
    have he : ‖(g-f) x‖ = ‖f x‖ := by simp only [ContinuousLinearMap.sub_apply, hx, zero_sub, norm_neg]
    rw [he] at h
    have hn : ‖x‖ = 0 := by nlinarith [hf x, norm_nonneg x]
    exact norm_eq_zero.mp hn
  intro x y hxy
  exact sub_eq_zero.mp (hz (x-y) (by rw [map_sub, hxy, sub_self]))

theorem exists_injective_operator_ball [CompleteSpace X] [CompleteSpace Y]
    (f : X →L[𝕜] Y) (hf : Function.Injective f)
    (hclosed : IsClosed (Set.range f)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : X →L[𝕜] Y, ‖g-f‖ < δ → Function.Injective g := by
  obtain ⟨K,hK⟩ := f.antilipschitz_of_injective_of_isClosed_range hf hclosed
  let c : ℝ := ((K : ℝ)+1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  refine ⟨c,hc,fun g hg => operator_injective_of_norm_sub_lt_lower_bound f g hc ?_ hg⟩
  intro x
  have h : ‖x‖ ≤ (K : ℝ) * ‖f x‖ := by
    simpa only [map_zero, dist_zero_right] using hK.le_mul_dist x 0
  have h' : ‖x‖ ≤ ((K : ℝ)+1) * ‖f x‖ := by nlinarith [norm_nonneg (f x)]
  have h'' := mul_le_mul_of_nonneg_left h' hc.le
  simpa only [c, ← mul_assoc, inv_mul_cancel₀ (by positivity : (K : ℝ)+1 ≠ 0), one_mul] using h''

theorem transverse_coprod_injective [CompleteSpace X] [CompleteSpace Y]
    (f : X →L[𝕜] Y) (hf : Function.Injective f) (Z : Submodule 𝕜 Y)
    (hZ : Disjoint (LinearMap.range f.toLinearMap) Z) :
    Function.Injective (f.coprod Z.subtypeL) := by
  have hz : ∀ u : X × Z, (f.coprod Z.subtypeL) u = 0 → u = 0 := by
    rintro ⟨x,z⟩ h
    change f x + z.val = 0 at h
    have hmem : f x ∈ Z := by
      have he : f x = -z.val := eq_neg_of_add_eq_zero_left h
      rw [he]
      exact Z.neg_mem z.property
    have hfx : f x = 0 := (Submodule.disjoint_def.mp hZ) (f x)
      (LinearMap.mem_range_self _ x) hmem
    have hx : x = 0 := hf (by simpa only [map_zero] using hfx)
    have hz : z = 0 := Subtype.ext (by simpa only [hfx, zero_add] using h)
    simp only [hx,hz,Prod.zero_eq_mk]
  intro u v huv
  exact sub_eq_zero.mp (hz (u-v) (by rw [map_sub, huv, sub_self]))

theorem exists_injective_transverse_ball [CompleteSpace X] [CompleteSpace Y]
    (f : X →L[𝕜] Y) (hf : Function.Injective f)
    (hclosed : IsClosed (Set.range f)) (Z : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 Z] (hZ : Disjoint (LinearMap.range f.toLinearMap) Z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : X →L[𝕜] Y, ‖g-f‖ < δ →
      Function.Injective (g.coprod Z.subtypeL) := by
  letI : CompleteSpace Z := Z.closed_of_finiteDimensional.completeSpace_coe
  let C := f.coprod Z.subtypeL
  have hC : Function.Injective C := transverse_coprod_injective f hf Z hZ
  have hCclosed : IsClosed (Set.range C) := by
    have hh := submodule_isClosed_sup_of_finiteDimensional_right
      (LinearMap.range f.toLinearMap) Z hclosed
    have he : LinearMap.range C.toLinearMap = LinearMap.range f.toLinearMap ⊔ Z := by
      simp only [C, ContinuousLinearMap.coe_coprod, LinearMap.range_coprod]
      change LinearMap.range f.toLinearMap ⊔ LinearMap.range Z.subtype = _
      rw [Submodule.range_subtype]
    change IsClosed (LinearMap.range C.toLinearMap : Set Y)
    rwa [he]
  obtain ⟨δ,hδ,hball⟩ := exists_injective_operator_ball C hC hCclosed
  refine ⟨δ,hδ,fun g hg => hball (g.coprod Z.subtypeL) ?_⟩
  apply lt_of_le_of_lt ?_ hg
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (g-f))
  rintro ⟨x,z⟩
  have he : ((g.coprod Z.subtypeL)-C) (x,z) = (g-f) x := by
    simp only [C, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coprod_apply,
      Submodule.subtypeL_apply, add_sub_add_right_eq_sub]
  rw [he]
  exact ((g-f).le_opNorm x).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le (x,z)) (norm_nonneg (g-f)))

end ThesisCommon
