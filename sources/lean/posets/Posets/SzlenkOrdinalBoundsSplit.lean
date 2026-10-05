import Posets.SzlenkOrdinalBoundsProjection
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! Supremum-norm coordinate splittings become additive norm splittings
in the genuine strong dual. -/
noncomputable section
open Set Topology Filter
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem strongDual_exists_unit_near_norm (φ : StrongDual 𝕜 E) {r : ℝ} (hr : r < ‖φ‖) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ r < ‖φ x‖ := by
  rw [← φ.sSup_unitClosedBall_eq_norm] at hr
  obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_csSup
    ((Metric.nonempty_closedBall.mpr zero_le_one).image (fun x => ‖φ x‖)) hr
  exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, hxr⟩

theorem strongDual_norm_split_le (P Q : E →L[𝕜] E)
    (hPQ : ∀ x y, ‖P x + Q y‖ ≤ max ‖x‖ ‖y‖) (φ : StrongDual 𝕜 E) :
    ‖φ.comp P‖ + ‖φ.comp Q‖ ≤ ‖φ‖ := by
  have hval : ∀ x y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖φ (P x)‖ + ‖φ (Q y)‖ ≤ ‖φ‖ := by
    intro x y hx hy
    obtain ⟨a, ha, hae⟩ := RCLike.exists_norm_eq_mul_self (φ (P x))
    obtain ⟨b, hb, hbe⟩ := RCLike.exists_norm_eq_mul_self (φ (Q y))
    have hxy : ‖P (a • x) + Q (b • y)‖ ≤ 1 := by
      apply (hPQ _ _).trans
      simpa only [norm_smul, ha, hb, one_mul] using max_le hx hy
    have hv := φ.le_opNorm_of_le hxy
    have he : φ (P (a • x) + Q (b • y)) =
        ((‖φ (P x)‖ + ‖φ (Q y)‖ : ℝ) : 𝕜) := by
      simp only [map_add, map_smul, smul_eq_mul, ← hae, ← hbe, map_add]
    rw [he, RCLike.norm_ofReal, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_one] at hv
    exact hv
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hφx⟩ := strongDual_exists_unit_near_norm (φ.comp P)
    (show ‖φ.comp P‖ - ε / 2 < ‖φ.comp P‖ by linarith)
  obtain ⟨y, hy, hφy⟩ := strongDual_exists_unit_near_norm (φ.comp Q)
    (show ‖φ.comp Q‖ - ε / 2 < ‖φ.comp Q‖ by linarith)
  have hh := hval x y hx hy
  simp only [ContinuousLinearMap.comp_apply] at hφx hφy
  linarith

theorem strongDual_norm_split (P Q : E →L[𝕜] E)
    (hsum : P + Q = ContinuousLinearMap.id 𝕜 E)
    (hPQ : ∀ x y, ‖P x + Q y‖ ≤ max ‖x‖ ‖y‖) (φ : StrongDual 𝕜 E) :
    ‖φ.comp P‖ + ‖φ.comp Q‖ = ‖φ‖ := by
  apply le_antisymm (strongDual_norm_split_le P Q hPQ φ)
  have he : φ.comp P + φ.comp Q = φ := by
    rw [← ContinuousLinearMap.comp_add, hsum, ContinuousLinearMap.comp_id]
  simpa only [he] using norm_add_le (φ.comp P) (φ.comp Q)

theorem strongDual_norm_sub_split (P Q : E →L[𝕜] E)
    (hsum : P + Q = ContinuousLinearMap.id 𝕜 E)
    (hPQ : ∀ x y, ‖P x + Q y‖ ≤ max ‖x‖ ‖y‖) (φ ψ : StrongDual 𝕜 E) :
    ‖φ - ψ‖ ≤ ‖φ.comp P - ψ.comp P‖ +
      (‖φ‖ - ‖φ.comp P‖) + (‖ψ‖ - ‖ψ.comp P‖) := by
  have hφ := strongDual_norm_split P Q hsum hPQ φ
  have hψ := strongDual_norm_split P Q hsum hPQ ψ
  have hd := strongDual_norm_split P Q hsum hPQ (φ - ψ)
  have hq := norm_sub_le (φ.comp Q) (ψ.comp Q)
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp] at hd
  linarith

theorem strongDual_projection_mass_approx {I : Type*} {l : Filter I} [NeBot l]
    (P : I → E →L[𝕜] E) (hP : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (φ : StrongDual 𝕜 E) {r : ℝ} (hr : r < ‖φ‖) : ∃ i, r < ‖φ.comp (P i)‖ := by
  obtain ⟨x, hx, hrx⟩ := strongDual_exists_unit_near_norm φ hr
  have ht := (φ.continuous.tendsto x |>.comp (hP x)).norm
  obtain ⟨i, hi⟩ := (ht.eventually (Ioi_mem_nhds hrx)).exists
  exact ⟨i, hi.trans_le (by simpa only [mul_one, ContinuousLinearMap.comp_apply, Function.comp_apply]
    using (φ.comp (P i)).le_opNorm_of_le hx)⟩

end Posets
