import LindenstraussRetraction.RadialRetraction
import Mathlib.Analysis.SpecificLimits.Basic

/-! The nonexpansive bounded radial maps in the final approximation proposition. -/

noncomputable section
open Filter Topology
namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def softRadial (R : ℝ) (x : X) : X := ((R/(R+‖x‖) : ℝ) : 𝕜) • x

theorem softRadial_norm_le {R : ℝ} (hR : 0 < R) (x : X) : ‖softRadial 𝕜 R x‖ ≤ R := by
  have hd : 0 < R+‖x‖ := add_pos_of_pos_of_nonneg hR (norm_nonneg x)
  rw [softRadial, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg hR.le hd.le)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

private theorem softRadial_dist_le_ordered {R : ℝ} (hR : 0 < R) (x y : X)
    (hxy : ‖y‖ ≤ ‖x‖) : dist (softRadial 𝕜 R x) (softRadial 𝕜 R y) ≤ dist x y := by
  let r := ‖x‖
  let s := ‖y‖
  let α := R/(R+r)
  let β := R/(R+s)
  let t := R/((R+r)*(R+s))
  have hr : 0 ≤ r := norm_nonneg x
  have hs : 0 ≤ s := norm_nonneg y
  have h₁ : 0 < R+r := add_pos_of_pos_of_nonneg hR hr
  have h₂ : 0 < R+s := add_pos_of_pos_of_nonneg hR hs
  have ht : 0 ≤ t := div_nonneg hR.le (mul_nonneg h₁.le h₂.le)
  have ha : 0 ≤ α := div_nonneg hR.le h₁.le
  have hdiff : β-α = t*(r-s) := by
    dsimp [α, β, t]
    field_simp
    ring
  have hβα : α ≤ β := by rw [← sub_nonneg, hdiff]; exact mul_nonneg ht (sub_nonneg.mpr hxy)
  have hcoef : α+t*s ≤ 1 := by
    have he : α+t*s = R*(R+2*s)/((R+r)*(R+s)) := by
      dsimp [α, t]
      field_simp
      ring
    rw [he, div_le_one₀ (mul_pos h₁ h₂)]
    nlinarith
  have he : softRadial 𝕜 R x-softRadial 𝕜 R y =
      (α : 𝕜) • (x-y) + ((α-β : ℝ) : 𝕜) • y := by
    rw [RCLike.ofReal_sub, sub_smul, smul_sub]
    change (α : 𝕜) • x-(β : 𝕜) • y = _
    abel
  rw [dist_eq_norm, dist_eq_norm, he]
  have hdist : r-s ≤ ‖x-y‖ := norm_sub_norm_le x y
  calc
    ‖(α : 𝕜) • (x-y) + ((α-β : ℝ) : 𝕜) • y‖ ≤
        ‖(α : 𝕜) • (x-y)‖ + ‖((α-β : ℝ) : 𝕜) • y‖ := norm_add_le _ _
    _ = α*‖x-y‖ + (β-α)*s := by
      rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg ha, abs_of_nonpos (sub_nonpos.mpr hβα)]
      dsimp [s]
      ring
    _ = α*‖x-y‖ + (t*s)*(r-s) := by rw [hdiff]; ring
    _ ≤ α*‖x-y‖ + (t*s)*‖x-y‖ :=
      add_le_add_left (mul_le_mul_of_nonneg_left hdist (mul_nonneg ht hs)) _
    _ = (α+t*s)*‖x-y‖ := by ring
    _ ≤ ‖x-y‖ := by nlinarith [norm_nonneg (x-y)]

theorem softRadial_lipschitz {R : ℝ} (hR : 0 < R) :
    LipschitzWith 1 (softRadial 𝕜 R : X → X) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact softRadial_dist_le_ordered 𝕜 hR x y h
  · simpa only [dist_comm] using softRadial_dist_le_ordered 𝕜 hR y x h

theorem softRadial_tendsto (x : X) :
    Tendsto (fun n : ℕ => softRadial 𝕜 ((n+1 : ℕ) : ℝ) x) atTop (𝓝 x) := by
  have hden : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)+‖x‖) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      tendsto_atTop_add_const_right atTop (1+‖x‖)
        (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  have hc : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)/(((n+1 : ℕ) : ℝ)+‖x‖))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖)).div_atTop hden)
    simp only [sub_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro n
    have hn : 0 < ((n+1 : ℕ) : ℝ)+‖x‖ := by positivity
    field_simp
    ring
  have hc𝕜 : Tendsto (fun n : ℕ =>
      ((((n+1 : ℕ) : ℝ) / (((n+1 : ℕ) : ℝ) + ‖x‖) : ℝ) : 𝕜)) atTop (𝓝 (1 : 𝕜)) :=
    by simpa only [Function.comp_def, RCLike.ofReal_one] using
      ((RCLike.continuous_ofReal : Continuous (fun r : ℝ => (r : 𝕜))).tendsto (1 : ℝ)).comp hc
  have h := hc𝕜.smul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  simpa only [RCLike.ofReal_one, one_smul, softRadial] using h

end LindenstraussRetraction
