import SurveyStatements.P5GridLocalizedAction
import SurveyStatements.P5CaponLocalizedUnbounded

/-! A norm limit of actual square-grid multipliers cannot have a bounded
Capon composition unless that multiplier is zero. The proof uses the explicit
localized finite tensors, with their nonvanishing images on one square. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem capon_square_grid_norm_closure_rigidity
    (hp_finite : p ≠ ∞)
    (M F : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      ∃ a : Fin (2 ^ m) → Fin (2 ^ m) → 𝕜,
        ‖M - mixedDyadicGridOperator m m a‖ < ε)
    (hFM : ∀ I J : DyadicIndex, F (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then M (productHaar 𝕜 p I J) else 0) :
    M = 0 := by
  by_contra hM
  let β : ℝ := ‖M‖
  have hβ : 0 < β := norm_pos_iff.mpr hM
  obtain ⟨m, a, happrox⟩ := happrox (β / 4) (by positivity)
  let A : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p := mixedDyadicGridOperator m m a
  have herror : ‖M - A‖ < β / 4 := happrox
  have htriangle : β ≤ ‖M - A‖ + ‖A‖ := by
    calc
      β = ‖(M - A) + A‖ := by rw [sub_add_cancel]
      _ ≤ ‖M - A‖ + ‖A‖ := norm_add_le _ _
  have hA : β / 2 < ‖A‖ := by linarith
  obtain ⟨i₀, j₀, ha⟩ : ∃ i₀ j₀ : Fin (2 ^ m), β / 2 < ‖a i₀ j₀‖ := by
    by_contra h
    push_neg at h
    have hbound : ‖A‖ ≤ β / 2 := norm_mixedDyadicGridOperator_le m m a (by positivity) h
    exact (not_le_of_gt hA) hbound
  let x (N : ℕ) : MixedNorm 𝕜 p :=
    RealScalar.embedding 𝕜 p (caponLocalizedInput m i₀ j₀ p N)
  let y (N : ℕ) : MixedNorm 𝕜 p :=
    RealScalar.embedding 𝕜 p (caponLocalizedImage m i₀ j₀ p N)
  have hFy (N : ℕ) : F (x N) = M (y N) := by
    apply caponLocalized_embedded_input_image 𝕜 m i₀ j₀ F M
    intro I J _ _ _ _
    exact hFM I J
  have hAy (N : ℕ) : A (y N) = a i₀ j₀ • y N :=
    mixedDyadicGridOperator_embedded_local_image m a i₀ j₀ N
  have hynorm (N : ℕ) : intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 ≤ ‖y N‖ := by
    change _ ≤ ‖RealScalar.embedding 𝕜 p (caponLocalizedImage m i₀ j₀ p N)‖
    rw [RealScalar.norm_embedding_apply]
    exact norm_caponLocalizedImage_lower m i₀ j₀ N
  have hMy (N : ℕ) : β / 4 * ‖y N‖ ≤ ‖M (y N)‖ := by
    have ht := norm_add_le ((A - M) (y N)) (M (y N))
    have heq : (A - M) (y N) + M (y N) = A (y N) := by
      simp only [ContinuousLinearMap.sub_apply, sub_add_cancel]
    rw [heq, hAy N, norm_smul] at ht
    have he := (A - M).le_opNorm (y N)
    rw [norm_sub_rev A M] at he
    have hn := norm_nonneg (y N)
    have hgap : β / 4 ≤ ‖a i₀ j₀‖ - ‖M - A‖ := by linarith
    have hgapmul := mul_le_mul_of_nonneg_right hgap hn
    nlinarith [hgapmul]
  have hlower (N : ℕ) : β / 4 *
      (intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4) ≤ ‖F (x N)‖ := by
    rw [hFy N]
    exact (mul_le_mul_of_nonneg_left (hynorm N) (by positivity)).trans (hMy N)
  have hx : Tendsto x atTop (nhds 0) := by
    simpa only [x, map_zero] using
      ((RealScalar.embedding 𝕜 p).continuous.tendsto 0).comp
        (tendsto_caponLocalizedInput hp_finite m i₀ j₀)
  have hlim : Tendsto (fun N => ‖F (x N)‖) atTop (nhds 0) := by
    simpa using ((F.continuous.tendsto 0).comp hx).norm
  have hbad := ge_of_tendsto hlim (Eventually.of_forall hlower)
  have hpos : 0 < β / 4 * (intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4) := by
    exact mul_pos (div_pos hβ (by norm_num))
      (div_pos (mul_pos (intervalLpDyadicRadius_pos m) (intervalLpDyadicRadius_pos m))
        (by norm_num))
  exact (not_le_of_gt hpos) hbad

end SurveyStatements.P5
