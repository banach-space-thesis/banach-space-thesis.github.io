import PEMS.ExtremalCutoffNorm
import ThesisCommon.Analysis.AlmostDisjointNormalization

/-! An actual disjoint splitting of an extremal sequence can be normalized
without changing its extremal cutoff limit. Uniform integrability of the
weak part supplies the only analytic loss estimate. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_normalized_disjoint_extremal_of_splitting
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f g h : ℕ → LOne 𝕜 μ)
    (hfg : ∀ n, f n = g n + h n) (hh : ∀ n, ‖h n‖ ≤ 1)
    (hdisj : Pairwise fun i j => ∀ᵐ x ∂μ, h i x = 0 ∨ h j x = 0)
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hAd : Pairwise (Disjoint on A))
    (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0))
    (hgUI : UnifIntegrable (fun n => (T (g n) : Y → 𝕜)) 1 ν)
    (hc : 0 < alphaTheta T univ)
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
      (𝓝 (alphaTheta T univ))) :
    ∃ u : ℕ → LOne 𝕜 μ, ∃ B : ℕ → Set Y, ∃ hB : ∀ n, MeasurableSet (B n),
      (∀ n, ‖u n‖ = 1) ∧
      (Pairwise fun i j => ∀ᵐ x ∂μ, u i x = 0 ∨ u j x = 0) ∧
      Pairwise (Disjoint on B) ∧
      Tendsto (fun n => ν (B n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖lpCut (B n) (hB n) (T (u n))‖) atTop
        (𝓝 (alphaTheta T univ)) ∧
      UniformIntegrable (fun n => (lpCut (B n)ᶜ (hB n).compl (T (u n)) : Y → 𝕜)) 1 ν := by
  have hgcut := ThesisCommon.UnifIntegrable.tendsto_norm_lOneCut
    (fun n => T (g n)) hgUI A hA hmass
  have herr : Tendsto (fun n =>
      ‖lpCut (A n) (hA n) (T (f n)) - lpCut (A n) (hA n) (T (h n))‖) atTop (𝓝 0) := by
    simpa only [hfg, map_add, lpCut_add, add_sub_cancel_right] using hgcut
  have hhcut := tendsto_norm_model_of_norm_error herr hconv
  have hhnorm := extremal_cutoff_input_norm_tendsto_one T h hh A hA hmass hc hhcut
  let v : ℕ → LOne 𝕜 μ := fun n => ((‖h n‖⁻¹ : ℝ) : 𝕜) • h n
  have hvclose : Tendsto (fun n => ‖h n - v n‖) atTop (𝓝 0) := by
    simpa only [inv_one, RCLike.ofReal_one, one_smul] using
      tendsto_normalized_model_error (𝕜 := 𝕜) (f := h) (g := h) zero_lt_one
        (by simp) hhnorm
  have hvcutclose : Tendsto (fun n =>
      ‖lpCut (A n) (hA n) (T (h n)) - lpCut (A n) (hA n) (T (v n))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hvclose.const_mul ‖T‖)
    change ‖((lpCutL (A n) (hA n)).comp T) (h n) -
      ((lpCutL (A n) (hA n)).comp T) (v n)‖ ≤ ‖T‖ * ‖h n - v n‖
    rw [← map_sub]
    exact (norm_lpCut_le (A n) (hA n) _).trans (T.le_opNorm _)
  have hvcut := tendsto_norm_model_of_norm_error hvcutclose hhcut
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hhnorm.eventually (lt_mem_nhds zero_lt_one))
  let φ : ℕ → ℕ := fun n => N + n
  have hφ : StrictMono φ := fun i j hij => Nat.add_lt_add_left hij N
  have hvnorm : ∀ n, ‖v (φ n)‖ = 1 := by
    intro n
    simpa only [v, RCLike.ofReal_inv] using
      norm_smul_inv_norm (𝕜 := 𝕜) (norm_pos_iff.mp (hN (φ n) (Nat.le_add_right _ _)))
  have hvdisj : Pairwise fun i j => ∀ᵐ x ∂μ, v (φ i) x = 0 ∨ v (φ j) x = 0 := by
    intro i j hij
    filter_upwards [hdisj (hφ.injective.ne hij),
      Lp.coeFn_smul (((‖h (φ i)‖⁻¹ : ℝ) : 𝕜)) (h (φ i)),
      Lp.coeFn_smul (((‖h (φ j)‖⁻¹ : ℝ) : 𝕜)) (h (φ j))] with x hx hi hj
    change (((‖h (φ i)‖⁻¹ : ℝ) : 𝕜) • h (φ i)) x = 0 ∨
      (((‖h (φ j)‖⁻¹ : ℝ) : 𝕜) • h (φ j)) x = 0
    rw [hi, hj]
    rcases hx with hx | hx <;> simp [hx]
  have hvconv := hvcut.comp hφ.tendsto_atTop
  have hmass' := hmass.comp hφ.tendsto_atTop
  refine ⟨fun n => v (φ n), fun n => A (φ n), fun n => hA (φ n),
    hvnorm, hvdisj, fun i j hij => hAd (hφ.injective.ne hij), hmass', hvconv, ?_⟩
  exact extremal_cutoff_residual_uniformIntegrable T _ (fun n => (hvnorm n).le)
    _ _ hmass' hvconv

end PEMS
