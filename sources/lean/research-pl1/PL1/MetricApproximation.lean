import PL1.IntrinsicWalshBlocks

/-! # Metric approximation in the actual intrinsic norm

Contractive finite-dimensional expectations approximate the identity uniformly
on each compact set. This is the metric approximation property, expressed
directly with bounded finite-rank operators and compact sets.
-/

noncomputable section
open Filter Set
open scoped Topology NNReal

namespace PL1

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def HasMetricApproximationProperty (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ K : Set E, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ T : E →L[𝕜] E, ‖T‖ ≤ 1 ∧ FiniteDimensional 𝕜 T.range ∧
      ∀ x ∈ K, ‖T x - x‖ < ε

theorem contractive_strong_approximation_uniform_on_compact
    (T : ℕ → E →L[𝕜] E) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x))
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖T n x - x‖ < ε := by
  obtain ⟨s, _, hs, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 4 by positivity)
  have hev : ∀ᶠ n in atTop, ∀ y ∈ s, ‖T n y - y‖ < ε / 2 := by
    apply hs.eventually_all.mpr
    intro y _
    have hy := (tendsto_iff_norm_sub_tendsto_zero.mp (hlim y)).eventually_lt_const
      (show 0 < ε / 2 by positivity)
    exact hy
  filter_upwards [hev] with n hn
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - y‖ < ε / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hbound : ‖T n x - T n y‖ ≤ ‖x - y‖ := by
    rw [← map_sub]
    exact ((T n).le_opNorm (x - y)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hT n) (norm_nonneg (x - y)))
  have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  have htriangle : ‖T n x - x‖ ≤ ‖T n x - T n y‖ + ‖T n y - y‖ + ‖y - x‖ := by
    calc
      ‖T n x - x‖ = ‖(T n x - T n y) + (T n y - y) + (y - x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hmiddle := hn y hy
  linarith

theorem hasMetricApproximationProperty_of_contractive_finiteDimensional_approximation
    (T : ℕ → E →L[𝕜] E) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hfin : ∀ n, FiniteDimensional 𝕜 (T n).range)
    (hlim : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 x)) :
    HasMetricApproximationProperty 𝕜 E := by
  intro K hK ε hε
  obtain ⟨n, hn⟩ := (contractive_strong_approximation_uniform_on_compact T hT hlim K hK ε hε).exists
  exact ⟨T n, hT n, hfin n, hn⟩

namespace Noise

theorem norm_intrinsicExpectation_eq_one (𝕜 : Type*) [RCLike 𝕜]
    (rates : ℕ → ℝ≥0) (m : ℕ) : ‖intrinsicExpectation 𝕜 rates m‖ = 1 := by
  apply le_antisymm (norm_intrinsicExpectation_le 𝕜 rates m)
  have hx : intrinsicCharacter 𝕜 rates ∅ ≠ 0 :=
    (linearIndependent_intrinsicCharacter 𝕜 rates).ne_zero ∅
  have hf : intrinsicExpectation 𝕜 rates m (intrinsicCharacter 𝕜 rates ∅) =
      intrinsicCharacter 𝕜 rates ∅ := by simp [intrinsicExpectation_character]
  have hn := (intrinsicExpectation 𝕜 rates m).le_opNorm (intrinsicCharacter 𝕜 rates ∅)
  rw [hf] at hn
  nlinarith [norm_pos_iff.mpr hx]

theorem intrinsic_hasMetricApproximationProperty (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0) :
    HasMetricApproximationProperty 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace :=
  hasMetricApproximationProperty_of_contractive_finiteDimensional_approximation
    (intrinsicExpectation 𝕜 rates) (norm_intrinsicExpectation_le 𝕜 rates)
    (intrinsicExpectation_range_finiteDimensional 𝕜 rates) (tendsto_intrinsicExpectation 𝕜 rates)

end Noise
end PL1
