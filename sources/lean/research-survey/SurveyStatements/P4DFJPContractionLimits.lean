import SurveyStatements.P4DFJPContractions
import Mathlib.Analysis.Normed.Group.Tannery

/-! Strong approximation in the ambient space lifts to the actual DFJP norm. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Filter Topology

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

theorem tendsto_contractions (D : DFJPGaugeData 𝕜 E) (T : ℕ → E →L[𝕜] E)
    (hK : ∀ n, ∀ x ∈ D.carrier, T n x ∈ D.carrier) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hpoint : ∀ x : E, Tendsto (fun n => T n x) atTop (𝓝 x)) (f : DFJPSpace D) :
    Tendsto (fun n => contraction D (T n) (hK n) (hT n) f) atTop (𝓝 f) := by
  let x := inclusion D f
  have hcoord (j : ℤ) : Tendsto
      (fun n => (dfjpGauge D.carrier j (T n x - x)) ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => T n x - x) atTop (𝓝 (0 : E)) := by
      simpa using (hpoint x).sub_const x
    simpa only [dfjpGauge, gauge_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((continuous_dfjpGauge D.absConvex D.zero_mem j).tendsto 0).comp ht).pow 2
  have hbound (n : ℕ) (j : ℤ) :
      ‖(dfjpGauge D.carrier j (T n x - x)) ^ 2‖ ≤ 4 * (dfjpGauge D.carrier j x) ^ 2 := by
    have hadd : dfjpGauge D.carrier j (T n x - x) ≤
        dfjpGauge D.carrier j (T n x) + dfjpGauge D.carrier j x :=
      map_sub_le_add (dfjpGaugeSeminorm D.absConvex D.zero_mem j) _ _
    have hle : dfjpGauge D.carrier j (T n x - x) ≤ 2 * dfjpGauge D.carrier j x := by
      have hc := gauge_contraction D (T n) (hK n) (hT n) j x
      linarith
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      (dfjpGauge D.carrier j (T n x - x)) ^ 2 ≤ (2 * dfjpGauge D.carrier j x) ^ 2 :=
        pow_le_pow_left₀ (dfjpGauge_nonneg _ _ _) hle 2
      _ = 4 * (dfjpGauge D.carrier j x) ^ 2 := by ring
  have hsum := tendsto_tsum_of_dominated_convergence
    ((summable_gauge_sq D f).mul_left 4) hcoord (Eventually.of_forall hbound)
  have hnorm : Tendsto
      (fun n => ‖contraction D (T n) (hK n) (hT n) f - f‖ ^ 2) atTop (𝓝 0) := by
    have heq (n : ℕ) : ‖contraction D (T n) (hK n) (hT n) f - f‖ ^ 2 =
        ∑' j : ℤ, (dfjpGauge D.carrier j (T n x - x)) ^ 2 := by
      rw [norm_sq]
      simp only [map_sub, inclusion_contractionLinearMap]
      rfl
    simp only [tsum_zero] at hsum
    exact hsum.congr' (Eventually.of_forall fun n => (heq n).symm)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hnorm
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end DFJPSpace

end SurveyStatements.P4
