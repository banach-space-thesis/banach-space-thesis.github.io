import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! Actual scalar ultralimits of bounded sequences, as a norm-one bounded
linear map. A cofinite ultrafilter agrees with ordinary sequence limits. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 ι : Type*} [RCLike 𝕜]

theorem scalar_bounded_exists_ultralimit (U : Ultrafilter ι)
    (x : lp (fun _ : ι => 𝕜) ∞) :
    ∃ z : 𝕜, Tendsto (fun i => x i) (U : Filter ι) (𝓝 z) := by
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : 𝕜) ‖x‖).ultrafilter_le_nhds
    (U.map (fun i => x i)) (by
      apply Filter.le_principal_iff.mpr
      change ∀ᶠ i in (U : Filter ι), x i ∈ Metric.closedBall (0 : 𝕜) ‖x‖
      exact Filter.Eventually.of_forall (fun i => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          lp.norm_apply_le_norm ENNReal.top_ne_zero x i))
  exact ⟨z, hz⟩

def scalarUltralimitValue (U : Ultrafilter ι) (x : lp (fun _ : ι => 𝕜) ∞) : 𝕜 :=
  limUnder (U : Filter ι) (fun i => x i)

theorem scalarUltralimitValue_tendsto (U : Ultrafilter ι)
    (x : lp (fun _ : ι => 𝕜) ∞) :
    Tendsto (fun i => x i) (U : Filter ι) (𝓝 (scalarUltralimitValue U x)) :=
  tendsto_nhds_limUnder (scalar_bounded_exists_ultralimit U x)

theorem norm_scalarUltralimitValue_le (U : Ultrafilter ι)
    (x : lp (fun _ : ι => 𝕜) ∞) : ‖scalarUltralimitValue U x‖ ≤ ‖x‖ :=
  le_of_tendsto (scalarUltralimitValue_tendsto U x).norm
    (Filter.Eventually.of_forall (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero x i))

def scalarUltralimit (U : Ultrafilter ι) : lp (fun _ : ι => 𝕜) ∞ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := scalarUltralimitValue U
      map_add' := fun x y => tendsto_nhds_unique
        (scalarUltralimitValue_tendsto U (x+y))
        ((scalarUltralimitValue_tendsto U x).add (scalarUltralimitValue_tendsto U y))
      map_smul' := fun c x => tendsto_nhds_unique
        (scalarUltralimitValue_tendsto U (c • x))
        ((scalarUltralimitValue_tendsto U x).const_smul c) }
    1 (fun x => by simpa only [one_mul] using norm_scalarUltralimitValue_le U x)

theorem norm_scalarUltralimit_le (U : Ultrafilter ι) :
    ‖scalarUltralimit (𝕜 := 𝕜) U‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem scalarUltralimit_tendsto (U : Ultrafilter ι)
    (x : lp (fun _ : ι => 𝕜) ∞) :
    Tendsto (fun i => x i) (U : Filter ι) (𝓝 (scalarUltralimit U x)) :=
  scalarUltralimitValue_tendsto U x

theorem scalarUltralimit_eq_of_tendsto (U : Ultrafilter ι)
    (x : lp (fun _ : ι => 𝕜) ∞) {z : 𝕜} (hz : Tendsto (fun i => x i) U (𝓝 z)) :
    scalarUltralimit U x = z :=
  tendsto_nhds_unique (scalarUltralimit_tendsto U x) hz

theorem scalarUltralimit_hyperfilter_eq_of_tendsto
    (x : lp (fun _ : ℕ => 𝕜) ∞) {z : 𝕜} (hz : Tendsto (fun i => x i) atTop (𝓝 z)) :
    scalarUltralimit (hyperfilter ℕ) x = z :=
  scalarUltralimit_eq_of_tendsto _ x (hz.mono_left Nat.hyperfilter_le_atTop)

end ThesisCommon

