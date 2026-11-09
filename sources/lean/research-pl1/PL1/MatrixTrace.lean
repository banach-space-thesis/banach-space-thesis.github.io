import PL1.SmoothingApproximation
import PL1.L1Sum

/-! # Finite matrix compressions and the interval identity obstruction -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.MatrixTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem trace_sum {ι : Type*} (s : Finset ι)
    (R : ι → IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (n : ℕ) :
    DyadicTrace.trace n (∑ i ∈ s, R i) = ∑ i ∈ s, DyadicTrace.trace n (R i) := by
  simp only [DyadicTrace.trace, TraceBounds.partitionTrace, TraceBounds.finiteTrace,
    ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  exact Finset.sum_comm

theorem trace_tendsto_zero_sum {ι : Type*} (s : Finset ι)
    (R : ι → IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (hR : ∀ i ∈ s, Tendsto (fun n => DyadicTrace.trace n (R i)) atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n (∑ i ∈ s, R i)) atTop (𝓝 0) := by
  simp_rw [trace_sum]
  simpa using tendsto_finsetSum s hR

def insertion (i : ℕ) : Y →L[𝕜] L1Sum Y :=
  lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) 1 i

def coordinate (i : ℕ) : L1Sum Y →L[𝕜] Y :=
  lp.evalCLM 𝕜 (fun _ : ℕ => Y) 1 i

/-- The actual finite coordinate mask of an ell1 sum. -/
def compression (s : Finset ℕ) : L1Sum Y →L[𝕜] L1Sum Y :=
  ∑ i ∈ s, (insertion (𝕜 := 𝕜) i).comp (coordinate i)

theorem compression_apply (s : Finset ℕ) (x : L1Sum Y) :
    compression (𝕜 := 𝕜) s x = ∑ i ∈ s, lp.single 1 i (x i) := by
  simp only [compression, sum_apply, ContinuousLinearMap.comp_apply, insertion, coordinate]
  rfl

theorem compression_apply_coord (s : Finset ℕ) (x : L1Sum Y) (i : ℕ) :
    compression (𝕜 := 𝕜) s x i = if i ∈ s then x i else 0 := by
  rw [compression_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

theorem norm_compression_le_one (s : Finset ℕ) : ‖compression (𝕜 := 𝕜) (Y := Y) s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, compression_apply]
  have h := lp.norm_compl_sum_single (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x s
  have hc := lp.norm_sum_single (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (fun i => x i) s
  simp only [ENNReal.toReal_one, Real.rpow_one] at h hc
  rw [hc]
  have hn := norm_nonneg (x - ∑ i ∈ s, lp.single 1 i (x i))
  linarith

def entry (Q : L1Sum Y →L[𝕜] L1Sum Y) (i j : ℕ) : Y →L[𝕜] Y :=
  (coordinate i).comp (Q.comp (insertion j))

theorem compressed_sandwich_eq_sum (E F : Finset ℕ)
    (A : L1Sum Y →L[𝕜] IntervalL1 𝕜) (Q : L1Sum Y →L[𝕜] L1Sum Y)
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum Y) :
    A.comp ((compression E).comp (Q.comp ((compression F).comp B))) =
      ∑ i ∈ E, ∑ j ∈ F, (A.comp (insertion i)).comp
        ((entry Q i j).comp ((coordinate j).comp B)) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [compression, entry, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  exact Finset.sum_comm

theorem compressed_trace_tendsto_zero (E F : Finset ℕ)
    (A : L1Sum Y →L[𝕜] IntervalL1 𝕜) (Q : L1Sum Y →L[𝕜] L1Sum Y)
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum Y)
    (hentry : ∀ i ∈ E, ∀ j ∈ F, Tendsto (fun n => DyadicTrace.trace n
      ((A.comp (insertion i)).comp ((entry Q i j).comp ((coordinate j).comp B))))
        atTop (𝓝 0)) :
    Tendsto (fun n => DyadicTrace.trace n
      (A.comp ((compression E).comp (Q.comp ((compression F).comp B))))) atTop (𝓝 0) := by
  rw [compressed_sandwich_eq_sum]
  apply trace_tendsto_zero_sum
  intro i hi
  exact trace_tendsto_zero_sum F _ (hentry i hi)

theorem one_le_norm_id_sub_compression (E F : Finset ℕ)
    (A : L1Sum Y →L[𝕜] IntervalL1 𝕜) (Q : L1Sum Y →L[𝕜] L1Sum Y)
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum Y)
    (hentry : ∀ i ∈ E, ∀ j ∈ F, Tendsto (fun n => DyadicTrace.trace n
      ((A.comp (insertion i)).comp ((entry Q i j).comp ((coordinate j).comp B))))
        atTop (𝓝 0)) :
    1 ≤ ‖DyadicTrace.restrictLinfty (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) -
      A.comp ((compression E).comp (Q.comp ((compression F).comp B))))‖ :=
  DyadicTrace.one_le_norm_id_sub _ (compressed_trace_tendsto_zero E F A Q B hentry)

end PL1.MatrixTrace
