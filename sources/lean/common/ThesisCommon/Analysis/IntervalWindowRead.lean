import ThesisCommon.Analysis.IntervalWindows
import ThesisCommon.Analysis.CZeroStrongRows

/-! Restriction to shrinking interval windows, with the value at zero
subtracted, gives a bounded map C[0,1] -> c0(C[0,1]). Continuity at zero
supplies norm convergence of the coordinate functions. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalAnchor : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousMap.const UnitInterval (f 0)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro t
      exact f.norm_coe_le_norm 0)

@[simp] theorem intervalAnchor_apply (f : IntervalContinuous 𝕜) (t : UnitInterval) :
    intervalAnchor f t = f 0 := rfl

theorem norm_intervalAnchor_le : ‖intervalAnchor (𝕜 := 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def intervalWindowRead (n : ℕ) : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
  intervalRead (intervalWindow n) - intervalAnchor

theorem norm_intervalWindowRead_le (n : ℕ) : ‖intervalWindowRead (𝕜 := 𝕜) n‖ ≤ 2 := by
  have h₁ := norm_intervalRead_le (𝕜 := 𝕜) (intervalWindow n)
  have h₂ := norm_intervalAnchor_le (𝕜 := 𝕜)
  change ‖intervalRead (𝕜 := 𝕜) (intervalWindow n) - intervalAnchor‖ ≤ 2
  calc
    _ ≤ ‖intervalRead (𝕜 := 𝕜) (intervalWindow n)‖ + ‖intervalAnchor (𝕜 := 𝕜)‖ :=
      norm_sub_le (intervalRead (𝕜 := 𝕜) (intervalWindow n)) (intervalAnchor (𝕜 := 𝕜))
    _ ≤ 2 := by linarith

theorem intervalWindowRead_tendsto_zero (f : IntervalContinuous 𝕜) :
    Tendsto (fun n => intervalWindowRead n f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := Metric.continuousAt_iff.1 (f.continuous.continuousAt (x := (0 : UnitInterval)))
    (ε/2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 intervalRadius_tendsto_zero).2 δ hδ)
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_zero_right]
  apply lt_of_le_of_lt ?_ (by linarith : ε/2 < ε)
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).2
  intro t
  let e := unitSubintervalHomeomorph (intervalWindowLeft n) (intervalWindowRight n) (intervalWindow n).property
  change ‖f (e t).val-f 0‖ ≤ ε/2
  rw [← dist_eq_norm]
  apply (hf ?_).le
  change |((e t).val : ℝ)-0| < δ
  rw [sub_zero, abs_of_nonneg (e t).val.property.1]
  have hb : ((e t).val : ℝ) ≤ (7/8 : ℝ)*intervalRadius n := (e t).property.2
  have hr : ((e t).val : ℝ) ≤ intervalRadius n := by
    have hp := intervalRadius_pos n
    nlinarith
  exact hr.trans_lt (hN n hn)

def intervalCZeroRead : IntervalContinuous 𝕜 →L[𝕜] CZeroSum (IntervalContinuous 𝕜) :=
  cZeroStrongRows intervalWindowRead 2 (by norm_num) norm_intervalWindowRead_le intervalWindowRead_tendsto_zero

@[simp] theorem intervalCZeroRead_apply (f : IntervalContinuous 𝕜) (n : ℕ) :
    intervalCZeroRead f n = intervalWindowRead n f := rfl

theorem norm_intervalCZeroRead_le : ‖intervalCZeroRead (𝕜 := 𝕜)‖ ≤ 2 := norm_cZeroStrongRows_le ..

end ThesisCommon
