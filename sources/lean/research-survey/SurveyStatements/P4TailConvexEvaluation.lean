import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

/-! Isometric scalarization on a compact parameter space times the weak-star
dual unit ball. Joint continuity uses the actual uniform dual norm bound. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology

namespace SurveyStatements.P4

variable {K E : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def realDualUnitBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1

instance realDualUnitBall_compactSpace : CompactSpace (realDualUnitBall E) :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ E) 1)

lemma realDualUnitBall_norm_le (φ : realDualUnitBall E) :
    ‖WeakDual.toStrongDual φ.val‖ ≤ 1 := by
  simpa only [realDualUnitBall, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right] using φ.property

def dualEvaluation (h : C(K, E)) : C(K × realDualUnitBall E, ℝ) where
  toFun := fun p => p.2.val (h p.1)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p₀
    have hfirst : Tendsto (fun p : K × realDualUnitBall E => ‖h p.1 - h p₀.1‖)
        (𝓝 p₀) (𝓝 0) := by
      have hc : Continuous (fun p : K × realDualUnitBall E => h p.1) :=
        h.continuous.comp continuous_fst
      simpa using ((hc.tendsto p₀).sub (tendsto_const_nhds (x := h p₀.1))).norm
    have hsecond : Tendsto
        (fun p : K × realDualUnitBall E => ‖p.2.val (h p₀.1) - p₀.2.val (h p₀.1)‖)
        (𝓝 p₀) (𝓝 0) := by
      have hc : Continuous (fun p : K × realDualUnitBall E => p.2.val (h p₀.1)) :=
        (WeakDual.eval_continuous (h p₀.1)).comp
          (continuous_subtype_val.comp continuous_snd)
      simpa using ((hc.tendsto p₀).sub
        (tendsto_const_nhds (x := p₀.2.val (h p₀.1)))).norm
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun p => ?_) (by simpa using hfirst.add hsecond)
    have heq : p.2.val (h p.1) - p₀.2.val (h p₀.1) =
        p.2.val (h p.1 - h p₀.1) +
          (p.2.val (h p₀.1) - p₀.2.val (h p₀.1)) := by
      rw [map_sub]
      ring
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add_right
    exact ((WeakDual.toStrongDual p.2.val).le_opNorm _).trans
      (by
        simpa using (mul_le_mul_of_nonneg_right (realDualUnitBall_norm_le p.2)
          (norm_nonneg (h p.1 - h p₀.1))))

@[simp] lemma dualEvaluation_apply (h : C(K, E)) (p : K × realDualUnitBall E) :
    dualEvaluation h p = p.2.val (h p.1) := rfl

lemma norm_dualEvaluation [CompactSpace K] (h : C(K, E)) :
    ‖dualEvaluation h‖ = ‖h‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro p
    calc
      ‖dualEvaluation h p‖ ≤ ‖WeakDual.toStrongDual p.2.val‖ * ‖h p.1‖ :=
        (WeakDual.toStrongDual p.2.val).le_opNorm _
      _ ≤ 1 * ‖h p.1‖ := mul_le_mul_of_nonneg_right
        (realDualUnitBall_norm_le p.2) (norm_nonneg _)
      _ ≤ ‖h‖ := by simpa using h.norm_coe_le_norm p.1
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ (h t)
    let ψ : realDualUnitBall E := ⟨StrongDual.toWeakDual φ,
      by change dist φ 0 ≤ 1; simpa only [dist_zero_right] using hφ⟩
    have heval := (dualEvaluation h).norm_coe_le_norm (t, ψ)
    change ‖φ (h t)‖ ≤ ‖dualEvaluation h‖ at heval
    simpa [hφx] using heval

end SurveyStatements.P4
