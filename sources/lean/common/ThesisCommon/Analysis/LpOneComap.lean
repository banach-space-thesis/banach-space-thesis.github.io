import ThesisCommon.Analysis.LpOneRestriction
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Pulling back ell-one coordinates along an injection is contractive. -/
noncomputable section
namespace ThesisCommon

def lpOneComap {ι κ : Type*} (e : ι ↪ κ) (f : lp (fun _ : κ => ℝ) 1) :
    lp (fun _ : ι => ℝ) 1 :=
  ⟨fun i => f (e i), memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Function.comp_def] using
      (lp_one_hasSum_norm f).summable.comp_injective e.injective)⟩

@[simp] theorem lpOneComap_apply {ι κ : Type*} (e : ι ↪ κ) (f : lp (fun _ : κ => ℝ) 1) (i : ι) :
    lpOneComap e f i = f (e i) := rfl

theorem lpOneComap_norm_le {ι κ : Type*} (e : ι ↪ κ) (f : lp (fun _ : κ => ℝ) 1) :
    ‖lpOneComap e f‖ ≤ ‖f‖ := by
  rw [← (lp_one_hasSum_norm (lpOneComap e f)).tsum_eq, ← (lp_one_hasSum_norm f).tsum_eq]
  exact tsum_comp_le_tsum_of_inj (lp_one_hasSum_norm f).summable (fun _ => norm_nonneg _) e.injective

end ThesisCommon
