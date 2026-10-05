import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Restricting ell-one coefficients to coordinates is contractive. -/
noncomputable section
open Set
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

theorem lp_one_hasSum_norm {ι : Type*} (f : lp (fun _ : ι => ℝ) 1) :
    HasSum (fun i => ‖f i‖) ‖f‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) f

def lpOneRestrict {ι : Type*} (S : Set ι) (f : lp (fun _ : ι => ℝ) 1) :
    lp (fun _ : ι => ℝ) 1 := by
  classical
  refine ⟨fun i => if i ∈ S then f i else 0, memℓp_gen ?_⟩
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (lp_one_hasSum_norm f).summable
  intro i
  split_ifs <;> simp

theorem lpOneRestrict_apply {ι : Type*} (S : Set ι) (f : lp (fun _ : ι => ℝ) 1) (i : ι) :
    lpOneRestrict S f i = if i ∈ S then f i else 0 := rfl

theorem lpOneRestrict_norm_le {ι : Type*} (S : Set ι) (f : lp (fun _ : ι => ℝ) 1) :
    ‖lpOneRestrict S f‖ ≤ ‖f‖ := by
  apply hasSum_le _ (lp_one_hasSum_norm (lpOneRestrict S f)) (lp_one_hasSum_norm f)
  intro i
  rw [lpOneRestrict_apply]
  split_ifs <;> simp

theorem lpOneRestrict_eq_self {ι : Type*} (S : Set ι) (f : lp (fun _ : ι => ℝ) 1)
    (hf : Function.support f ⊆ S) : lpOneRestrict S f = f := by
  classical
  apply lp.ext
  funext i
  rw [lpOneRestrict_apply]
  by_cases hi : i ∈ S
  · exact if_pos hi
  · rw [if_neg hi]
    by_contra h
    exact hi (hf (Ne.symm h))

end ThesisCommon
