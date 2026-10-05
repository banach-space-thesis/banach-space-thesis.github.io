import ThesisCommon.Analysis.ChargeBasics
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Absolutely summable mixtures of full-power-set charges. Total variation is
bounded by the sum of absolute coefficients, also for uncountable index sets. -/
noncomputable section
open Set
namespace ThesisCommon

theorem chargeSeries_summable_abs {α ι : Type*} (c : ι → ℝ)
    (hc : Summable (fun i => |c i|)) (ν : ι → UnitCharge α) (A : Set α) :
    Summable (fun i => |c i * ν i A|) := by
  apply hc.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro i
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) ((ν i).abs_apply_le_one A)

theorem chargeSeries_summable {α ι : Type*} (c : ι → ℝ)
    (hc : Summable (fun i => |c i|)) (ν : ι → UnitCharge α) (A : Set α) :
    Summable (fun i => c i * ν i A) := by
  apply hc.of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) ((ν i).abs_apply_le_one A)

theorem chargeSeries_variation {α ι : Type*} (c : ι → ℝ)
    (hc : Summable (fun i => |c i|)) (ν : ι → UnitCharge α)
    (F : Finset ℕ) (A : ℕ → Set α)
    (hA : (↑F : Set ℕ).Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ j ∈ F, |∑' i, c i * ν i (A j)| ≤ ∑' i, |c i| := by
  have hs := hasSum_sum (s := F) (fun j _ => (chargeSeries_summable_abs c hc ν (A j)).hasSum)
  calc
    _ ≤ ∑ j ∈ F, ∑' i, |c i * ν i (A j)| := Finset.sum_le_sum (fun j _ => by
      have hn : Summable (fun i => ‖c i * ν i (A j)‖) := by
        simpa only [Real.norm_eq_abs] using chargeSeries_summable_abs c hc ν (A j)
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun i => c i * ν i (A j)) hn)
    _ ≤ ∑' i, |c i| := hasSum_le (fun i => by
      simp_rw [abs_mul, ← Finset.mul_sum]
      exact mul_le_of_le_one_right (abs_nonneg _) ((ν i).variation_le F A hA)) hs hc.hasSum

def chargeSeries {α ι : Type*} (c : ι → ℝ) (hc : Summable (fun i => |c i|))
    (hbound : (∑' i, |c i|) ≤ 1) (ν : ι → UnitCharge α) : UnitCharge α where
  toFun A := ∑' i, c i * ν i A
  map_empty := by simp only [UnitCharge.map_empty, mul_zero, tsum_zero]
  map_union A B hAB := by
    simp only [UnitCharge.map_union _ _ _ hAB, mul_add]
    exact (chargeSeries_summable c hc ν A).tsum_add (chargeSeries_summable c hc ν B)
  variation_le F A hA := (chargeSeries_variation c hc ν F A hA).trans hbound

@[simp] theorem chargeSeries_apply {α ι : Type*} (c : ι → ℝ) (hc : Summable (fun i => |c i|))
    (hbound : (∑' i, |c i|) ≤ 1) (ν : ι → UnitCharge α) (A : Set α) :
    chargeSeries c hc hbound ν A = ∑' i, c i * ν i A := rfl

def lpChargeSeries {α ι : Type*} (c : lp (fun _ : ι => ℝ) 1) (hc : ‖c‖ ≤ 1)
    (ν : ι → UnitCharge α) : UnitCharge α :=
  chargeSeries c
    (by simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) c).summable)
    (by
      have hs : HasSum (fun i => |c i|) ‖c‖ := by
        simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
          lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) c
      exact hs.tsum_eq.trans_le hc) ν

@[simp] theorem lpChargeSeries_apply {α ι : Type*} (c : lp (fun _ : ι => ℝ) 1) (hc : ‖c‖ ≤ 1)
    (ν : ι → UnitCharge α) (A : Set α) : lpChargeSeries c hc ν A = ∑' i, c i * ν i A := rfl

end ThesisCommon
