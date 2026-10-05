import ThesisCommon.Analysis.SigmaComplexUnitCharge
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Absolutely summable complex mixtures of full-power-set charges. The total
variation bound is joint complex variation, with arbitrary index sets. -/
noncomputable section
open Set
namespace ThesisCommon

instance {α : Type*} : Zero (ComplexUnitCharge α) where
  zero := {
    toFun := fun _ => 0
    map_empty := rfl
    map_union := by intros; simp
    variation_le := by intros; simp }

@[simp] theorem ComplexUnitCharge.zero_apply {α : Type*} (A : Set α) :
    (0 : ComplexUnitCharge α) A = 0 := rfl

instance {α : Type*} : Inhabited (ComplexUnitCharge α) := ⟨0⟩

theorem complexChargeSeries_summable_norm {α ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (ν : ι → ComplexUnitCharge α) (A : Set α) :
    Summable (fun i => ‖c i * ν i A‖) := by
  apply hc.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((ν i).norm_apply_le_one A)

theorem complexChargeSeries_summable {α ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (ν : ι → ComplexUnitCharge α) (A : Set α) :
    Summable (fun i => c i * ν i A) := (complexChargeSeries_summable_norm c hc ν A).of_norm

theorem complexChargeSeries_variation {α ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (ν : ι → ComplexUnitCharge α)
    (F : Finset ℕ) (A : ℕ → Set α)
    (hA : (↑F : Set ℕ).Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∑ j ∈ F, ‖∑' i, c i * ν i (A j)‖ ≤ ∑' i, ‖c i‖ := by
  have hs := hasSum_sum (s := F) (fun j _ => (complexChargeSeries_summable_norm c hc ν (A j)).hasSum)
  calc
    _ ≤ ∑ j ∈ F, ∑' i, ‖c i * ν i (A j)‖ := Finset.sum_le_sum (fun j _ =>
      norm_tsum_le_tsum_norm (complexChargeSeries_summable_norm c hc ν (A j)))
    _ ≤ ∑' i, ‖c i‖ := hasSum_le (fun i => by
      simp_rw [norm_mul,← Finset.mul_sum]
      exact mul_le_of_le_one_right (norm_nonneg _) ((ν i).variation_le F A hA)) hs hc.hasSum

def complexChargeSeries {α ι : Type*} (c : ι → ℂ) (hc : Summable (fun i => ‖c i‖))
    (hbound : (∑' i, ‖c i‖) ≤ 1) (ν : ι → ComplexUnitCharge α) : ComplexUnitCharge α where
  toFun A := ∑' i, c i * ν i A
  map_empty := by simp only [ComplexUnitCharge.map_empty,mul_zero,tsum_zero]
  map_union A B hAB := by
    simp only [ComplexUnitCharge.map_union _ _ _ hAB,mul_add]
    exact (complexChargeSeries_summable c hc ν A).tsum_add (complexChargeSeries_summable c hc ν B)
  variation_le F A hA := (complexChargeSeries_variation c hc ν F A hA).trans hbound

@[simp] theorem complexChargeSeries_apply {α ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (hbound : (∑' i, ‖c i‖) ≤ 1)
    (ν : ι → ComplexUnitCharge α) (A : Set α) :
    complexChargeSeries c hc hbound ν A = ∑' i, c i * ν i A := rfl

def complexLpChargeSeries {α ι : Type*} (c : lp (fun _ : ι => ℂ) 1) (hc : ‖c‖ ≤ 1)
    (ν : ι → ComplexUnitCharge α) : ComplexUnitCharge α :=
  complexChargeSeries c
    (by simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) c).summable)
    (by
      have hs : HasSum (fun i => ‖c i‖) ‖c‖ := by
        simpa only [ENNReal.toReal_one,Real.rpow_one] using
          lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) c
      exact hs.tsum_eq.trans_le hc) ν

@[simp] theorem complexLpChargeSeries_apply {α ι : Type*} (c : lp (fun _ : ι => ℂ) 1)
    (hc : ‖c‖ ≤ 1) (ν : ι → ComplexUnitCharge α) (A : Set α) :
    complexLpChargeSeries c hc ν A = ∑' i, c i * ν i A := rfl

end ThesisCommon
