import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative finite complex coefficient selection. Real and imaginary
positive/negative parts supply a subset whose sum retains at least a quarter
of the total coefficient mass. This is an ingredient of complex Rosenthal
selection; it does not itself assert the infinite subsequence dichotomy. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

theorem real_coefficient_mass_le_two {ι : Type*} (F : Finset ι) (a : ι → ℝ)
    (C : ℝ) (hC : ∀ S : Finset ι, S ⊆ F → |∑ i ∈ S, a i| ≤ C) :
    ∑ i ∈ F, |a i| ≤ 2 * C := by
  classical
  let P := F.filter (fun i => 0 ≤ a i)
  let N := F.filter (fun i => ¬ 0 ≤ a i)
  have hp : (∑ i ∈ P, |a i|) = ∑ i ∈ P, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (Finset.mem_filter.mp hi).2
  have hn : (∑ i ∈ N, |a i|) = -(∑ i ∈ N, a i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
  have hsplit : (∑ i ∈ P, |a i|) + (∑ i ∈ N, |a i|) = ∑ i ∈ F, |a i| :=
    Finset.sum_filter_add_sum_filter_not F (fun i => 0 ≤ a i) (fun i => |a i|)
  calc
    _ = (∑ i ∈ P, a i) - ∑ i ∈ N, a i := by rw [← hsplit, hp, hn]; rfl
    _ ≤ |∑ i ∈ P, a i| + |∑ i ∈ N, a i| := by
      simpa only [sub_eq_add_neg] using
        add_le_add (le_abs_self (∑ i ∈ P, a i)) (neg_le_abs (∑ i ∈ N, a i))
    _ ≤ C + C := add_le_add (hC P (Finset.filter_subset _ _))
      (hC N (Finset.filter_subset _ _))
    _ = 2 * C := by ring

theorem exists_complex_coefficient_subset {ι : Type*} (F : Finset ι) (a : ι → ℂ) :
    ∃ S : Finset ι, S ⊆ F ∧ (∑ i ∈ F, ‖a i‖) / 4 ≤ ‖∑ i ∈ S, a i‖ := by
  classical
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image F.powerset
    (fun S : Finset ι => ‖∑ i ∈ S, a i‖)
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset F)⟩
  have hb (U : Finset ι) (hU : U ⊆ F) :
      ‖∑ i ∈ U, a i‖ ≤ ‖∑ i ∈ S, a i‖ := hmax U (Finset.mem_powerset.mpr hU)
  have hr : (∑ i ∈ F, |(a i).re|) ≤ 2 * ‖∑ i ∈ S, a i‖ := by
    apply real_coefficient_mass_le_two
    intro U hU
    rw [← Complex.re_sum]
    exact (Complex.abs_re_le_norm _).trans (hb U hU)
  have hi : (∑ i ∈ F, |(a i).im|) ≤ 2 * ‖∑ i ∈ S, a i‖ := by
    apply real_coefficient_mass_le_two
    intro U hU
    rw [← Complex.im_sum]
    exact (Complex.abs_im_le_norm _).trans (hb U hU)
  have hm : (∑ i ∈ F, ‖a i‖) ≤ (∑ i ∈ F, |(a i).re|) + ∑ i ∈ F, |(a i).im| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => Complex.norm_le_abs_re_add_abs_im (a i))
  refine ⟨S, Finset.mem_powerset.mp hS, ?_⟩
  linarith

theorem exists_complex_unit_mass_subset {ι : Type*} (F : Finset ι) (a : ι → ℂ)
    (ha : (∑ i ∈ F, ‖a i‖) = 1) :
    ∃ S : Finset ι, S ⊆ F ∧ (1 / 4 : ℝ) ≤ ‖∑ i ∈ S, a i‖ := by
  simpa only [ha] using exists_complex_coefficient_subset F a

end SurveyStatements.P1
