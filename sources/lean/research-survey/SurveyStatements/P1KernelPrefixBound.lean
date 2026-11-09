import SurveyStatements.P1KernelNormingFamilies
import SurveyStatements.P1BasicCriterion
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A summable budget of evaluations by finite norming families gives one
uniform bound for all basis projections. The maximum of the finite family
of partial sums avoids assuming the desired projection bound in its proof. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem kernel_norming_uniform_prefix_bound
    (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (F : ℕ → Finset (StrongDual ℂ X)) {d : ℝ} (hd : 0 < d)
    (hFbound : ∀ N f, f ∈ F N → ‖f‖ ≤ 1)
    (hFnorm : ∀ N, ∀ x ∈ Submodule.span ℂ (e '' (Finset.range N : Set ℕ)),
      x ≠ 0 → ∃ f ∈ F N, d * ‖x‖ < ‖f x‖)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hbudget : ∀ M, ∑ i ∈ Finset.range M, ε i ≤ d / 4)
    (hfuture : ∀ N i, N ≤ i → ∀ f ∈ F N, ‖f (e i)‖ ≤ ε i) :
    ∀ N M, N ≤ M → ∀ a : ℕ → ℂ,
      (d / 2) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
  classical
  intro N M hNM a
  obtain ⟨K, hK, hmax⟩ := (Finset.range (M + 1)).exists_max_image
    (fun j => ‖sequencePartialSum e a j‖) ⟨0, by simp⟩
  have hKM : K ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hK
  let S : ℝ := ‖sequencePartialSum e a K‖
  have hS : 0 ≤ S := norm_nonneg _
  have hmax' (j : ℕ) (hj : j ≤ M) : ‖sequencePartialSum e a j‖ ≤ S :=
    hmax j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hcoeff (i : ℕ) (hi : i < M) : ‖a i‖ ≤ 2 * S := by
    have hdiff : a i • e i =
        sequencePartialSum e a (i + 1) - sequencePartialSum e a i := by
      simp [sequencePartialSum, Finset.sum_range_succ]
    calc
      ‖a i‖ = ‖a i • e i‖ := by rw [norm_smul, he i, mul_one]
      _ ≤ ‖sequencePartialSum e a (i + 1)‖ + ‖sequencePartialSum e a i‖ := by
        rw [hdiff]
        exact norm_sub_le _ _
      _ ≤ S + S := add_le_add (hmax' _ (by omega)) (hmax' _ (by omega))
      _ = 2 * S := by ring
  have hSbound : (d / 2) * S ≤ ‖sequencePartialSum e a M‖ := by
    by_cases hx : sequencePartialSum e a K = 0
    · simp [S, hx, norm_nonneg]
    have hxspan : sequencePartialSum e a K ∈
        Submodule.span ℂ (e '' (Finset.range K : Set ℕ)) := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    obtain ⟨f, hf, hfx⟩ := hFnorm K _ hxspan hx
    have hdecomp : sequencePartialSum e a M = sequencePartialSum e a K +
        ∑ i ∈ Finset.Ico K M, a i • e i :=
      (Finset.sum_range_add_sum_Ico (fun i => a i • e i) hKM).symm
    have htail : ‖f (∑ i ∈ Finset.Ico K M, a i • e i)‖ ≤ (d / 2) * S := by
      calc
        _ = ‖∑ i ∈ Finset.Ico K M, a i • f (e i)‖ := by
          rw [map_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact f.map_smul _ _
        _ ≤ ∑ i ∈ Finset.Ico K M, ‖a i • f (e i)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ico K M, (2 * S) * ε i := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul]
          exact mul_le_mul (hcoeff i (Finset.mem_Ico.mp hi).2)
            (hfuture K i (Finset.mem_Ico.mp hi).1 f hf)
            (norm_nonneg _) (by positivity)
        _ = (2 * S) * ∑ i ∈ Finset.Ico K M, ε i := by rw [Finset.mul_sum]
        _ ≤ (2 * S) * (d / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
            (fun i _ _ => hε i)).trans (hbudget M)
        _ = (d / 2) * S := by ring
    have hnear : ‖f (sequencePartialSum e a K)‖ ≤
        ‖sequencePartialSum e a M‖ + (d / 2) * S := by
      calc
        _ = ‖f (sequencePartialSum e a M) -
            f (∑ i ∈ Finset.Ico K M, a i • e i)‖ := by
          rw [hdecomp, map_add, add_sub_cancel_right]
        _ ≤ ‖f (sequencePartialSum e a M)‖ +
            ‖f (∑ i ∈ Finset.Ico K M, a i • e i)‖ := norm_sub_le _ _
        _ ≤ ‖sequencePartialSum e a M‖ + (d / 2) * S := by
          apply add_le_add _ htail
          exact (f.le_opNorm _).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (hFbound K f hf) (norm_nonneg _))
    change d * S < _ at hfx
    linarith
  exact (mul_le_mul_of_nonneg_left (hmax' N hNM) (by positivity)).trans hSbound

end SurveyStatements.P1
