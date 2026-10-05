import JLMS.DualFiniteBlocks
import JLMS.EllOneFiniteLower

/-!
# Ordered normalized coefficient blocks

An ordered block system records finite supports, scalar coefficients with
total absolute mass one, and separation of successive supports. The tail
property ensures that pointwise null sequences remain null under blocking.
This is the reusable combinatorial interface for the Hagler–Johnson proof.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable (𝕜 : Type*) [RCLike 𝕜]

structure NormalizedBlockSystem where
  support : ℕ → Finset ℕ
  coefficient : ℕ → ℕ → 𝕜
  mass_one : ∀ n, ∑ k ∈ support n, ‖coefficient n k‖ = 1
  ordered : ∀ n m, n < m → ∀ i ∈ support n, ∀ j ∈ support m, i < j

variable {𝕜}

theorem NormalizedBlockSystem.support_nonempty (b : NormalizedBlockSystem 𝕜) (n : ℕ) :
    (b.support n).Nonempty := by
  by_contra h
  have he : b.support n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hm := b.mass_one n
  simp [he] at hm

theorem NormalizedBlockSystem.disjoint (b : NormalizedBlockSystem 𝕜) :
    Pairwise fun n m => Disjoint (b.support n) (b.support m) := by
  intro n m hnm
  apply Finset.disjoint_left.mpr
  intro k hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact (lt_irrefl k) (b.ordered n m h k hn k hm)
  · exact (lt_irrefl k) (b.ordered m n h k hm k hn)

theorem NormalizedBlockSystem.index_le_support (b : NormalizedBlockSystem 𝕜)
    (n k : ℕ) (hk : k ∈ b.support n) : n ≤ k := by
  induction n generalizing k with
  | zero => exact Nat.zero_le k
  | succ n ih =>
    obtain ⟨i, hi⟩ := b.support_nonempty n
    have hin := ih i hi
    have hik := b.ordered n (n + 1) (Nat.lt_succ_self n) i hi k hk
    omega

def NormalizedBlockSystem.applyDual {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (b : NormalizedBlockSystem 𝕜) (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) : X →L[𝕜] 𝕜 :=
  dualFiniteBlock f (b.support n) (b.coefficient n)

theorem NormalizedBlockSystem.norm_applyDual_le {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (b : NormalizedBlockSystem 𝕜)
    (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) :
    ‖b.applyDual f n‖ ≤ C := norm_dualFiniteBlock_le _ _ _ hf (b.mass_one n)

theorem NormalizedBlockSystem.pointwise_null {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (b : NormalizedBlockSystem 𝕜)
    (f : ℕ → (X →L[𝕜] 𝕜))
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    ∀ x, Tendsto (fun n => b.applyDual f n x) atTop (𝓝 0) := by
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hf x) (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_zero_right]
  have hsum : ‖b.applyDual f n x‖ ≤ ∑ k ∈ b.support n, ‖b.coefficient n k‖ * ‖f k x‖ := by
    change ‖dualFiniteBlock f (b.support n) (b.coefficient n) x‖ ≤ _
    simp only [dualFiniteBlock, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  calc
    _ ≤ ∑ k ∈ b.support n, ‖b.coefficient n k‖ * ‖f k x‖ := hsum
    _ ≤ ∑ k ∈ b.support n, ‖b.coefficient n k‖ * (ε / 2) := Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (by
        have h := hN k (hn.trans (b.index_le_support n k hk))
        simpa only [dist_zero_right] using h.le) (norm_nonneg _))
    _ = ε / 2 := by rw [← Finset.sum_mul, b.mass_one, one_mul]
    _ < ε := half_lt_self hε

end JLMS
