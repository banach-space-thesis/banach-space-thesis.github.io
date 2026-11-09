import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Uniform summable coordinate domination for increasing finite variations. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace PL1.DyadicCoordinateDomination

theorem exists_summable_majorant (a : ℕ → ℕ → ℝ) (C : ℝ)
    (ha : ∀ m n, 0 ≤ a m n)
    (hmono : ∀ n, Monotone (fun m => a m n))
    (hbound : ∀ m (s : Finset ℕ), ∑ n ∈ s, a m n ≤ C) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧
      (∀ m n, a m n ≤ b n) ∧ ∑' n, b n ≤ C := by
  classical
  have hab (m n : ℕ) : a m n ≤ C := by
    simpa using hbound m {n}
  have hbdd (n : ℕ) : BddAbove (Set.range (fun m => a m n)) :=
    ⟨C, by rintro y ⟨m, rfl⟩; exact hab m n⟩
  let b : ℕ → ℝ := fun n => sSup (Set.range (fun m => a m n))
  have hle (m n : ℕ) : a m n ≤ b n := le_csSup (hbdd n) (Set.mem_range_self m)
  have hb (n : ℕ) : 0 ≤ b n := (ha 0 n).trans (hle 0 n)
  have ht (n : ℕ) : Tendsto (fun m => a m n) atTop (𝓝 (b n)) :=
    tendsto_atTop_ciSup (hmono n) (hbdd n)
  have hsum (s : Finset ℕ) : ∑ n ∈ s, b n ≤ C := by
    apply le_of_tendsto (tendsto_finsetSum s (fun n _ => ht n))
    exact Filter.Eventually.of_forall (fun m => hbound m s)
  have hs : Summable b := summable_of_sum_le hb hsum
  exact ⟨b, hs, hb, hle, hs.tsum_le_of_sum_le hsum⟩

theorem tendsto_tsum_zero_of_increasing_majorants
    (a u : ℕ → ℕ → ℝ) (C : ℝ)
    (ha : ∀ m n, 0 ≤ a m n)
    (hmono : ∀ n, Monotone (fun m => a m n))
    (hbound : ∀ m (s : Finset ℕ), ∑ n ∈ s, a m n ≤ C)
    (hu : ∀ m n, 0 ≤ u m n) (hua : ∀ m n, u m n ≤ a m n)
    (ht : ∀ n, Tendsto (fun m => u m n) atTop (𝓝 0)) :
    Tendsto (fun m => ∑' n, u m n) atTop (𝓝 0) := by
  obtain ⟨b, hb, hb0, hab, _⟩ := exists_summable_majorant a C ha hmono hbound
  have hd (m n : ℕ) : ‖u m n‖ ≤ b n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hu m n)]
    exact (hua m n).trans (hab m n)
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb ht
    (Filter.Eventually.of_forall (fun m n => hd m n))

end PL1.DyadicCoordinateDomination
