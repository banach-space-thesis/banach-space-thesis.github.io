import JLMS.L1Restriction
import Mathlib.Topology.Sequences

/-!
# Coordinate compactness for uniformly bounded ℓ¹ rows

Place the rows in a countable product of compact scalar balls, extract a
convergent subsequence, and pass each finite mass bound to the limit. The
limit is absolutely summable. This is the compactness input for Rosenthal's
c₀ restriction argument; it uses only scalar compactness, not weak-star
sequential compactness of the eventual codomain.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_summable_matrix_column_limit (A : ℕ → ℕ → 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ n (t : Finset ℕ), ∑ j ∈ t, ‖A n j‖ ≤ M) :
    ∃ b : ℕ → 𝕜, Summable (fun j => ‖b j‖) ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ j, Tendsto (fun n => A (s n) j) atTop (𝓝 (b j)) := by
  let B := ↥(Metric.closedBall (0 : 𝕜) M)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : 𝕜) M)
  have hentry (n j : ℕ) : A n j ∈ Metric.closedBall (0 : 𝕜) M := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hmass n {j}
  let u (n : ℕ) : ℕ → B := fun j => ⟨A n j, hentry n j⟩
  obtain ⟨v, s, hs, ht⟩ := SeqCompactSpace.tendsto_subseq u
  let b (j : ℕ) : 𝕜 := (v j).val
  have hj (j : ℕ) : Tendsto (fun n => A (s n) j) atTop (𝓝 (b j)) :=
    continuous_subtype_val.tendsto (v j) |>.comp ((tendsto_pi_nhds.mp ht) j)
  have hb (t : Finset ℕ) : ∑ j ∈ t, ‖b j‖ ≤ M := by
    apply le_of_tendsto (tendsto_finset_sum t (fun j _ => (hj j).norm))
    exact Eventually.of_forall (fun n => hmass (s n) t)
  exact ⟨b, summable_of_sum_le (fun _ => norm_nonneg _) hb, s, hs, hj⟩

end JLMS
