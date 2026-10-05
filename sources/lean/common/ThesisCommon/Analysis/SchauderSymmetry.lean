import ThesisCommon.Analysis.SchauderBasis

/-! Finite permutation consequences of a symmetric norm. The isometric
behavior on finite subsequences is derived from permutation invariance.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon

/-- A finite part of an injection extends to a permutation, by successively
swapping the new image into place without disturbing earlier images. -/
theorem finite_embedding_extends_permutation {α : Type*} (f : α ↪ α) (F : Finset α) :
    ∃ σ : Equiv.Perm α, ∀ n ∈ F, σ n = f n := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Equiv.refl α, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨σ.trans (Equiv.swap (σ a) (f a)), ?_⟩
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · simp
    · have hna : n ≠ a := fun h => ha (h ▸ hn)
      have h₁ : σ n ≠ σ a := fun h => hna (σ.injective h)
      have h₂ : σ n ≠ f a := by rw [hσ n hn]; exact f.injective.ne hna
      simpa only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hσ n hn

namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

/-- Every finite subsequence identification is isometric in a symmetric norm. -/
theorem finite_subsequence_norm (hb : b.HasSymmetricNorm)
    (f : ℕ ↪ ℕ) (F : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ n ∈ F, a n • b.vector (f n)‖ = ‖∑ n ∈ F, a n • b.vector n‖ := by
  obtain ⟨σ, hσ⟩ := finite_embedding_extends_permutation f F
  calc
    _ = ‖∑ n ∈ F, a n • b.vector (σ n)‖ := by
      congr 1
      exact Finset.sum_congr rfl (fun n hn => by rw [hσ n hn])
    _ = _ := hb.2 σ F a

/-- The unconditional lower-estimate argument in Lemma 3.1, specialized to
a symmetric norm: a functional bounded away from zero on an infinite
subsequence forces equivalence of the entire basis to the ℓ₁ basis.
Unimodular phase alignment is performed coefficientwise, so no scalar sector
subsequence is needed and the same lower estimate has the sharper constant. -/
theorem equivalentEllOne_of_large_functional (hb : b.HasSymmetricNorm)
    (φ : X →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε)
    (hA : {n : ℕ | ε ≤ ‖φ (b.vector n)‖}.Infinite) : b.EquivalentEllOne := by
  classical
  let A : Set ℕ := {n | ε ≤ ‖φ (b.vector n)‖}
  let f : ℕ ↪ ℕ := (hA.natEmbedding A).trans (Function.Embedding.subtype A)
  have hf (n : ℕ) : ε ≤ ‖φ (b.vector (f n))‖ := (hA.natEmbedding A n).property
  have hn (n : ℕ) : φ (b.vector (f n)) ≠ 0 := norm_pos_iff.mp (hε.trans_le (hf n))
  have hφ : 0 < ‖φ‖ := by
    have hh := (hf 0).trans (φ.le_opNorm (b.vector (f 0)))
    rw [b.norm_vector, mul_one] at hh
    exact hε.trans_le hh
  refine ⟨ε / ‖φ‖, div_pos hε hφ, ?_⟩
  intro F a
  let c : ℕ → 𝕜 := fun n => ((ε * ‖a n‖ : ℝ) : 𝕜) / φ (b.vector (f n))
  have hc (n : ℕ) : ‖c n‖ ≤ ‖a n‖ := by
    dsimp [c]
    rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg hε.le (norm_nonneg _))]
    apply (div_le_iff₀ (hε.trans_le (hf n))).mpr
    nlinarith [norm_nonneg (a n), hf n]
  have hnorm : ‖∑ n ∈ F, c n • b.vector (f n)‖ ≤
      ‖∑ n ∈ F, a n • b.vector (f n)‖ := by
    rw [b.finite_subsequence_norm hb, b.finite_subsequence_norm hb]
    simpa only [one_mul] using hb.1.2 F c a (fun n _ => hc n)
  have heval : φ (∑ n ∈ F, c n • b.vector (f n)) =
      ((ε * ∑ n ∈ F, ‖a n‖ : ℝ) : 𝕜) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      _ = ∑ n ∈ F, ((ε * ‖a n‖ : ℝ) : 𝕜) := by
        apply Finset.sum_congr rfl
        intro n _
        exact div_mul_cancel₀ _ (hn n)
      _ = _ := by rw [← RCLike.ofReal_sum, Finset.mul_sum]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).mpr
  calc
    ε * ∑ n ∈ F, ‖a n‖ = ‖φ (∑ n ∈ F, c n • b.vector (f n))‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    _ ≤ ‖φ‖ * ‖∑ n ∈ F, c n • b.vector (f n)‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖∑ n ∈ F, a n • b.vector (f n)‖ :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = ‖∑ n ∈ F, a n • b.vector n‖ * ‖φ‖ := by
      rw [b.finite_subsequence_norm hb, mul_comm]

/-- A symmetric basis not equivalent to the ℓ₁ basis is weakly null.
This discharges the weak-null input of the gliding-hump selection in 3.3. -/
theorem weakly_null_of_not_equivalentEllOne (hb : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (φ : X →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  simp only [dist_zero_right]
  by_contra h
  push_neg at h
  have hA : {n : ℕ | ε ≤ ‖φ (b.vector n)‖}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hn, hh⟩ := h (N + 1)
    exact ⟨n, hh, by omega⟩
  exact hnot (b.equivalentEllOne_of_large_functional hb φ hε hA)

end NormalizedSchauderBasis
end ThesisCommon
