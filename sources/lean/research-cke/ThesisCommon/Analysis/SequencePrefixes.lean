import ThesisCommon.Analysis.SequenceEmbeddingAlgebra

/-! Actual finite-prefix truncations, with the complementary infinite tail. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Keep the coordinates 0,...,k and set the others to zero. -/
def lpPrefix {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lp (fun _ : ℕ => X) p :=
  ⟨fun n => if n ≤ k then x n else 0,
    mem_lp_of_norm_le_mul x _ zero_le_one (fun n => by split_ifs <;> simp)⟩

/-- The same finite-prefix truncation of a null sequence. -/
def cZeroPrefix (k : ℕ) (x : CZeroSum X) : CZeroSum X :=
  cZeroOfDominated x (fun n => if n ≤ k then x n else 0)
    (C := 1) (fun n => by dsimp; split_ifs <;> simp)

private theorem tail_extend_restrict (x : ℕ → X) (k n : ℕ) :
    Function.extend (coordinateTail (Function.Embedding.refl ℕ) k)
      (fun j => x (k + 1 + j)) 0 n = if n ≤ k then 0 else x n := by
  classical
  by_cases hn : n ≤ k
  · have hnot : ¬ ∃ j, coordinateTail (Function.Embedding.refl ℕ) k j = n := by
      rintro ⟨j, hj⟩
      change k + 1 + j = n at hj
      omega
    simp [Function.extend_apply' _ _ _ hnot, hn]
  · have heq : k + 1 + (n - (k + 1)) = n := by omega
    have himage : coordinateTail (Function.Embedding.refl ℕ) k (n - (k + 1)) = n := heq
    rw [← himage, Function.Injective.extend_apply (coordinateTail (Function.Embedding.refl ℕ) k).injective]
    simp only [himage, heq, if_neg hn]

/-- Finite prefix plus actual zero-inserted tail equals the whole lp vector. -/
theorem lpPrefix_add_tail {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lpPrefix k x + lpExtend (𝕜 := 𝕜) p (coordinateTail (Function.Embedding.refl ℕ) k)
      (lpRestrict (𝕜 := 𝕜) p (coordinateTail (Function.Embedding.refl ℕ) k) x) = x := by
  ext n
  change (if n ≤ k then x n else 0) + Function.extend
    (coordinateTail (Function.Embedding.refl ℕ) k) (fun j => x (k + 1 + j)) 0 n = x n
  rw [tail_extend_restrict]
  split_ifs <;> simp

/-- Finite prefix plus actual zero-inserted tail equals the whole c₀ vector. -/
theorem cZeroPrefix_add_tail (k : ℕ) (x : CZeroSum X) :
    cZeroPrefix k x + cZeroExtend (𝕜 := 𝕜) (coordinateTail (Function.Embedding.refl ℕ) k)
      (cZeroRestrict (𝕜 := 𝕜) (coordinateTail (Function.Embedding.refl ℕ) k) x) = x := by
  ext n
  change (if n ≤ k then x n else 0) + Function.extend
    (coordinateTail (Function.Embedding.refl ℕ) k) (fun j => x (k + 1 + j)) 0 n = x n
  rw [tail_extend_restrict]
  split_ifs <;> simp

/-- The prefix has exactly its finite single-coordinate expansion. -/
theorem lpPrefix_eq_sum_single {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (k : ℕ) (x : lp (fun _ : ℕ => X) p) :
    lpPrefix k x = ∑ j ∈ Finset.range (k + 1), lp.single p j (x j) := by
  ext n
  simp only [lpPrefix, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range, Nat.lt_succ_iff]

end ThesisCommon
