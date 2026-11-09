import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.CZeroOperators
import Mathlib.Data.Nat.Pairing

/-! Disjoint blocks with uniformly bounded signed sums in c₀ and ℓ∞.
These are the actual coordinate witnesses for the cotype reductions.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Infinitely many pairwise disjoint infinite coordinate sets, enumerated
using the pairing function. Only finitely many are used at each cotype step. -/
def disjointCoordinateEmbedding (i : ℕ) : ℕ ↪ ℕ where
  toFun := Nat.pair i
  inj' := fun _ _ h => (Nat.pair_eq_pair.mp h).2

theorem disjointCoordinateEmbedding_disjoint {i j a b : ℕ}
    (h : disjointCoordinateEmbedding i a = disjointCoordinateEmbedding j b) : i = j :=
  (Nat.pair_eq_pair.mp h).1

/-- At most one nonzero summand survives at each coordinate. -/
theorem norm_sign_sum_apply_le {ι κ : Type*} [Fintype ι]
    (f : ι → κ → X) (hf : ∀ i k, ‖f i k‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, f i k = 0 ∨ f j k = 0)
    (θ : ι → Bool) (k : κ) :
    ‖∑ i, if θ i then f i k else -f i k‖ ≤ 1 := by
  classical
  by_cases h : ∃ i, f i k ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · split_ifs <;> simpa only [norm_neg] using hf i k
    · intro j _ hj
      have hz := (hdis i j hj.symm k).resolve_left hi
      simp [hz]
    · simp
  · push_neg at h
    simp [h]

/-- Any signed sum of disjoint unit vectors has sup norm at most one. -/
theorem infinity_norm_sign_sum_le {ι κ : Type*} [Fintype ι]
    (x : ι → lp (fun _ : κ => X) ∞) (hx : ∀ i, ‖x i‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) (θ : ι → Bool) :
    ‖∑ i, if θ i then x i else -x i‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  intro k
  have hb := norm_sign_sum_apply_le (fun i k => x i k)
    (fun i k => (lp.norm_apply_le_norm ENNReal.top_ne_zero (x i) k).trans (hx i)) hdis θ k
  convert hb using 1; simp
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- The identical coordinate argument works in the actual c₀ norm. -/
theorem cZero_norm_sign_sum_le {ι : Type*} [Fintype ι]
    (x : ι → CZeroSum X) (hx : ∀ i, ‖x i‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) (θ : ι → Bool) :
    ‖∑ i, if θ i then x i else -x i‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro k
  have hb := norm_sign_sum_apply_le (fun i k => x i k)
    (fun i k => (BoundedContinuousFunction.norm_coe_le_norm (x i).toBCF k).trans (hx i)) hdis θ k
  convert hb using 1; simp
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

private theorem extend_disjoint {i j : ℕ} (hij : i ≠ j) (f g : ℕ → X) (k : ℕ) :
    Function.extend (disjointCoordinateEmbedding i) f 0 k = 0 ∨
    Function.extend (disjointCoordinateEmbedding j) g 0 k = 0 := by
  classical
  by_cases hi : ∃ a, disjointCoordinateEmbedding i a = k
  · right
    obtain ⟨a, ha⟩ := hi
    have hj : ¬ ∃ b, disjointCoordinateEmbedding j b = k := by
      rintro ⟨b, hb⟩
      exact hij (disjointCoordinateEmbedding_disjoint (ha.trans hb.symm))
    simp [Function.extend_apply' _ _ _ hj]
  · left
    simp [Function.extend_apply' _ _ _ hi]

/-- Canonical infinite ℓ∞ blocks satisfy the signed-sum hypothesis. -/
theorem infinity_disjoint_blocks_sign_bound {n : ℕ}
    (x : Fin n → EllInfinitySum X) (hx : ∀ i, ‖x i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then lpExtend (𝕜 := 𝕜) ∞ (disjointCoordinateEmbedding i) (x i)
      else -(lpExtend (𝕜 := 𝕜) ∞ (disjointCoordinateEmbedding i) (x i))‖ ≤ 1 := by
  apply infinity_norm_sign_sum_le _ _ _ θ
  · intro i
    have hE := norm_lpExtend_le (𝕜 := 𝕜) (X := X) (p := ∞) (disjointCoordinateEmbedding i)
    exact ((lpExtend (𝕜 := 𝕜) (X := X) ∞ (disjointCoordinateEmbedding i)).le_opNorm (x i)).trans
      (by nlinarith [norm_nonneg (x i), hx i])
  · intro i j hij k
    exact extend_disjoint (fun heq => hij (Fin.ext heq)) (x i) (x j) k

/-- Canonical infinite c₀ blocks satisfy the signed-sum hypothesis. -/
theorem cZero_disjoint_blocks_sign_bound {n : ℕ}
    (x : Fin n → CZeroSum X) (hx : ∀ i, ‖x i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then cZeroExtend (𝕜 := 𝕜) (disjointCoordinateEmbedding i) (x i)
      else -(cZeroExtend (𝕜 := 𝕜) (disjointCoordinateEmbedding i) (x i))‖ ≤ 1 := by
  apply cZero_norm_sign_sum_le _ _ _ θ
  · intro i
    have hE := norm_cZeroExtend_le (𝕜 := 𝕜) (X := X) (disjointCoordinateEmbedding i)
    exact ((cZeroExtend (𝕜 := 𝕜) (X := X) (disjointCoordinateEmbedding i)).le_opNorm (x i)).trans
      (by nlinarith [norm_nonneg (x i), hx i])
  · intro i j hij k
    exact extend_disjoint (fun heq => hij (Fin.ext heq)) (x i) (x j) k

/-- Finite single-coordinate blocks in ℓ∞ have the same signed-sum bound. -/
theorem infinity_single_blocks_sign_bound {n : ℕ}
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => X) ∞ i (x i)
      else -(lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => X) ∞ i (x i))‖ ≤ 1 := by
  apply infinity_norm_sign_sum_le _ _ _ θ
  · intro i
    simpa only [lp.singleContinuousLinearMap_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞)] using hx i
  · intro i j hij k
    by_cases hik : i = k
    · subst k
      right
      simp [lp.singleContinuousLinearMap_apply, hij]
    · left
      simp [lp.singleContinuousLinearMap_apply, Ne.symm hik]

end ThesisCommon
