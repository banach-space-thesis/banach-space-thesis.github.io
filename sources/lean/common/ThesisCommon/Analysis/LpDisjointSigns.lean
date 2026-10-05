import ThesisCommon.Analysis.DisjointSequenceBlocks
import ThesisCommon.Analysis.SignAveraging

/-! Exact power additivity for disjoint finite-p vectors, and the signed
N^(1/p) bound used in the ell1 self-similarity reductions. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_disjoint_signed_sum_rpow {ι : Type*} [Fintype ι]
    (x : ι → X) (hdis : ∀ i j, i ≠ j → x i = 0 ∨ x j = 0)
    (θ : ι → Bool) {r : ℝ} (hr : 0 < r) :
    ‖∑ i, signedValue (θ i) (x i)‖ ^ r = ∑ i, ‖x i‖ ^ r := by
  classical
  by_cases h : ∃ i, x i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, j ≠ i → x j = 0 := fun j hj => (hdis i j hj.symm).resolve_left hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp only [signedValue]; split_ifs <;> simp
    · intro j _ hj; simp [hz j hj, Real.zero_rpow hr.ne']
    · simp
    · intro j _ hj; simp [signedValue, hz j hj]
    · simp
  · push_neg at h
    simp [signedValue, h, Real.zero_rpow hr.ne']

theorem lp_disjoint_sign_sum_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    {ι κ : Type*} [Fintype ι] (x : ι → lp (fun _ : κ => X) p)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) (θ : ι → Bool) :
    ‖∑ i, signedValue (θ i) (x i)‖ ^ p.toReal = ∑ i, ‖x i‖ ^ p.toReal := by
  classical
  rw [lp.norm_rpow_eq_tsum hp]
  calc
    _ = ∑' k, ∑ i, ‖x i k‖ ^ p.toReal := by
      apply tsum_congr
      intro k
      have heq : (∑ i, signedValue (θ i) (x i)) k = ∑ i, signedValue (θ i) (x i k) := by
        simp only [signedValue, lp.coeFn_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> rfl
      rw [heq]
      exact norm_disjoint_signed_sum_rpow _ (fun i j hij => hdis i j hij k) θ hp
    _ = ∑ i, ∑' k, ‖x i k‖ ^ p.toReal :=
      Summable.tsum_finsetSum (fun i _ => (lp.memℓp (x i)).summable hp)
    _ = _ := Finset.sum_congr rfl (fun i _ => (lp.norm_rpow_eq_tsum hp (x i)).symm)

theorem lp_disjoint_sign_sum_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    {n : ℕ} (x : Fin n → lp (fun _ : ℕ => X) p) (hx : ∀ i, ‖x i‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ k, x i k = 0 ∨ x j k = 0) (θ : Fin n → Bool) :
    ‖∑ i, signedValue (θ i) (x i)‖ ≤ (n : ℝ) ^ (1 / p.toReal) := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hp).mp
  rw [lp_disjoint_sign_sum_rpow hp x hdis θ, ← Real.rpow_mul (Nat.cast_nonneg n),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) ^ p.toReal := Finset.sum_le_sum (fun i _ =>
      Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le)
    _ = n := by simp

theorem lpExtend_disjoint {p : ℝ≥0∞} [Fact (1 ≤ p)] {i j : ℕ} (hij : i ≠ j)
    (x y : lp (fun _ : ℕ => X) p) (k : ℕ) :
    lpExtend (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x k = 0 ∨
      lpExtend (𝕜 := 𝕜) p (disjointCoordinateEmbedding j) y k = 0 := by
  classical
  change Function.extend (disjointCoordinateEmbedding i) x 0 k = 0 ∨
    Function.extend (disjointCoordinateEmbedding j) y 0 k = 0
  by_cases hi : ∃ a, disjointCoordinateEmbedding i a = k
  · right
    obtain ⟨a, ha⟩ := hi
    have hj : ¬ ∃ b, disjointCoordinateEmbedding j b = k := by
      rintro ⟨b, hb⟩
      exact hij (disjointCoordinateEmbedding_disjoint (ha.trans hb.symm))
    simp [Function.extend_apply' _ _ _ hj]
  · left
    simp [Function.extend_apply' _ _ _ hi]

theorem lp_disjoint_blocks_sign_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    {n : ℕ} (x : Fin n → lp (fun _ : ℕ => X) p) (hx : ∀ i, ‖x i‖ ≤ 1)
    (θ : Fin n → Bool) :
    ‖∑ i, signedValue (θ i) (lpExtend (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (x i))‖ ≤
      (n : ℝ) ^ (1 / p.toReal) := by
  apply lp_disjoint_sign_sum_le hp
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (x i)) _ _ θ
  · intro i
    have hE := norm_lpExtend_le (𝕜 := 𝕜) (X := X) (p := p) (disjointCoordinateEmbedding i)
    exact ((lpExtend (𝕜 := 𝕜) p (disjointCoordinateEmbedding i)).le_opNorm (x i)).trans
      (by simpa using mul_le_mul hE (hx i) (norm_nonneg (x i)) zero_le_one)
  · intro i j hij k
    exact lpExtend_disjoint (fun heq => hij (Fin.ext heq)) (x i) (x j) k

end ThesisCommon


