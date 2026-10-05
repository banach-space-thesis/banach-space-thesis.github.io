import Posets.AcceptanceDichotomyRowBlocks
import Mathlib.Algebra.Ring.Parity

/-! A single indicator detects nonconvergence of a nonvanishing row sequence. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_nonconvergent_indicator_test (u : ℕ → lp (fun _ : ℕ => 𝕜) 1)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : StrictMono k)
    (hdiag : Tendsto (fun n => u n (k n)) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (hmass : ∀ n, δ ≤ ‖u n‖) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ A : Set ℕ,
      (∀ n, k (r n) ∉ A) ∧
      ¬ ∃ a : 𝕜, Tendsto (fun n => ∑' i, indicator 𝕜 A i * u (r n) i) atTop (𝓝 a) := by
  obtain ⟨r, hr, B, hdisj, havoid, hclose⟩ := exists_disjoint_row_blocks u hu k hk hdiag
    (by positivity : 0 < δ / 32)
  choose F hF hnorm using fun n => exists_subset_four_mul_norm_sum (B n) (fun i => u (r n) i)
  let A : Set ℕ := {i | ∃ n, Even n ∧ i ∈ F n}
  have hb : ∀ i, ‖indicator 𝕜 A i‖ ≤ 1 := by
    intro i; by_cases hi : i ∈ A <;> simp [indicator, hi]
  let φ := ThesisCommon.scalarEllOneTest (indicator 𝕜 A) hb
  let v (n : ℕ) := ∑ i ∈ B n, lp.single 1 i (u (r n) i)
  have hsingle (i : ℕ) (a : 𝕜) : φ (lp.single 1 i a) = indicator 𝕜 A i * a := by
    change (∑' j, indicator 𝕜 A j * lp.single (E := fun _ : ℕ => 𝕜) 1 i a j) = _
    rw [tsum_eq_single i]
    · simp
    · intro j hj
      simp [lp.single_apply, Pi.single, Function.update, hj]
  have hmem (n i : ℕ) (hi : i ∈ B n) : i ∈ A ↔ Even n ∧ i ∈ F n := by
    constructor
    · rintro ⟨m, hm, hiF⟩
      have hmn : m = n := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj hne) (hF m hiF) hi
      subst m
      exact ⟨hm, hiF⟩
    · rintro ⟨hn, hiF⟩
      exact ⟨n, hn, hiF⟩
  have htest (n : ℕ) : φ (v n) = if Even n then ∑ i ∈ F n, u (r n) i else 0 := by
    simp only [v, map_sum, hsingle]
    by_cases hn : Even n
    · rw [if_pos hn]
      calc
        (∑ i ∈ B n, indicator 𝕜 A i * u (r n) i) =
            ∑ i ∈ F n, indicator 𝕜 A i * u (r n) i := by
          symm
          apply Finset.sum_subset (hF n)
          intro i hi hiF
          have hiA : i ∉ A := fun h => hiF ((hmem n i hi).mp h).2
          simp [indicator, hiA]
        _ = ∑ i ∈ F n, u (r n) i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiA : i ∈ A := ⟨n, hn, hi⟩
          simp [indicator, hiA]
    · rw [if_neg hn]
      apply Finset.sum_eq_zero
      intro i hi
      have hiA : i ∉ A := fun h => hn ((hmem n i hi).mp h).1
      simp [indicator, hiA]
  have herr (n : ℕ) : ‖φ (u (r n)) - φ (v n)‖ < δ / 32 := by
    rw [← map_sub]
    exact (ThesisCommon.scalarEllOneTest_bound _ hb _).trans_lt (hclose n)
  have heven (n : ℕ) : δ / 8 ≤ ‖φ (u (r (2 * n)))‖ := by
    have hc := hclose (2 * n)
    have hm := hmass (r (2 * n))
    have hs := hnorm (2 * n)
    have hvnorm : ‖v (2 * n)‖ = ∑ i ∈ B (2 * n), ‖u (r (2 * n)) i‖ := by
      simpa [v] using (lp.norm_sum_single (E := fun _ : ℕ => 𝕜)
        (by norm_num : 0 < (1 : ENNReal).toReal) (fun i => u (r (2 * n)) i) (B (2 * n)))
    have hv := norm_sub_norm_le (u (r (2 * n))) (v (2 * n))
    have he := herr (2 * n)
    have hφ := norm_sub_norm_le (φ (v (2 * n))) (φ (u (r (2 * n))))
    rw [norm_sub_rev] at hφ
    rw [htest, if_pos (even_two_mul n)] at he hφ
    rw [hvnorm] at hv
    change ‖u (r (2 * n)) - v (2 * n)‖ < δ / 32 at hc
    linarith
  have hodd (n : ℕ) : ‖φ (u (r (2 * n + 1)))‖ ≤ δ / 32 := by
    have he := herr (2 * n + 1)
    rw [htest, if_neg (Nat.not_even_two_mul_add_one n), sub_zero] at he
    exact he.le
  refine ⟨r, hr, A, ?_, ?_⟩
  · intro n ⟨m, _, hm⟩
    exact havoid n m (hF m hm)
  · rintro ⟨a, ha⟩
    change Tendsto (fun n => φ (u (r n))) atTop (𝓝 a) at ha
    have he : StrictMono (fun n : ℕ => 2 * n) := by intro m n h; dsimp only; omega
    have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro m n h; dsimp only; omega
    have hlo := ge_of_tendsto (ha.norm.comp he.tendsto_atTop) (Eventually.of_forall heven)
    have hhi := le_of_tendsto (ha.norm.comp ho.tendsto_atTop) (Eventually.of_forall hodd)
    linarith

end Posets
