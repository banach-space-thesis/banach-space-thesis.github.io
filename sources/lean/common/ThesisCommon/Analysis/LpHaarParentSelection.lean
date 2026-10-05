import ThesisCommon.Analysis.LpHaarDyadicRefinement
import ThesisCommon.Analysis.LpHaarBlockReaderDecay

/-! A concrete interference-small Haar block inside any nonempty finite
dyadic parent. Refinement preserves the parent exactly, and the two signed
children split it into equal-measure measurable pieces. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

def lpHaarRefineAt (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀))) (n : ℕ) :
    Finset (Fin (2 ^ n)) :=
  if hn : n₀ ≤ n then (Nat.add_sub_of_le hn) ▸ lpHaarRefine n₀ S (n - n₀) else ∅

theorem lpHaarRefineAt_parent (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀)))
    (n : ℕ) (hn : n₀ ≤ n) :
    lpHaarBlockParent n (lpHaarRefineAt n₀ S n) = lpHaarBlockParent n₀ S := by
  unfold lpHaarRefineAt
  simp only [dif_pos hn]
  have htransport (m l : ℕ) (h : m = l) (A : Finset (Fin (2 ^ m))) :
      lpHaarBlockParent l (h ▸ A) = lpHaarBlockParent m A := by
    cases h
    rfl
  exact (htransport (n₀ + (n - n₀)) n (Nat.add_sub_of_le hn)
    (lpHaarRefine n₀ S (n - n₀))).trans (lpHaarBlockParent_refine n₀ S (n - n₀))

theorem lpHaarRefineAt_mass (n₀ : ℕ) (S : Finset (Fin (2 ^ n₀)))
    (n : ℕ) (hn : n₀ ≤ n) :
    ((lpHaarRefineAt n₀ S n).card : ℝ) * intervalLpDyadicRadius n =
      (S.card : ℝ) * intervalLpDyadicRadius n₀ := by
  rw [← lpHaarBlockParent_real_measure, lpHaarRefineAt_parent n₀ S n hn,
    lpHaarBlockParent_real_measure]

theorem lpHaarParent_select_small (𝕜 : Type*) [RCLike 𝕜]
    (p : BanachExponent) (hp : p.val ≠ ∞) {a b : ℕ}
    (φ : Fin a → IntervalLp 𝕜 p →L[𝕜] 𝕜) (f : Fin b → IntervalLp 𝕜 p)
    (n₀ : ℕ) (S₀ : Finset (Fin (2 ^ n₀))) (hS₀ : S₀.Nonempty)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n ≥ N, ∃ S : Finset (Fin (2 ^ n)), ∃ θ : Fin (2 ^ n) → Bool,
      S.Nonempty ∧ lpHaarBlockParent n S = lpHaarBlockParent n₀ S₀ ∧
      (∀ r, ‖φ r (lpHaarSignedBlock 𝕜 p n S θ)‖ < ε) ∧
      ∀ r, ‖lpHaarSignedBlockReader 𝕜 p n S θ (f r)‖ < ε := by
  let m : ℝ := (S₀.card : ℝ) * intervalLpDyadicRadius n₀
  have hm : 0 < m := mul_pos (by exact_mod_cast Finset.card_pos.mpr hS₀)
    (intervalLpDyadicRadius_pos n₀)
  have hmass : ∀ᶠ n in atTop,
      m ≤ (lpHaarRefineAt n₀ S₀ n).card * intervalLpDyadicRadius n := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact le_of_eq (lpHaarRefineAt_mass n₀ S₀ n hn).symm
  obtain ⟨n, hn, θ, hf, hb⟩ := lpHaarSignedBlock_two_sided_small 𝕜 p hp φ f
    (lpHaarRefineAt n₀ S₀) hm hε hmass (max N n₀)
  have hn₀ : n₀ ≤ n := (le_max_right N n₀).trans hn
  have hnonempty : (lpHaarRefineAt n₀ S₀ n).Nonempty := by
    by_contra h
    have hz : (lpHaarRefineAt n₀ S₀ n).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    have hm' := lpHaarRefineAt_mass n₀ S₀ n hn₀
    simp only [hz, Nat.cast_zero, zero_mul] at hm'
    change 0 = m at hm'
    linarith
  exact ⟨n, (le_max_left N n₀).trans hn, lpHaarRefineAt n₀ S₀ n, θ,
    hnonempty, lpHaarRefineAt_parent n₀ S₀ n hn₀, hf, hb⟩

end ThesisCommon
