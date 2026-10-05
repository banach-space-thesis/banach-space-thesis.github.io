import ThesisCommon.Analysis.LpHaarBlockReaders
import ThesisCommon.Analysis.LpHaarBackwardSelection
import ThesisCommon.Analysis.LpHaarSubsetSignSelection

/-! Two-sided finite interference selection for actual signed Haar blocks.
Backward estimates hold uniformly in the signs, once the selected parents
have a fixed positive measure. Forward estimates use the finite sign moment. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem lpHaarSignedBlockReader_norm_le (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (f : IntervalLp 𝕜 p) :
    ‖lpHaarSignedBlockReader 𝕜 p n S θ f‖ ≤
      (S.card : ℝ)⁻¹ * ∑ k ∈ S, ‖lpHaarDyadicCoefficient 𝕜 p n k f‖ := by
  rw [lpHaarSignedBlockReader_apply, norm_mul, norm_inv]
  have hc : ‖(S.card : 𝕜)‖ = (S.card : ℝ) := by simp
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ k ∈ S, ‖signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      cases θ k <;> simp [signedValue]

theorem lpHaarSignedBlockReader_mass_bound (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (hS : S.Nonempty) (θ : Fin (2 ^ n) → Bool) (f : IntervalLp 𝕜 p) :
    ((S.card : ℝ) * intervalLpDyadicRadius n) *
        ‖lpHaarSignedBlockReader 𝕜 p n S θ f‖ ≤
      ∑ k : Fin (2 ^ n), intervalLpDyadicRadius n *
        ‖lpHaarDyadicCoefficient 𝕜 p n k f‖ := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  calc
    _ ≤ ((S.card : ℝ) * intervalLpDyadicRadius n) *
        ((S.card : ℝ)⁻¹ * ∑ k ∈ S, ‖lpHaarDyadicCoefficient 𝕜 p n k f‖) :=
      mul_le_mul_of_nonneg_left (lpHaarSignedBlockReader_norm_le 𝕜 p n S θ f)
        (mul_nonneg (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le)
    _ = intervalLpDyadicRadius n * ∑ k ∈ S, ‖lpHaarDyadicCoefficient 𝕜 p n k f‖ := by
      field_simp
    _ = ∑ k ∈ S, intervalLpDyadicRadius n * ‖lpHaarDyadicCoefficient 𝕜 p n k f‖ :=
      Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun k _ _ => mul_nonneg (intervalLpDyadicRadius_pos n).le (norm_nonneg _))

theorem lpHaarSignedBlockReader_uniform_small
    (S : ∀ n, Finset (Fin (2 ^ n))) {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hS : ∀ᶠ n in atTop, m ≤ (S n).card * intervalLpDyadicRadius n)
    (f : IntervalLp 𝕜 p) :
    ∀ᶠ n in atTop, ∀ θ : Fin (2 ^ n) → Bool,
      ‖lpHaarSignedBlockReader 𝕜 p n (S n) θ f‖ < ε := by
  have ht := (tendsto_order.mp (lpHaar_backward_mass_tendsto_zero 𝕜 p f)).2
    (m * ε) (mul_pos hm hε)
  filter_upwards [hS, ht] with n hn hmass θ
  have hne : (S n).Nonempty := by
    by_contra h
    have hz : (S n).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    simp only [hz, Nat.cast_zero, zero_mul] at hn
    linarith
  have hb := lpHaarSignedBlockReader_mass_bound 𝕜 p n (S n) hne θ f
  have hle : m * ‖lpHaarSignedBlockReader 𝕜 p n (S n) θ f‖ ≤
      ((S n).card * intervalLpDyadicRadius n) *
        ‖lpHaarSignedBlockReader 𝕜 p n (S n) θ f‖ :=
    mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  nlinarith

/-- One genuine block simultaneously makes finitely many forward and
backward interactions small, at an arbitrarily late level. -/
theorem lpHaarSignedBlock_two_sided_small (hp : p.val ≠ ∞) {a b : ℕ}
    (φ : Fin a → IntervalLp 𝕜 p →L[𝕜] 𝕜) (f : Fin b → IntervalLp 𝕜 p)
    (S : ∀ n, Finset (Fin (2 ^ n))) {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hS : ∀ᶠ n in atTop, m ≤ (S n).card * intervalLpDyadicRadius n) (N : ℕ) :
    ∃ n ≥ N, ∃ θ : Fin (2 ^ n) → Bool,
      (∀ r, ‖φ r (lpHaarSignedBlock 𝕜 p n (S n) θ)‖ < ε) ∧
      ∀ r, ‖lpHaarSignedBlockReader 𝕜 p n (S n) θ (f r)‖ < ε := by
  have hb : ∀ᶠ n in atTop, ∀ r : Fin b, ∀ θ : Fin (2 ^ n) → Bool,
      ‖lpHaarSignedBlockReader 𝕜 p n (S n) θ (f r)‖ < ε := by
    exact eventually_all.mpr (fun r => lpHaarSignedBlockReader_uniform_small 𝕜 p S hm hε hS (f r))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hb
  obtain ⟨n, hn, θ, hθ⟩ := lpHaarSignedBlock_subset_small 𝕜 p hp φ S (max N M) hε
  exact ⟨n, (le_max_left N M).trans hn, θ, hθ,
    fun r => hM n ((le_max_right N M).trans hn) r θ⟩

end ThesisCommon
