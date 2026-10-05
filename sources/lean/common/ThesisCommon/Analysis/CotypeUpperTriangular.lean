import ThesisCommon.Analysis.CotypeUpperSelection

/-! UPFP Proposition 3.5: the sum of the earlier-column norms is small
in every selected row. The geometric budget follows the paper's construction.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem sum_lt_of_geometric_entries {ε : ℝ} (hε : 0 < ε)
    (a : ℕ → ℕ → ℝ)
    (ha : ∀ i j, i < j → a i j < (ε / 4) * (1 / 2 : ℝ) ^ i) (j : ℕ) :
    ∑ i ∈ Finset.range j, a i j < ε := by
  calc
    _ ≤ ∑ i ∈ Finset.range j, (ε / 4) * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum fun i hi => (ha i j (Finset.mem_range.mp hi)).le
    _ = (ε / 4) * ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := (Finset.mul_sum ..).symm
    _ ≤ (ε / 4) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le j) (by positivity)
    _ < ε := by linarith

/-- Finite cotype yields the upper-triangular entry estimate on ℓ∞. -/
theorem HasFiniteCotype.infinity_upper_triangular (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpCoordinate ∞ (e j)).comp T).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i))‖) < ε := by
  obtain ⟨e, hmono, he⟩ := h.infinity_upper_selection T
    (fun k => (ε / 4) * (1 / 2 : ℝ) ^ k) (fun k => by positivity)
  exact ⟨e, hmono, sum_lt_of_geometric_entries hε _ he⟩

/-- The identical upper-triangular entry estimate on c₀. -/
theorem HasFiniteCotype.cZero_upper_triangular (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((cZeroCoordinate (e j)).comp T).comp
        (cZeroSingleCLM (e i))‖) < ε := by
  obtain ⟨e, hmono, he⟩ := h.cZero_upper_selection T
    (fun k => (ε / 4) * (1 / 2 : ℝ) ^ k) (fun k => by positivity)
  exact ⟨e, hmono, sum_lt_of_geometric_entries hε _ he⟩

end ThesisCommon
