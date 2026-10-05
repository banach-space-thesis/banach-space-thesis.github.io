import Posets.WolfePreservationBlockJointPhaseLower

/-! Uniform analytic parameters are chosen before the quantile grid and
before the ordinal core. Only the final phase error depends on grid size. -/

noncomputable section
namespace Posets

structure WolfePhaseParameters (c B Q : ℝ) where
  atom : ℝ
  relative : ℝ
  floor : ℝ
  gap : ℝ
  atom_pos : 0 < atom
  relative_pos : 0 < relative
  relative_le_one : relative ≤ 1
  floor_pos : 0 < floor
  gap_pos : 0 < gap
  quantile_gap : 3 * relative + 2 * gap < atom
  floor_budget : (1 + relative) * floor * B ≤ c / 8
  atom_budget : atom * Q ≤ c / 8

theorem wolfePhaseParameters_exists {c B Q : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hQ : 0 ≤ Q) :
    Nonempty (WolfePhaseParameters c B Q) := by
  let δ := c / (8 * (Q + c + 1))
  have hden : 0 < 8 * (Q + c + 1) := by positivity
  have hδ : 0 < δ := div_pos hc hden
  have hδsmall : δ < 1 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hδbudget : δ * Q ≤ c / 8 := by
    have he : δ * (8 * (Q + c + 1)) = c := div_mul_cancel₀ c (ne_of_gt hden)
    have hle : δ * (8 * Q) ≤ δ * (8 * (Q + c + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    nlinarith
  let τ := δ / 16
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτone : τ ≤ 1 := by dsimp [τ]; linarith
  let κ := c / (8 * ((1 + τ) * (B + 1)))
  have hκden : 0 < 8 * ((1 + τ) * (B + 1)) := by positivity
  have hκ : 0 < κ := div_pos hc hκden
  have hκbudget : (1 + τ) * κ * B ≤ c / 8 := by
    have he : κ * (8 * ((1 + τ) * (B + 1))) = c :=
      div_mul_cancel₀ c (ne_of_gt hκden)
    have hle : (1 + τ) * κ * B ≤ (1 + τ) * κ * (B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hκ.le)
    nlinarith
  refine ⟨⟨δ, τ, κ, δ / 8, hδ, hτ, hτone, hκ, by positivity, ?_, hκbudget, hδbudget⟩⟩
  dsimp [τ]
  linarith

theorem WolfePhaseParameters.exists_error {c B Q : ℝ}
    (p : WolfePhaseParameters c B Q) (hc : 0 < c) (n : ℕ) :
    ∃ η : ℝ, 0 < η ∧ (1 + (1 + p.relative) / p.relative) * η ≤ c / 8 ∧
      ((n : ℝ) + 1) * η ≤ c / 64 := by
  let A := 1 + (1 + p.relative) / p.relative
  have hτ := p.relative_pos
  have hA : 0 < A := by dsimp [A]; positivity
  let η := min (c / (8 * A)) (c / (64 * ((n : ℝ) + 1)))
  have hη : 0 < η := lt_min (div_pos hc (by positivity)) (div_pos hc (by positivity))
  refine ⟨η, hη, ?_, ?_⟩
  · have he := mul_le_mul_of_nonneg_left (min_le_left
      (c / (8 * A)) (c / (64 * ((n : ℝ) + 1)))) hA.le
    have hcancel : A * (c / (8 * A)) = c / 8 := by field_simp [ne_of_gt hA]
    exact he.trans_eq hcancel
  · have he := mul_le_mul_of_nonneg_left (min_le_right
      (c / (8 * A)) (c / (64 * ((n : ℝ) + 1)))) (by positivity : 0 ≤ (n : ℝ) + 1)
    have hcancel : ((n : ℝ) + 1) * (c / (64 * ((n : ℝ) + 1))) = c / 64 := by
      have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity : 0 < (n : ℝ) + 1)
      field_simp [hn]
    exact he.trans_eq hcancel

end Posets
