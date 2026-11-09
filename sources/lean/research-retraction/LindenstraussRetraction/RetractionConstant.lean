import LindenstraussRetraction.Definitions

/-! # Meaning of the bidual Lipschitz retraction constant

The infimum is finite exactly when a Lipschitz retraction exists. Upper bounds
come from actual retractions; lower bounds must hold for every admissible bound.
-/

noncomputable section

open scoped NNReal ENNReal

namespace LindenstraussRetraction

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- An actual retraction with bound `K` provides an upper bound on `Λ(X)`. -/
theorem bidualLipschitzRetractionConstant_le_of_retraction
    {K : ℝ≥0} {r : Bidual 𝕜 X → X}
    (hLip : LipschitzWith K r) (hret : IsRetraction (bidualEmbedding 𝕜 X) r) :
    bidualLipschitzRetractionConstant 𝕜 X ≤ (K : ℝ≥0∞) := by
  exact sInf_le ⟨K, r, rfl, hLip, hret⟩

/-- A lower bound holds precisely when it holds for every retraction bound.
This does not assume that the infimum is attained. -/
theorem le_bidualLipschitzRetractionConstant_iff (L : ℝ≥0∞) :
    L ≤ bidualLipschitzRetractionConstant 𝕜 X ↔
      ∀ (K : ℝ≥0) (r : Bidual 𝕜 X → X), LipschitzWith K r →
        IsRetraction (bidualEmbedding 𝕜 X) r → L ≤ (K : ℝ≥0∞) := by
  constructor
  · intro h K r hLip hret
    exact h.trans (bidualLipschitzRetractionConstant_le_of_retraction hLip hret)
  · intro h
    apply le_sInf
    rintro A ⟨K, r, rfl, hLip, hret⟩
    exact h K r hLip hret

/-- The empty-infimum convention is exactly absence of Lipschitz retractability. -/
theorem bidualLipschitzRetractionConstant_eq_top_iff :
    bidualLipschitzRetractionConstant 𝕜 X = ∞ ↔
      ¬ HasLipschitzBidualRetraction 𝕜 X := by
  constructor
  · intro h hret
    obtain ⟨K, r, hLip, hfix⟩ := hret
    have hK := bidualLipschitzRetractionConstant_le_of_retraction hLip hfix
    rw [h] at hK
    exact ENNReal.not_top_le_coe hK
  · intro h
    apply top_unique
    apply (le_bidualLipschitzRetractionConstant_iff (𝕜 := 𝕜) (X := X) ∞).2
    intro K r hLip hfix
    exact False.elim (h ⟨K, r, hLip, hfix⟩)

/-- A finite retraction constant is equivalent to existence of a retraction. -/
theorem bidualLipschitzRetractionConstant_ne_top_iff :
    bidualLipschitzRetractionConstant 𝕜 X ≠ ∞ ↔
      HasLipschitzBidualRetraction 𝕜 X := by
  exact (not_congr (bidualLipschitzRetractionConstant_eq_top_iff
    (𝕜 := 𝕜) (X := X))).trans not_not

end LindenstraussRetraction
