import SurveyStatements.P5L1VariationTrace
import SurveyStatements.P5L1VariationHilbertCluster
import Mathlib.MeasureTheory.Function.L2Space

/-! Bounded actual dyadic symbol functions as L² vectors, retaining
their exact set-integral and indicator-pairing formulas. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

abbrev IntervalL2 (𝕜 : Type*) [RCLike 𝕜] := IntervalLp 𝕜 ⟨2, by norm_num⟩

theorem stepSymbol_bound (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) (x : ℝ) : ‖stepSymbol 𝕜 d n x‖ ≤ B := by
  by_cases h : ∃ k : Fin (2 ^ n), x ∈ lpHaarCell n k
  · obtain ⟨k, hk⟩ := h
    rw [stepSymbol_on_cell 𝕜 d n k hk]
    exact hd n k
  · have hs : stepSymbol 𝕜 d n x = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Set.indicator_of_notMem (fun hx => h ⟨k, hx⟩) _
    rw [hs, norm_zero]
    exact hB

theorem stepSymbol_memLp_two (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) :
    MemLp (stepSymbol 𝕜 d n) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
  MemLp.of_bound (stepSymbol_stronglyMeasurable 𝕜 d n).aestronglyMeasurable B
    (Eventually.of_forall (stepSymbol_bound 𝕜 d B hB hd n))

def stepSymbolL2 (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) : IntervalL2 𝕜 :=
  (stepSymbol_memLp_two 𝕜 d B hB hd n).toLp (stepSymbol 𝕜 d n)

theorem stepSymbolL2_coe (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) :
    stepSymbolL2 𝕜 d B hB hd n =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] stepSymbol 𝕜 d n :=
  (stepSymbol_memLp_two 𝕜 d B hB hd n).coeFn_toLp

theorem stepSymbolL2_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) : ‖stepSymbolL2 𝕜 d B hB hd n‖ ≤ B := by
  have hc : ‖Lp.const (2 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) (B : 𝕜)‖ = B := by
    rw [Lp.norm_const' _ _ _ (by norm_num) (by norm_num)]
    simp [RCLike.norm_ofReal, abs_of_nonneg hB]
  calc
    ‖stepSymbolL2 𝕜 d B hB hd n‖ ≤
        ‖Lp.const (2 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) (B : 𝕜)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [stepSymbolL2_coe 𝕜 d B hB hd n,
        Lp.coeFn_const (2 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) (B : 𝕜)] with x hs hc'
      rw [hs, hc', Function.const_apply, RCLike.norm_ofReal, abs_of_nonneg hB]
      exact stepSymbol_bound 𝕜 d B hB hd n x
    _ = B := hc

theorem stepSymbolL2_setIntegral (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (n : ℕ) (s : Set ℝ) :
    (∫ x in s, stepSymbolL2 𝕜 d B hB hd n x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      lpHaarLevelTrace d n s := by
  rw [integral_congr_ae (ae_restrict_of_ae (stepSymbolL2_coe 𝕜 d B hB hd n)),
    stepSymbol_setIntegral]

end SurveyStatements.P5L1Variation
