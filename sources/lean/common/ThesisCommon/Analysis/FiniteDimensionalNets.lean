import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Order.SuccPred.Archimedean

/-! Uniform finite nets in finite-dimensional normed spaces. A Haar-volume
packing bound is independent of the particular norm. The realification of
an RCLike space has real dimension at most twice its scalar dimension. -/
noncomputable section
open Metric Set Module MeasureTheory
open scoped ENNReal
namespace ThesisCommon

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The usual volume packing estimate. This generalises the radius choices
in mathlib's `Besicovitch.card_le_of_separated` to arbitrary positive δ. -/
theorem unitBall_separated_card_le (s : Finset E) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (1 + 2 / δ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let η : ℝ := δ / 2
  let ρ : ℝ := 1 + δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball (c : E) η
  have hdisj : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c η) (ball d η)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := hsep c hc d hd hcd
    dsimp [η]
    linarith
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [η, ρ]
    linarith [hs c hc]
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (η ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        dsimp [A]
        rw [measure_biUnion_finset hdisj (fun c _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hη, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hvol' : (s.card : ℝ≥0∞) * ENNReal.ofReal (η ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_right (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne).mp hvol
  have hreal : (s.card : ℝ) * η ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hvol'
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hη.le _)] using h
  calc
    (s.card : ℝ) ≤ ρ ^ finrank ℝ E / η ^ finrank ℝ E :=
      (le_div_iff₀ (pow_pos hη _)).mpr hreal
    _ = (ρ / η) ^ finrank ℝ E := (div_pow _ _ _).symm
    _ = (1 + 2 / δ) ^ finrank ℝ E := by
      congr 1
      dsimp [ρ, η]
      field_simp
      ring

end Real
end ThesisCommon
