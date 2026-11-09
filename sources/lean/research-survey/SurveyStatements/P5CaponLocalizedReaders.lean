import SurveyStatements.P5CaponLocalizedInput

/-! Contractive mixed-space readers detect the localized finite Capon images. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def caponLocalizedReader (m : ℕ) (j₀ : Fin (2 ^ m))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : MixedNorm ℝ p →L[ℝ] ℝ :=
  mixedSetReader (Finset.range N) (fun i => (caponLocalBranch m j₀).annulus (i + 1))
    (fun i => dyadicRademacherFunction ℝ (m + i))
    (fun i => dyadicRademacherFunction_stronglyMeasurable (m + i))
    (fun i => norm_dyadicRademacherFunction_le (m + i))

theorem norm_caponLocalizedReader_le (m : ℕ) (j₀ : Fin (2 ^ m)) (N : ℕ) :
    ‖caponLocalizedReader m j₀ p N‖ ≤ 1 := by
  unfold caponLocalizedReader
  apply norm_mixedSetReader_le (p := p)
  · intro i _
    exact (caponLocalBranch m j₀).annulus_measurable _
  · intro i _ j _ hij
    exact (caponLocalBranch m j₀).annulus_disjoint (by omega : i + 1 ≠ j + 1)

theorem caponLocalizedReader_tensor_level (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ)
    (g : Lp ℝ 1 unitIntervalMeasure) (n : ℕ) :
    caponLocalizedReader m j₀ p N (tensorWith g (caponLocalRademacher m i₀ p n)) =
      if n < N then intervalLpDyadicRadius m *
        l1SetReader ((caponLocalBranch m j₀).annulus (n + 1)) g else 0 := by
  rw [caponLocalizedReader, mixedSetReader_tensor]
  change (∑ i ∈ Finset.range N,
    l1SetReader ((caponLocalBranch m j₀).annulus (i + 1)) g *
      rademacherReader p (m + i) (caponLocalRademacher m i₀ p n)) = _
  simp_rw [rademacherReader_caponLocalRademacher]
  by_cases hn : n < N
  · simp [hn, Finset.mem_range, mul_comm]
  · simp [hn, Finset.mem_range]

theorem caponLocalizedReader_haar_level (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N k n : ℕ) :
    caponLocalizedReader m j₀ p N
      (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
        (caponLocalRademacher m i₀ p n)) =
      if n < N then intervalLpDyadicRadius m *
        (unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1)) *
          (if k < n + 1 then 1 else if k = n + 1 then -1 else 0)) else 0 := by
  rw [caponLocalizedReader_tensor_level]
  split
  · rw [l1SetReader_caponLocalInnerHaar]
  · rfl

end SurveyStatements.P5
