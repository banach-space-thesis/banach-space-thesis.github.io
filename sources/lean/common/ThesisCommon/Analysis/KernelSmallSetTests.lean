import ThesisCommon.Analysis.IntegralAlgebraPositivity
import Mathlib.Probability.Kernel.Basic

/-! Small-set bounds can be tested on a generating algebra. Approximation
under the sum of the reference and tested measures preserves both the size
constraint and the tested mass. Countability makes all fibre tests hold
outside one null set, even when the tested set subsequently depends on x. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal symmDiff
namespace ThesisCommon
variable {Y : Type*} [mY : MeasurableSpace Y]
variable {ν σ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure σ]

theorem exists_small_algebra_measure_approximation {𝒜 : Set (Set Y)}
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : mY = MeasurableSpace.generateFrom 𝒜)
    {A : Set Y} (hA : MeasurableSet A) {δ ε : ℝ}
    (hδ : ν.real A < δ) (hε : 0 < ε) :
    ∃ B ∈ 𝒜, ν.real B < δ ∧ σ.real A ≤ σ.real B + ε := by
  let η := min ε ((δ - ν.real A) / 2)
  have hη : 0 < η := lt_min hε (by linarith)
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (ν + σ) h𝒜 hgen
  obtain ⟨B, hB, hdiff⟩ := hd.approx A hA (measure_ne_top _ _) η hη
  have hdiff' : (ν + σ).real (A ∆ B) < η := by
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hdiff
      |>.trans_le (by rw [ENNReal.toReal_ofReal hη.le])
  rw [measureReal_add_apply] at hdiff'
  have hν := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
    hA.nullMeasurableSet (hd.measurable B hB).nullMeasurableSet
  have hσ := abs_measureReal_sub_le_measureReal_symmDiff (μ := σ)
    hA.nullMeasurableSet (hd.measurable B hB).nullMeasurableSet
  have hν0 := measureReal_nonneg (μ := ν) (s := A ∆ B)
  have hσ0 := measureReal_nonneg (μ := σ) (s := A ∆ B)
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ (δ - ν.real A) / 2 := min_le_right _ _
  refine ⟨B, hB, ?_, ?_⟩
  · have := (abs_le.mp hν).1
    linarith
  · have := (abs_le.mp hσ).2
    linarith

theorem measure_le_of_small_algebra_tests {𝒜 : Set (Set Y)}
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : mY = MeasurableSpace.generateFrom 𝒜)
    {δ C : ℝ} (htest : ∀ B ∈ 𝒜, ν.real B < δ → σ.real B ≤ C)
    {A : Set Y} (hA : MeasurableSet A) (hδ : ν.real A < δ) : σ.real A ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨B, hB, hBδ, happrox⟩ :=
    exists_small_algebra_measure_approximation h𝒜 hgen hA hδ hε (σ := σ)
  exact happrox.trans (add_le_add_right (htest B hB hBδ) ε)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ae_kernel_smallSet_bound_of_algebra_tests
    (κ : Kernel X Y) [IsFiniteKernel κ] {𝒜 : Set (Set Y)}
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : mY = MeasurableSpace.generateFrom 𝒜)
    (hcount : 𝒜.Countable) {δ C : ℝ}
    (htest : ∀ B ∈ 𝒜, ν.real B < δ → ∀ᵐ x ∂μ, (κ x).real B ≤ C) :
    ∀ᵐ x ∂μ, ∀ A : Set Y, MeasurableSet A → ν.real A < δ → (κ x).real A ≤ C := by
  letI : Countable 𝒜 := hcount.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ B : 𝒜, ν.real B < δ → (κ x).real B ≤ C := by
    apply ae_all_iff.mpr
    intro B
    by_cases hB : ν.real B < δ
    · exact (htest B B.2 hB).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hB h).elim
  filter_upwards [hall] with x hx
  intro A hA hδ
  exact measure_le_of_small_algebra_tests h𝒜 hgen
    (fun B hB => hx ⟨B, hB⟩) hA hδ

/-- The exceptional null set can be chosen before choosing the output set.
Only countable generation of the output sigma algebra is needed. -/
theorem ae_kernel_smallSet_bound [MeasurableSpace.CountablyGenerated Y]
    (κ : Kernel X Y) [IsFiniteKernel κ] {δ C : ℝ}
    (htest : ∀ B : Set Y, MeasurableSet B → ν.real B < δ →
      ∀ᵐ x ∂μ, (κ x).real B ≤ C) :
    ∀ᵐ x ∂μ, ∀ A : Set Y, MeasurableSet A → ν.real A < δ → (κ x).real A ≤ C := by
  let 𝒜 := generateSetAlgebra (MeasurableSpace.countableGeneratingSet Y)
  have hgen : mY = MeasurableSpace.generateFrom 𝒜 := by
    rw [generateFrom_generateSetAlgebra_eq, MeasurableSpace.generateFrom_countableGeneratingSet]
  apply ae_kernel_smallSet_bound_of_algebra_tests κ isSetAlgebra_generateSetAlgebra hgen
    (countable_generateSetAlgebra MeasurableSpace.countable_countableGeneratingSet)
  intro B hB
  exact htest B (hgen ▸ MeasurableSpace.measurableSet_generateFrom hB)

end ThesisCommon
