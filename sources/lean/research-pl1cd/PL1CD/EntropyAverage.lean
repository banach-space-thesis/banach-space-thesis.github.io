import PL1CD.BoundedEntropy

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PL1CD.Entropy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

def functionAverage (f : ι → Ω → ℝ) (x : Ω) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i x

omit [MeasurableSpace Ω] in
theorem functionAverage_sum (f : ι → Ω → ℝ) (x : Ω) :
    ∑ i, f i x = (Fintype.card ι : ℝ) * functionAverage f x := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [functionAverage, hc]

omit [Nonempty ι] in
theorem measurable_functionAverage (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (functionAverage f) := by
  classical
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hf i))

omit [MeasurableSpace Ω] in
theorem functionAverage_mem_Icc (f : ι → Ω → ℝ) (C : ℝ)
    (hbound : ∀ i x, f i x ∈ Set.Icc 0 C) (x : Ω) :
    functionAverage f x ∈ Set.Icc 0 C := by
  classical
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinv : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  constructor
  · exact mul_nonneg hinv (Finset.sum_nonneg (fun i _ => (hbound i x).1))
  · calc
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hbound i x).2)) hinv
      _ = C := by simp [hc]

theorem functionAverage_mass_le_one (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (C : ℝ)
    (hbound : ∀ i x, f i x ∈ Set.Icc 0 C)
    (hmass : ∀ i, ∫ x, f i x ∂μ ≤ 1) :
    ∫ x, functionAverage f x ∂μ ≤ 1 := by
  classical
  have hi (i : ι) : Integrable (f i) μ :=
    integrable_continuous_comp_bounded μ (f i) (hf i) C (hbound i) id continuous_id
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold functionAverage
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hmass i)) (by positivity)
    _ = 1 := by simp [hc]

theorem bounded_average_entropy_gap (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (C : ℝ)
    (hbound : ∀ i x, f i x ∈ Set.Icc 0 C)
    (hmass : ∀ i, ∫ x, f i x ∂μ ≤ 1) :
    (Fintype.card ι : ℝ)⁻¹ * (∑ i, Phi μ (f i)) - Phi μ (functionAverage f) ≥
      (4 * (Fintype.card ι : ℝ))⁻¹ *
        ∑ i, (∫ x, |f i x - functionAverage f x| ∂μ) ^ 2 :=
  averaged_Phi_gap μ f (functionAverage f) hf (measurable_functionAverage f hf) C hbound
    (functionAverage_mem_Icc f C hbound) (functionAverage_sum f) hmass
    (functionAverage_mass_le_one μ f hf C hbound hmass)

end PL1CD.Entropy
