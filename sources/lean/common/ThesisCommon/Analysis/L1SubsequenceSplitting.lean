import ThesisCommon.Analysis.L1DisjointBiting
import ThesisCommon.Analysis.L1UniformIntegrableSubsequence

/-! Kadec–Pełczyński subsequence splitting in genuine finite-measure L1,
for real and complex scalars. Biting selection constructs the disjoint
part, and Dunford–Pettis compactness supplies the weakly convergent part. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem exists_real_lOne_subsequence_splitting
    (f : ℕ → Lp ℝ 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ r : ℕ → ℕ, ∃ g h : ℕ → Lp ℝ 1 μ, ∃ x : Lp ℝ 1 μ,
      StrictMono r ∧ (∀ n, f (r n) = g n + h n) ∧
      (∀ n, ∀ᵐ y ∂μ, g n y = 0 ∨ h n y = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂μ, h i y = 0 ∨ h j y = 0) ∧
      Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 1 μ) (g n)) atTop
        (𝓝 (toWeakSpace ℝ (Lp ℝ 1 μ) x)) ∧
      (∀ n, ‖g n‖ ≤ ‖f (r n)‖) ∧ (∀ n, ‖h n‖ ≤ ‖f (r n)‖) := by
  obtain ⟨r, g, h, hr, hfg, hgh, hhh, hUI, hg, hh⟩ :=
    exists_lOne_uniformIntegrable_disjoint_splitting f hf
  obtain ⟨x, s, hs, ht⟩ := exists_real_lOne_weak_subsequence_of_uniformIntegrable g hUI
  refine ⟨r ∘ s, g ∘ s, h ∘ s, x, hr.comp hs, fun n => hfg _, fun n => hgh _,
    ?_, ht, fun n => hg _, fun n => hh _⟩
  intro i j hij
  exact hhh (fun heq => hij (hs.injective heq))

theorem exists_complex_lOne_subsequence_splitting
    (f : ℕ → Lp ℂ 1 μ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ r : ℕ → ℕ, ∃ g h : ℕ → Lp ℂ 1 μ, ∃ x : Lp ℂ 1 μ,
      StrictMono r ∧ (∀ n, f (r n) = g n + h n) ∧
      (∀ n, ∀ᵐ y ∂μ, g n y = 0 ∨ h n y = 0) ∧
      (Pairwise fun i j => ∀ᵐ y ∂μ, h i y = 0 ∨ h j y = 0) ∧
      Tendsto (fun n => toWeakSpace ℂ (Lp ℂ 1 μ) (g n)) atTop
        (𝓝 (toWeakSpace ℂ (Lp ℂ 1 μ) x)) ∧
      (∀ n, ‖g n‖ ≤ ‖f (r n)‖) ∧ (∀ n, ‖h n‖ ≤ ‖f (r n)‖) := by
  obtain ⟨r, g, h, hr, hfg, hgh, hhh, hUI, hg, hh⟩ :=
    exists_lOne_uniformIntegrable_disjoint_splitting f hf
  obtain ⟨x, s, hs, ht⟩ := exists_complex_lOne_weak_subsequence_of_uniformIntegrable g hUI
  refine ⟨r ∘ s, g ∘ s, h ∘ s, x, hr.comp hs, fun n => hfg _, fun n => hgh _,
    ?_, ht, fun n => hg _, fun n => hh _⟩
  intro i j hij
  exact hhh (fun heq => hij (hs.injective heq))

end ThesisCommon
