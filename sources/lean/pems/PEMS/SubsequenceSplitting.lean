import PEMS.Definitions
import ThesisCommon.Analysis.L1SubsequenceSplitting
import ThesisCommon.Analysis.L1AEDisjointness

/-! Source Lemma 5.3: Kadec–Pełczyński subsequence splitting. The hypotheses
are precisely a finite measure and a bounded sequence. The lattice moduli
and the weak convergence below are the actual L1 constructions. -/
noncomputable section
open MeasureTheory Set Filter Topology ThesisCommon
namespace PEMS
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem lemma_5_3_real_subsequence_splitting
    (f : ℕ → LOne ℝ μ) (hf : Bornology.IsBounded (Set.range f)) :
    ∃ r : ℕ → ℕ, ∃ g h : ℕ → LOne ℝ μ, ∃ x : LOne ℝ μ,
      StrictMono r ∧ (∀ n, f (r n) = g n + h n) ∧
      (∀ n, |g n| ⊓ |h n| = 0) ∧
      (Pairwise fun i j => |h i| ⊓ |h j| = 0) ∧
      Tendsto (fun n => toWeakSpace ℝ (LOne ℝ μ) (g n)) atTop
        (𝓝 (toWeakSpace ℝ (LOne ℝ μ) x)) := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  obtain ⟨r, g, h, x, hr, hfg, hgh, hhh, ht, _, _⟩ :=
    exists_real_lOne_subsequence_splitting f (fun n => hC _ (mem_range_self n))
  exact ⟨r, g, h, x, hr, hfg,
    fun n => lOne_abs_inf_eq_zero_of_ae_disjoint _ _ (hgh n),
    fun i j hij => lOne_abs_inf_eq_zero_of_ae_disjoint _ _ (hhh hij), ht⟩

theorem lemma_5_3_complex_subsequence_splitting
    (f : ℕ → LOne ℂ μ) (hf : Bornology.IsBounded (Set.range f)) :
    ∃ r : ℕ → ℕ, ∃ g h : ℕ → LOne ℂ μ, ∃ x : LOne ℂ μ,
      StrictMono r ∧ (∀ n, f (r n) = g n + h n) ∧
      (∀ n, complexL1Modulus (g n) ⊓ complexL1Modulus (h n) = 0) ∧
      (Pairwise fun i j => complexL1Modulus (h i) ⊓ complexL1Modulus (h j) = 0) ∧
      Tendsto (fun n => toWeakSpace ℂ (LOne ℂ μ) (g n)) atTop
        (𝓝 (toWeakSpace ℂ (LOne ℂ μ) x)) := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  obtain ⟨r, g, h, x, hr, hfg, hgh, hhh, ht, _, _⟩ :=
    exists_complex_lOne_subsequence_splitting f (fun n => hC _ (mem_range_self n))
  exact ⟨r, g, h, x, hr, hfg,
    fun n => complexL1Modulus_inf_eq_zero_of_ae_disjoint _ _ (hgh n),
    fun i j hij => complexL1Modulus_inf_eq_zero_of_ae_disjoint _ _ (hhh hij), ht⟩

end PEMS
