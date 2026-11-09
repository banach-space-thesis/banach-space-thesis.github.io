import PL1.NoiseGenerator
import PL1.WalshExpectations

/-! # Finite Walsh polynomials form a core for the actual noise generator

The conditional expectations preserve the genuine generator graph and
converge in both coordinates. Convergence is stated explicitly in the graph
sum norm `‖f‖₁ + ‖g‖₁`, with no substitution of the product maximum norm.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace PL1.Noise
open Walsh WalshExpectations

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- Every finite-coordinate expectation preserves the actual infinitesimal generator graph. -/
theorem IsGeneratorPair.expectation {f g : Lp K 1 haar}
    (hfg : IsGeneratorPair K rates f g) (m : ℕ) :
    IsGeneratorPair K rates (expectationL1 K m f) (expectationL1 K m g) := by
  apply (isGeneratorPair_iff_resolvent K rates _ _).mpr
  have he := (isGeneratorPair_iff_resolvent K rates f g).mp hfg
  calc
    _ = resolventL1 K rates (dyadicTime 0) (expectationL1 K m (f + g)) := by simp only [map_add]
    _ = expectationL1 K m (resolventL1 K rates (dyadicTime 0) (f + g)) :=
      (DFunLike.congr_fun (expectationL1_resolvent_commute K m rates (dyadicTime 0)) (f + g)).symm
    _ = _ := by rw [he]

/-- The expectation approximants converge in the exact graph sum norm. -/
theorem tendsto_expectation_graphNorm (f g : Lp K 1 haar) :
    Tendsto (fun m => ResolventGeneratorGraph.graphNorm K
      (expectationL1 K m f - f, expectationL1 K m g - g)) atTop (𝓝 0) := by
  have hf := ((tendsto_expectationL1 K f).sub_const f).norm
  have hg := ((tendsto_expectationL1 K g).sub_const g).norm
  simpa only [ResolventGeneratorGraph.graphNorm, sub_self, norm_zero, zero_add] using hf.add hg

/-- Every actual generator pair is approximated by finite Walsh polynomial generator pairs. -/
theorem IsGeneratorPair.polynomial_core {f g : Lp K 1 haar}
    (hfg : IsGeneratorPair K rates f g) :
    (∀ m, expectationL1 K m f ∈ finiteSpan K m ∧ expectationL1 K m g ∈ finiteSpan K m ∧
      IsGeneratorPair K rates (expectationL1 K m f) (expectationL1 K m g)) ∧
    Tendsto (fun m => ‖expectationL1 K m f - f‖ + ‖expectationL1 K m g - g‖) atTop (𝓝 0) :=
  ⟨fun m => ⟨expectationL1_mem_finiteSpan K m f, expectationL1_mem_finiteSpan K m g,
      hfg.expectation K rates m⟩, tendsto_expectation_graphNorm K f g⟩

/-- A quantitative form of graph-norm density by finite Walsh polynomials. -/
theorem IsGeneratorPair.exists_polynomial_graphNorm_lt {f g : Lp K 1 haar}
    (hfg : IsGeneratorPair K rates f g) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (p q : Lp K 1 haar), p ∈ finiteSpan K m ∧ q ∈ finiteSpan K m ∧
      IsGeneratorPair K rates p q ∧ ‖p - f‖ + ‖q - g‖ < ε := by
  obtain ⟨m, hm⟩ := ((tendsto_expectation_graphNorm K f g).eventually_lt_const hε).exists
  exact ⟨m, expectationL1 K m f, expectationL1 K m g,
    expectationL1_mem_finiteSpan K m f, expectationL1_mem_finiteSpan K m g,
    hfg.expectation K rates m, hm⟩

/-- Every finite Walsh polynomial itself belongs to the actual generator domain. -/
theorem finiteSpan_subset_generator_domain (m : ℕ) {f : Lp K 1 haar}
    (hf : f ∈ finiteSpan K m) : ∃ g, IsGeneratorPair K rates f g := by
  apply (exists_generatorPair_iff_range K rates f).mpr
  have hsub : finiteSpan K m ≤ (resolventL1 K rates (dyadicTime 0)).range := by
    apply Submodule.span_le.mpr
    rintro x ⟨F, _, rfl⟩
    exact (exists_generatorPair_iff_range K rates (scalarCharacterLp K 1 F)).mp
      ⟨_, isGeneratorPair_character K rates F⟩
  exact hsub hf

#print axioms IsGeneratorPair.polynomial_core
#print axioms IsGeneratorPair.exists_polynomial_graphNorm_lt
#print axioms finiteSpan_subset_generator_domain
end PL1.Noise
