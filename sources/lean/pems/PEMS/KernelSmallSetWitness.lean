import ThesisCommon.Analysis.IntegralKernelGeneralSmallSet

/-! Lemma 4.11 with its necessary witness conventions made explicit:
the input measure is nonzero and the natural threshold is positive.
The main theorem includes the zero-input case separately. See source note D09. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def Lemma_4_11_nonzero (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) : Prop :=
  IsIntegralKernel k K → μ ≠ 0 → ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 0 < n →
    ∃ (G : Set Y) (M : Set X), MeasurableSet G ∧ ν.real G ≤ 2 * ‖K‖ / n ∧
      MeasurableSet M ∧ 0 < μ M ∧ ∀ x ∈ M,
        (∫ y, |truncatedKernel n k (x, y)| ∂ν) - ε ≤ ∫ y in G, |k (x, y)| ∂ν

theorem lemma_4_11_nonzero_proof (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) :
    Lemma_4_11_nonzero K k := by
  intro hk hμ ε hε n hn
  simpa only [Real.norm_eq_abs] using
    hk.exists_smallSet_tail_witness hμ (Nat.cast_pos.mpr hn) hε

end PEMS
