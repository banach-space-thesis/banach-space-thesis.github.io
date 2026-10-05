import ThesisCommon.Analysis.IntegralKernelGeneralSmallSet

/-! The kernel small-set witness can be obtained inside any measurable
positive input set, with the same column bound and threshold. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
variable {k : X × Y → 𝕜} {C : ℝ}

theorem HasKernelBound.exists_smallSet_tail_witness_subset
    (hk : Measurable k) (hb : HasKernelBound μ ν k C) (hC : 0 ≤ C)
    (M : Set X) (hM : MeasurableSet M) (hμM : 0 < μ M)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ (B : Set Y) (N : Set X), MeasurableSet B ∧ ν.real B ≤ 2 * C / r ∧
      MeasurableSet N ∧ N ⊆ M ∧ 0 < μ N ∧
      ∀ x ∈ N, (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) - ε ≤
        ∫ y in B, ‖k (x, y)‖ ∂ν := by
  have hb' : HasKernelBound (μ.restrict M) ν k C := ae_restrict_of_ae hb
  obtain ⟨B, N, hB, hsize, hN, hpos, hmass⟩ :=
    hb'.exists_smallSet_tail_witness_general (Measure.restrict_eq_zero.not.mpr hμM.ne') hk hC hr hε
  refine ⟨B, N ∩ M, hB, hsize, hN.inter hM, inter_subset_right, ?_, fun x hx => hmass x hx.1⟩
  simpa only [Measure.restrict_apply hN] using hpos

end ThesisCommon
