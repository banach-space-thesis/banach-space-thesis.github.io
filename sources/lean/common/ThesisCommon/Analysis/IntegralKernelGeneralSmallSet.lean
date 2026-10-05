import ThesisCommon.Analysis.IntegralKernelSmallSetWitness
import ThesisCommon.Analysis.ProductMeasurableCountableRight

/-! The small-set witness theorem without a countability assumption on either
measure space. A fixed kernel is measurable for a countably generated output
sub-sigma-algebra; trimming the output measure preserves its column integrals. -/
noncomputable section
open MeasureTheory Set Filter MeasurableSpace
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
variable {k : X × Y → 𝕜} {C : ℝ}

theorem HasKernelBound.exists_smallSet_tail_witness_general
    (hμ : μ ≠ 0) (hk : Measurable k) (hb : HasKernelBound μ ν k C)
    (hC : 0 ≤ C) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ (B : Set Y) (M : Set X), MeasurableSet B ∧ ν.real B ≤ 2 * C / r ∧
      MeasurableSet M ∧ 0 < μ M ∧
      ∀ x ∈ M, (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) - ε ≤
        ∫ y in B, ‖k (x, y)‖ ∂ν := by
  obtain ⟨A, hA, hAm, hkA⟩ := exists_countable_right_generators_of_measurable hk
  let m : MeasurableSpace Y := generateFrom A
  have hm : m ≤ mY := generateFrom_le hAm
  let ν' : @Measure Y m := ν.trim hm
  letI hcount : @CountablyGenerated Y m := ⟨⟨A, hA, rfl⟩⟩
  have hkx (x : X) : @Measurable Y 𝕜 m _ (fun y => k (x, y)) :=
    hkA.comp (@measurable_prodMk_left X Y mX m x)
  have hb' : @HasKernelBound 𝕜 _ X Y mX m μ ν' k C := by
    filter_upwards [hb] with x hx
    refine ⟨hx.1.trim hm (hkx x).stronglyMeasurable, ?_⟩
    rw [← integral_trim hm (hkx x).norm.stronglyMeasurable]
    exact hx.2
  obtain ⟨B, M, hB, hsize, hM, hpos, hmass⟩ :=
    @HasKernelBound.exists_smallSet_tail_witness 𝕜 _ X Y mX m hcount μ ν' _ k C
      hμ hkA hb' hC r ε hr hε
  refine ⟨B, M, hm _ hB, ?_, hM, hpos, ?_⟩
  · simpa only [measureReal_def, ν', trim_measurableSet_eq hm hB] using hsize
  · intro x hx
    have htail : StronglyMeasurable[m]
        (fun y => ‖ThesisCommon.truncatedKernel r k (x, y)‖) :=
      ((@measurable_truncatedKernel 𝕜 _ X Y mX m k hkA r).comp
        (@measurable_prodMk_left X Y mX m x)).norm.stronglyMeasurable
    rw [integral_trim hm htail, setIntegral_trim hm (hkx x).norm.stronglyMeasurable hB]
    exact hmass x hx

/-- Lemma 4.11's witness, with the necessary nonzero input and positive
threshold hypotheses, for the paper's real integral kernels. -/
theorem IsIntegralKernel.exists_smallSet_tail_witness [SigmaFinite μ]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (hμ : μ ≠ 0)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ (B : Set Y) (M : Set X), MeasurableSet B ∧ ν.real B ≤ 2 * ‖K‖ / r ∧
      MeasurableSet M ∧ 0 < μ M ∧
      ∀ x ∈ M, (∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν) - ε ≤
        ∫ y in B, ‖k (x, y)‖ ∂ν :=
  hk.hasKernelBound_sigmaFinite.exists_smallSet_tail_witness_general
    hμ hk.measurable (norm_nonneg K) hr hε

end ThesisCommon
