import ThesisCommon.Analysis.L1SeparableEnvelope
import ThesisCommon.Analysis.L1SubsigmaSingular

/-! Constructed finite-L1 separable reductions preserving operator moduli
and singularity. The subspaces are actual trimmed L1 spaces over countably
generated sub-sigma-algebras; the reduced operator is the actual output lift.
These are the cofinality constructions for PEMS Lemmas 4.8 and 4.9. -/
noncomputable section
open MeasureTheory MeasurableSpace Set TopologicalSpace
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ]

theorem exists_countablyGenerated_modulusPreserving_lOneSubsigma
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (m : MeasurableSpace X) (hm : m ≤ m₀) (hmc : @CountablyGenerated X m)
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M) :
    ∃ (m' : MeasurableSpace X) (hm' : m' ≤ m₀), m ≤ m' ∧
      @CountablyGenerated X m' ∧ M ⊆ lOneSubsigma μ m' ∧
      L1SubsigmaPreservesModulus T hm' := by
  obtain ⟨W, hc, hW⟩ := exists_countable_lOne_subsigma_modulus_witnesses T
  obtain ⟨m', hm', hmm', hmc', hinc⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement μ m hm hmc
      (M ∪ W) (hM.union hc.isSeparable)
  exact ⟨m', hm', hmm', hmc', fun _ h => hinc (mem_union_left _ h),
    hW m' hm' (fun _ h => hinc (mem_union_right _ h))⟩

theorem exists_countablyGenerated_simultaneous_modulusPreserving_lOneSubsigma
    (T : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν))
    (m : MeasurableSpace X) (hm : m ≤ m₀) (hmc : @CountablyGenerated X m)
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M) :
    ∃ (m' : MeasurableSpace X) (hm' : m' ≤ m₀), m ≤ m' ∧
      @CountablyGenerated X m' ∧ M ⊆ lOneSubsigma μ m' ∧
      ∀ n, L1SubsigmaPreservesModulus (T n) hm' := by
  choose W hc hW using fun n => exists_countable_lOne_subsigma_modulus_witnesses (T n)
  obtain ⟨m', hm', hmm', hmc', hinc⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement μ m hm hmc
      (M ∪ ⋃ n, W n) (hM.union (countable_iUnion hc).isSeparable)
  exact ⟨m', hm', hmm', hmc', fun _ h => hinc (mem_union_left _ h),
    fun n => hW n m' hm' (fun _ h => hinc (mem_union_right _ (mem_iUnion.mpr ⟨n, h⟩)))⟩

variable [IsFiniteMeasure ν]

/-- Every pair of separable input/output sets admits an actual countably
generated singularity-preserving reduction. Existing countably generated
input and output sigma algebras can both be retained. -/
theorem exists_countablyGenerated_singular_lOneSubsigma_reduction
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S)
    (m : MeasurableSpace X) (hm : m ≤ m₀) (hmc : @CountablyGenerated X m)
    (n : MeasurableSpace Y) (hn : n ≤ n₀) (hnc : @CountablyGenerated Y n)
    (M : Set (Lp ℝ 1 μ)) (hM : IsSeparable M)
    (N : Set (Lp ℝ 1 ν)) (hN : IsSeparable N) :
    ∃ (m' : MeasurableSpace X) (hm' : m' ≤ m₀)
      (n' : MeasurableSpace Y) (hn' : n' ≤ n₀),
      m ≤ m' ∧ n ≤ n' ∧ @CountablyGenerated X m' ∧ @CountablyGenerated Y n' ∧
      M ⊆ lOneSubsigma μ m' ∧ N ⊆ lOneSubsigma ν n' ∧
      ∃ hmap : ∀ f, S (lOneSubsigmaEmbedding μ hm' f) ∈ lOneSubsigma ν n',
        IsSingularOperator (lOneSubsigmaLift ν hn'
          (S.comp (lOneSubsigmaEmbedding μ hm').toContinuousLinearMap) hmap) := by
  obtain ⟨Wm, hcm, hWm⟩ :=
    @exists_countable_lOne_subsigma_modulus_witnesses X Y m₀ n₀ μ ν _
      (S - @integralRankOne X Y m₀ n₀ μ ν _ _)
  obtain ⟨Wp, hcp, hWp⟩ :=
    @exists_countable_lOne_subsigma_modulus_witnesses X Y m₀ n₀ μ ν _
      (S + @integralRankOne X Y m₀ n₀ μ ν _ _)
  obtain ⟨m', hm', hmm', hmc', hinc⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement μ m hm hmc
      (M ∪ (Wm ∪ Wp)) (hM.union (hcm.union hcp).isSeparable)
  letI := hmc'
  have himage : IsSeparable (S '' (lOneSubsigma μ m' : Set (Lp ℝ 1 μ))) :=
    (isSeparable_lOneSubsigma μ hm').image S.continuous
  obtain ⟨n', hn', hnn', hnc', hout⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement ν n hn hnc
      (N ∪ S '' (lOneSubsigma μ m' : Set (Lp ℝ 1 μ))) (hN.union himage)
  have hmap : ∀ f, S (lOneSubsigmaEmbedding μ hm' f) ∈ lOneSubsigma ν n' := by
    intro f
    apply hout
    apply mem_union_right
    refine ⟨lOneSubsigmaEmbedding μ hm' f, ?_, rfl⟩
    rw [← range_lOneSubsigmaEmbedding μ hm']
    exact mem_range_self f
  refine ⟨m', hm', n', hn', hmm', hnn', hmc', hnc',
    fun _ h => hinc (mem_union_left _ h), fun _ h => hout (mem_union_left _ h), hmap, ?_⟩
  apply @isSingularOperator_lOneSubsigmaLift X Y m₀ n₀ μ ν _ _ S hS m' n' hm' hn' hmap
  · exact hWm m' hm' (fun _ h => hinc (mem_union_right _ (mem_union_left _ h)))
  · exact hWp m' hm' (fun _ h => hinc (mem_union_right _ (mem_union_right _ h)))

end ThesisCommon
