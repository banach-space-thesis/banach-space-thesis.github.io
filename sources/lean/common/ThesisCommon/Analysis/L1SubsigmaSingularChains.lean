import ThesisCommon.Analysis.L1SubsigmaModulusChains
import ThesisCommon.Analysis.L1SubsigmaSingular
import ThesisCommon.Analysis.RichFamilyProducts

/-! Exact singularity of a trimmed-space operator is equivalent to equality
of two restricted ambient moduli. This equivalence makes singularity pass
to the actual closure of an increasing chain of input/output L1 subspaces. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem isSingularOperator_lOneSubsigmaLift_iff
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {m : MeasurableSpace X} {n : MeasurableSpace Y} (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, S (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n) :
    IsSingularOperator (lOneSubsigmaLift ν hn
      (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) ↔
    |(S - @integralRankOne X Y m₀ n₀ μ ν _ _).comp
      (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap| =
    |(S + @integralRankOne X Y m₀ n₀ μ ν _ _).comp
      (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap| := by
  let R := lOneSubsigmaLift ν hn
    (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap
  let L := (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap
  have hR : L.comp R = S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap :=
    lOneSubsigmaEmbedding_lift ν hn _ hmap
  have hrank := lOneSubsigmaEmbedding_rankOne (μ := μ) (ν := ν) hm hn
  have hminus : L.comp (R - integralRankOne (μ.trim hm) (ν.trim hn)) =
      (S - @integralRankOne X Y m₀ n₀ μ ν _ _).comp
        (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_sub, hR, hrank, ContinuousLinearMap.sub_comp]
  have hplus : L.comp (R + integralRankOne (μ.trim hm) (ν.trim hn)) =
      (S + @integralRankOne X Y m₀ n₀ μ ν _ _).comp
        (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_add, hR, hrank, ContinuousLinearMap.add_comp]
  rw [← hminus, ← hplus,
    @abs_lOneOperator_postcomp X Y Y m n n₀ (μ.trim hm) (ν.trim hn) ν _ L
      (lOneSubsigmaEmbedding_abs ν hn),
    @abs_lOneOperator_postcomp X Y Y m n n₀ (μ.trim hm) (ν.trim hn) ν _ L
      (lOneSubsigmaEmbedding_abs ν hn)]
  rw [@isSingularOperator_iff_abs_sub_rankOne_eq_abs_add X Y m n
    (μ.trim hm) (ν.trim hn) _ _]
  constructor
  · intro h
    exact congrArg (fun T => L.comp T) h
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    exact (lOneSubsigmaEmbedding ν hn).injective (DFunLike.congr_fun h f)

theorem isSingularOperator_lOneSubsigmaLift_iSup
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (m : ℕ → MeasurableSpace X) (n : ℕ → MeasurableSpace Y)
    (hm : ∀ i, m i ≤ m₀) (hn : ∀ i, n i ≤ n₀)
    (hmono : Monotone (fun i => lOneSubsigma μ (m i)))
    (hmap : ∀ i, ∀ f, S (lOneSubsigmaEmbedding μ (hm i) f) ∈ lOneSubsigma ν (n i))
    (hsing : ∀ i, @IsSingularOperator X Y (m i) (n i) (μ.trim (hm i)) (ν.trim (hn i))
      (lOneSubsigmaLift ν (hn i)
      (S.comp (lOneSubsigmaEmbedding μ (hm i)).toContinuousLinearMap) (hmap i)))
    (hfinal : ∀ f, S (lOneSubsigmaEmbedding μ (iSup_le hm) f) ∈
      lOneSubsigma ν (⨆ i, n i)) :
    @IsSingularOperator X Y (⨆ i, m i) (⨆ i, n i) (μ.trim (iSup_le hm)) (ν.trim (iSup_le hn))
      (lOneSubsigmaLift ν (iSup_le hn)
      (S.comp (lOneSubsigmaEmbedding μ (iSup_le hm)).toContinuousLinearMap) hfinal) := by
  apply (@isSingularOperator_lOneSubsigmaLift_iff X Y m₀ n₀ μ ν _ _ S
    (⨆ i, m i) (⨆ i, n i) (iSup_le hm) (iSup_le hn) hfinal).mpr
  apply @lOneSubsigma_moduli_eq_iSup X Y m₀ n₀ μ ν _
    (S - @integralRankOne X Y m₀ n₀ μ ν _ _)
    (S + @integralRankOne X Y m₀ n₀ μ ν _ _) m hm hmono
  intro i
  exact (@isSingularOperator_lOneSubsigmaLift_iff X Y m₀ n₀ μ ν _ _ S
    (m i) (n i) (hm i) (hn i) (hmap i)).mp (hsing i)

end ThesisCommon
