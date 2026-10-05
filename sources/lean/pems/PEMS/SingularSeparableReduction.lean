import PEMS.ModulusSeparableReduction
import ThesisCommon.Analysis.L1SubsigmaSingularChains

/-! Lemma 4.9 for real finite measure spaces. The family consists exactly
of products of countably generated L1 subspaces on which the actual lifted
operator is singular. Both cofinality and closure under increasing chains
are proved, including the chain argument omitted in the source proof. -/
noncomputable section
open MeasureTheory MeasurableSpace Set ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def singularPreservingL1Family (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    Set (Submodule ℝ (Lp ℝ 1 μ × Lp ℝ 1 ν)) :=
  {P | ∃ (m : MeasurableSpace X) (hm : m ≤ m₀)
      (n : MeasurableSpace Y) (hn : n ≤ n₀),
    @CountablyGenerated X m ∧ @CountablyGenerated Y n ∧
    P = (lOneSubsigma μ m).prod (lOneSubsigma ν n) ∧
    ∃ hmap : ∀ f, S (lOneSubsigmaEmbedding μ hm f) ∈ lOneSubsigma ν n,
      IsSingularOperator (lOneSubsigmaLift ν hn
        (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap)}

theorem lemma_4_9_singular_rich (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : IsSingularOperator S) : IsRichFamily (singularPreservingL1Family S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro P ⟨m, hm, n, hn, _, _, rfl, _⟩
    exact (isClosed_lOneSubsigma μ hm).prod (isClosed_lOneSubsigma ν hn)
  · rintro P ⟨m, hm, n, hn, hmc, hnc, rfl, _⟩
    letI := hmc
    letI := hnc
    exact (isSeparable_lOneSubsigma μ hm).prod (isSeparable_lOneSubsigma ν hn)
  · intro D hD
    obtain ⟨m, hm, n, hn, _, _, hmc, hnc, hM, hN, hmap, hsing⟩ :=
      @exists_countablyGenerated_singular_lOneSubsigma_reduction X Y m₀ n₀ μ ν _ _
        S hS ⊥ bot_le (countablyGenerated_bot X) ⊥ bot_le (countablyGenerated_bot Y)
        (Prod.fst '' D) (hD.image continuous_fst) (Prod.snd '' D) (hD.image continuous_snd)
    refine ⟨(lOneSubsigma μ m).prod (lOneSubsigma ν n),
      ⟨m, hm, n, hn, hmc, hnc, rfl, hmap, hsing⟩, ?_⟩
    intro p hp
    exact ⟨hM ⟨p, hp, rfl⟩, hN ⟨p, hp, rfl⟩⟩
  · intro V hV hmono
    choose m hm n hn hmc hnc heq hmap hsing using hV
    let E := fun i => lOneSubsigma μ (m i)
    let F := fun i => lOneSubsigma ν (n i)
    have hEmono : Monotone E := by
      intro i j hij f hf
      have hi : (f, (0 : Lp ℝ 1 ν)) ∈ V i := by
        rw [heq i]
        exact ⟨hf, (F i).zero_mem⟩
      have hj := hmono hij hi
      rw [heq j] at hj
      exact hj.1
    have hFmono : Monotone F := by
      intro i j hij g hg
      have hi : ((0 : Lp ℝ 1 μ), g) ∈ V i := by
        rw [heq i]
        exact ⟨(E i).zero_mem, hg⟩
      have hj := hmono hij hi
      rw [heq j] at hj
      exact hj.2
    have hEc : richChainClosure E = lOneSubsigma μ (⨆ i, m i) :=
      richChainClosure_lOneSubsigma μ m hm hEmono
    have hFc : richChainClosure F = lOneSubsigma ν (⨆ i, n i) :=
      richChainClosure_lOneSubsigma ν n hn hFmono
    have hEF : ∀ i, ∀ f ∈ E i, S f ∈ F i := by
      intro i f hf
      change f ∈ (lOneSubsigma μ (m i) : Set (Lp ℝ 1 μ)) at hf
      rw [← range_lOneSubsigmaEmbedding μ (hm i)] at hf
      obtain ⟨g, rfl⟩ := hf
      exact hmap i g
    have hmapc := continuousLinearMap_maps_richChainClosure S E F hEmono hEF
    rw [hEc, hFc] at hmapc
    have hfinal : ∀ f, S (lOneSubsigmaEmbedding μ (iSup_le hm) f) ∈
        lOneSubsigma ν (⨆ i, n i) := by
      intro f
      apply hmapc
      change lOneSubsigmaEmbedding μ (iSup_le hm) f ∈
        (lOneSubsigma μ (⨆ i, m i) : Set (Lp ℝ 1 μ))
      rw [← range_lOneSubsigmaEmbedding μ (iSup_le hm)]
      exact mem_range_self f
    refine ⟨⨆ i, m i, iSup_le hm, ⨆ i, n i, iSup_le hn,
      countablyGenerated_iSup m hmc, countablyGenerated_iSup n hnc, ?_, hfinal, ?_⟩
    · rw [show V = (fun i => (E i).prod (F i)) from funext heq,
        richChainClosure_prod E F hEmono hFmono, hEc, hFc]
    · exact @isSingularOperator_lOneSubsigmaLift_iSup X Y m₀ n₀ μ ν _ _
        S m n hm hn hEmono hmap hsing hfinal

end PEMS
