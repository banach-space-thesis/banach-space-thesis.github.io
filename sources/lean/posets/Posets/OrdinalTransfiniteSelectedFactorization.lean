import Posets.OrdinalTransfiniteOperatorCores
import Posets.OrdinalTransfiniteSelectedTargetSequence
import Posets.OrdinalAnchoredInverseAssembly

/-! Concrete factors of the original operator on the selected cofinal blocks. -/

noncomputable section
open Set Order Topology
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000

local instance transfiniteSelectedSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance transfiniteSelectedSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

namespace OrdinalTransfiniteColouredCores

theorem selected_factorization
    {c : Cardinal.{0}} {γ : Ordinal.{0}} {N : ℕ}
    {R : OrdinalTransfiniteRankUnits c.ord γ (2*N+2)} {hγ : IsSuccLimit γ}
    {M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))}
    {T S : JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) →L[𝕜]
      JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))}
    (F : OrdinalTransfiniteColouredCores R hγ M T S (1/100) (1/100))
    (hc : c.IsRegular)
    (A : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ))
    (hW : (if F.colour then T else S) = ordinalCeilingCorrectedCZero
      (R.paddedSequence hγ).blockMap (R.paddedSequence hγ).blockMap_strictMono
      (R.paddedSequence hγ).blockMap_endpoint F.colour A) :
    let Q := R.selectedTargetSequence hc (by omega) hγ F.index F.injective
    ∃ J : JLMS.CZeroSum 𝕜 (fun i : Iio c.ord => JLMS.OrdinalC 𝕜 (Q.endpoint i)) →L[𝕜]
        JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ),
    ∃ L : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜]
        JLMS.CZeroSum 𝕜 (fun i : Iio c.ord => JLMS.OrdinalC 𝕜 (Q.endpoint i)),
      L.comp (A.comp J) = ContinuousLinearMap.id 𝕜 _ ∧ ‖J‖ ≤ 1 ∧ ‖L‖ ≤ 5 := by
  let Q := R.selectedTargetSequence hc (by omega) hγ F.index F.injective
  let r := R.selectedTargetReindex hc (by omega) hγ F.index F.injective
  have hr : Function.Injective r := R.selectedTargetReindex_injective hc (by omega) hγ F.index F.injective
  let P := R.paddedSequence hγ
  let k : Iio c.ord → Iio c.ord := fun i => F.index (r i)
  have hk : Function.Injective k := F.injective.comp hr
  let G : Iio c.ord → Set (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) :=
    fun i => range (P.sourceEmbedding (k i))
  have hG : Pairwise (fun i j => Disjoint (G i) (G j)) :=
    fun i j hij => P.sourceEmbedding_ranges_disjoint (hk.ne hij)
  have hex (i : Iio c.ord) :
      ∃ J : JLMS.OrdinalC 𝕜 (Q.endpoint i) →ₗᵢ[𝕜]
          JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
      ∃ q : C(JLMS.OrdinalInterval (Q.endpoint i), JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
      ∃ B : JLMS.OrdinalC 𝕜 (Q.endpoint i) →L[𝕜] JLMS.OrdinalC 𝕜 (Q.endpoint i),
        B.comp (ordinalBandCompression (if F.colour then T else S) J.toContinuousLinearMap q) =
          ContinuousLinearMap.id 𝕜 _ ∧ ‖B‖ ≤ 1/(1/2-3*(1/100 : ℝ)) ∧
        (∀ f, Function.support (J f) ⊆ G i) ∧ (∀ x, q x ∈ F.core (r i)) := by
    have hQi : Q.endpoint i = Ordinal.omega0 ^ R.unit (F.index (r i)) :=
      R.selectedTargetSequence_endpoint hc (by omega) hγ F.index F.injective i
    rw [hQi]
    simpa only [G, P, k] using F.localInverse (by norm_num) (by norm_num) (r i)
  choose J q B hB hBn hsupp hq using hex
  have hqplace : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet P.blockMap (k i) :=
    fun i x => P.sourceEmbedding_range_subset_block (k i) (F.block (r i) (hq i x))
  let read := ordinalAnchoredBlockReadback (𝕜 := 𝕜) P.blockMap P.blockMap_strictMono
    P.blockMap_endpoint P.blockMap_zero k hk q hqplace
  let J₀ := (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) (Ordinal.omega0 ^ γ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (wolfeDisjointSynthesis G hG J hsupp)
  have hzeroInsert : ∀ f η, wolfeDisjointSynthesis G hG J hsupp f (P.blockMap η) = 0 := by
    intro f η
    by_contra hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ordinalIndexedSynthesis_support G hG J hsupp f hne)
    exact disjoint_left.mp (P.sourceEmbedding_range_disjoint_boundary (k i)) hi (mem_range_self η)
  have hkernel : ∀ f i x, read (A (J₀ f)) i x =
      (if F.colour then T else S) (wolfeDisjointSynthesis G hG J hsupp f) (q i x) := by
    intro f i x
    rw [hW, ordinalCeilingCorrectedCZero_apply_of_range_zero _ _ _ _ _ _ (hzeroInsert f),
      ordinalEmbeddingCeiling_eq_block_right P.blockMap P.blockMap_strictMono P.blockMap_endpoint
        (k i) (q i x) (hqplace i x)]
    rfl
  have hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion G i)
      ((JLMS.evaluation (q i x)).comp (if F.colour then T else S))‖ ≤ (1/100 : ℝ) := by
    intro i x
    have hsub := wolfeIndexedCrossUnion_reindex_subset
      (fun j => range (P.sourceEmbedding (F.index j))) hr i
    exact (wolfeMass_mono M (wolfeOperatorRow (if F.colour then T else S) (q i x)) hsub).trans
      (F.cross (r i) (q i x) (hq i x)).le
  obtain ⟨L, hf, hL⟩ := ordinalIndexed_factors_of_coordinate_inverses G hG J hsupp M
    (if F.colour then T else S) q A J₀ read
    (ordinalAnchoredBlockReadback_norm_le P.blockMap P.blockMap_strictMono
      P.blockMap_endpoint P.blockMap_zero k hk q hqplace)
    hkernel B (by norm_num : (0 : ℝ) < 1/2-3*(1/100))
    (by norm_num : (0 : ℝ) ≤ 1/100) (by norm_num : (1/100 : ℝ) < 1/2-3*(1/100)) hBn hB hcross
  refine ⟨J₀, L, hf, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖(JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) (Ordinal.omega0 ^ γ)).symm
      (wolfeDisjointSynthesis G hG J hsupp f)‖ ≤ 1 * ‖f‖
    rw [LinearIsometryEquiv.norm_map, wolfeDisjointSynthesis_norm, one_mul]
  · exact hL.trans (by norm_num)

end OrdinalTransfiniteColouredCores
end Posets

