import Posets.PFPOrdinalTransfiniteLocalFactors
import Posets.OrdinalAnchoredSupportedAssembly

/-! The extracted local inverses assemble on every vector of the genuine
transfinite c₀ sum. Ceiling normalization gives exact anchored reading of
the original operator, so no endpoint-row smallness is assumed. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2400000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

namespace PFPOrdinalTransfinitePaddedCores
variable {Λ γ : Ordinal.{u}} {N : ℕ}
  {R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)} {hγ : IsSuccLimit γ}
  {T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)}
  (F : PFPOrdinalTransfinitePaddedCores R hγ T (1 / 100) (1 / 100))

theorem exists_block_factorization :
    ∃ J : JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)))
        →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ),
    ∃ V : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜]
        JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i))),
      V.comp ((if F.colour then T else ContinuousLinearMap.id 𝕜 _ - T).comp J) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖J‖ ≤ 1 ∧ ‖V‖ ≤ 5 := by
  classical
  choose J q B hB hBn hJs hqc using F.exists_local_factors
  let P := R.pfpPaddedSequence hγ
  let G : Iio Λ → Set (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) :=
    fun i => range (R.pfpPaddedEmbedding hγ (F.index i))
  have hG : Pairwise (fun i j => Disjoint (G i) (G j)) :=
    fun _ _ hij => R.pfpPaddedEmbedding_disjoint hγ (F.injective.ne hij)
  let J₀ := ordinalAnchoredSupportedInsertion G hG J hJs
  have hqplace : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet P.blockMap (F.index i) :=
    fun i x => P.sourceEmbedding_range_subset_block (F.index i) (F.block i (hqc i x))
  let Q := ordinalAnchoredBlockReadback (𝕜 := 𝕜) P.blockMap P.blockMap_strictMono
    P.blockMap_endpoint P.blockMap_zero F.index F.injective q hqplace
  let A := if F.colour then T else ContinuousLinearMap.id 𝕜 _ - T
  let W := if F.colour then R.pfpNormalizedZeroOperator hγ T
    else ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T
  have hz (f : JLMS.CZeroSum 𝕜 (fun i : Iio Λ =>
      JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)))) (η : JLMS.OrdinalInterval Λ) :
      wolfeDisjointSynthesis G hG J hJs f (P.blockMap η) = 0 := by
    by_contra hn
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ordinalIndexedSynthesis_support G hG J hJs f hn)
    exact disjoint_left.mp (P.sourceEmbedding_range_disjoint_boundary (F.index i)) hi (mem_range_self η)
  have hkernel : ∀ f i x, Q (A (J₀ f)) i x =
      W (wolfeDisjointSynthesis G hG J hJs f) (q i x) := by
    intro f i x
    have hr := ordinalEmbeddingCeiling_eq_block_right P.blockMap P.blockMap_strictMono
      P.blockMap_endpoint (F.index i) (q i x) (hqplace i x)
    cases hc : F.colour with
    | true =>
        simp only [A, W, hc, if_true]
        change T (J₀ f) (q i x) - T (J₀ f)
          (P.blockMap ⟨succ (F.index i).val, Ordinal.zero_le _, succ_le_of_lt (F.index i).property⟩) =
            T (J₀ f) (q i x) - T (J₀ f) (P.blockMap (JLMS.ordinalEmbeddingCeiling P.blockMap (q i x)))
        rw [hr]
    | false =>
        simp only [A, W, hc, Bool.false_eq_true, if_false]
        change (J₀ f (q i x) - T (J₀ f) (q i x)) -
          (J₀ f (P.blockMap ⟨succ (F.index i).val, Ordinal.zero_le _,
            succ_le_of_lt (F.index i).property⟩) - T (J₀ f)
              (P.blockMap ⟨succ (F.index i).val, Ordinal.zero_le _, succ_le_of_lt (F.index i).property⟩)) =
          J₀ f (q i x) - (T (J₀ f) (q i x) -
            T (J₀ f) (P.blockMap (JLMS.ordinalEmbeddingCeiling P.blockMap (q i x))))
        rw [hr]
        have hzero : J₀ f (P.blockMap ⟨succ (F.index i).val, Ordinal.zero_le _,
            succ_le_of_lt (F.index i).property⟩) = 0 := hz f _
        rw [hzero]
        abel
  have hcross : ∀ i x, ‖JLMS.atomicRestriction (JLMS.ordinalAtomicDualModel (𝕜 := 𝕜) _)
      (wolfeIndexedCrossUnion G i) ((JLMS.evaluation (q i x)).comp W)‖ ≤ (1 / 100 : ℝ) :=
    fun i x => (F.cross i _ (hqc i x)).le
  obtain ⟨V, hV, hVn⟩ := ordinalIndexed_factors_of_coordinate_inverses G hG J hJs
    (JLMS.ordinalAtomicDualModel _) W q A J₀ Q
    (ordinalAnchoredBlockReadback_norm_le _ _ _ _ _ _ _ _) hkernel B
    (r := (47 / 100 : ℝ)) (δ := (1 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; norm_num; exact hBn i) hB hcross
  refine ⟨J₀, V, hV, ordinalAnchoredSupportedInsertion_norm_le G hG J hJs, ?_⟩
  norm_num at hVn
  linarith

end PFPOrdinalTransfinitePaddedCores
end Posets
