import Posets.OrdinalAnchoredInverseAssembly

/-! The literal isometries and coordinate inverses supplied by the selected
band geometry assemble without exposing the cell's internal coordinate map. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1800000
variable {𝕜 I : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
  {D : I → Type*} [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
local instance anchoredSupportedCoordinateGroup (i : I) : NormedAddCommGroup C(D i, 𝕜) := inferInstance
local instance anchoredSupportedCoordinateSpace (i : I) : NormedSpace 𝕜 C(D i, 𝕜) := inferInstance
local instance anchoredSupportedSumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance
local instance anchoredSupportedSumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance

variable (G : I → Set (JLMS.OrdinalInterval β))
  (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
  (J : ∀ i, C(D i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 (JLMS.OrdinalInterval β))
  (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)

def ordinalAnchoredSupportedInsertion :
    JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (wolfeDisjointSynthesis G hG J hsupp)

theorem ordinalAnchoredSupportedInsertion_norm_le :
    ‖ordinalAnchoredSupportedInsertion G hG J hsupp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm
    (wolfeDisjointSynthesis G hG J hsupp f)‖ ≤ 1 * ‖f‖
  rw [LinearIsometryEquiv.norm_map, wolfeDisjointSynthesis_norm, one_mul]

theorem ordinalAnchored_supported_factors_of_coordinate_inverses
    (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (index : I → Iio γ) (hindex : Function.Injective index)
    (G : I → Set (JLMS.OrdinalInterval β))
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (J : ∀ i, C(D i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 (JLMS.OrdinalInterval β))
    (hsupp : ∀ i f, Function.support (J i f) ⊆ G i)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β)) (hqG : ∀ i x, q i x ∈ G i)
    (hplace : ∀ i, G i ⊆ JLMS.ordinalSpaceBlockSet g (index i))
    (hanchor : ∀ i, Disjoint (G i) (range g))
    (M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval β))
    (b : Bool) (A : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (W : JLMS.CZero 𝕜 (JLMS.OrdinalInterval β) →L[𝕜] JLMS.CZero 𝕜 (JLMS.OrdinalInterval β))
    (hW : W = ordinalCeilingCorrectedCZero g hg htop b A)
    (B : ∀ i, C(D i, 𝕜) →L[𝕜] C(D i, 𝕜))
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hgap : δ < r)
    (hBn : ∀ i, ‖B i‖ ≤ 1 / r)
    (hB : ∀ i, (B i).comp (ordinalBandCompression W (J i).toContinuousLinearMap (q i)) =
      ContinuousLinearMap.id 𝕜 C(D i, 𝕜))
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion G i)
      ((JLMS.evaluation (q i x)).comp W)‖ ≤ δ) :
    ∃ R : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)),
      R.comp (A.comp (ordinalAnchoredSupportedInsertion G hG J hsupp)) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / (r - δ) := by
  have hqplace : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (index i) :=
    fun i x => hplace i (hqG i x)
  let read := ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero index hindex q hqplace
  have hzeroInsert : ∀ f η, wolfeDisjointSynthesis G hG J hsupp f (g η) = 0 := by
    intro f η
    by_contra hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ordinalIndexedSynthesis_support G hG J hsupp f hne)
    exact disjoint_left.mp (hanchor i) hi (mem_range_self η)
  have hkernel : ∀ f i x,
      read (A (ordinalAnchoredSupportedInsertion G hG J hsupp f)) i x =
        W (wolfeDisjointSynthesis G hG J hsupp f) (q i x) := by
    intro f i x
    rw [hW, ordinalCeilingCorrectedCZero_apply_of_range_zero _ _ _ _ _ _ (hzeroInsert f),
      ordinalEmbeddingCeiling_eq_block_right g hg htop (index i) (q i x) (hqplace i x)]
    rfl
  exact ordinalIndexed_factors_of_coordinate_inverses G hG J hsupp M W q A
    (ordinalAnchoredSupportedInsertion G hG J hsupp) read
    (ordinalAnchoredBlockReadback_norm_le g hg htop hzero index hindex q hqplace)
    hkernel B hr hδ hgap hBn hB hcross

end Posets


