import Posets.OrdinalInfiniteCrossMass
import Posets.OrdinalAnchoredBlockReadback
import Posets.OrdinalCeilingOperatorCorrection
import Posets.OrdinalBandAnchorExclusion
import Posets.OrdinalBandCoordinateInverse
import Posets.OrdinalBandInsertion
import Posets.WolfeDisjointSynthesis
import Posets.CZeroCenteredInverseAssembly

/-! Actual arbitrary-index anchored assembly from compact clopen cells,
uniform local inverses and one bound on each entire cross-cell row. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1800000

variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {D : I → Type*} [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)]

local instance indexedCoordinateGroup (i : I) : NormedAddCommGroup C(D i, 𝕜) := inferInstance
local instance indexedCoordinateSpace (i : I) : NormedSpace 𝕜 C(D i, 𝕜) := inferInstance
local instance indexedSumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance
local instance indexedSumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance

variable (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
  (J : ∀ i, C(D i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
  (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)

theorem ordinalIndexedSynthesis_single (i : I) (f : C(D i, 𝕜)) :
    wolfeDisjointSynthesis H hH J hsupp (JLMS.CZeroSum.single i f) = J i f := by
  classical
  change (∑' j, J j (JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun i => C(D i, 𝕜)) i f j)) = J i f
  rw [tsum_eq_single i]
  · rw [JLMS.CZeroSum.single_apply_self]
  · intro j hji
    rw [JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun i => C(D i, 𝕜)) i f hji, map_zero]

theorem ordinalIndexedSynthesis_support (f : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) :
    Function.support (wolfeDisjointSynthesis H hH J hsupp f) ⊆ ⋃ i, H i := by
  classical
  intro x hx
  by_contra hn
  have hv := (JLMS.evaluation x).hasSum
    (JLMS.hasSum_cZeroSumSynthesis (fun i => (J i).toContinuousLinearMap)
      (wolfe_disjoint_finite_sum_bound H hH J hsupp) f)
  change HasSum (fun i => J i (f i) x) (wolfeDisjointSynthesis H hH J hsupp f x) at hv
  apply hx
  rw [← hv.tsum_eq]
  have hz : ∀ i, J i (f i) x = 0 := by
    intro i
    by_contra hi
    exact hn (mem_iUnion.mpr ⟨i, hsupp i (f i) hi⟩)
  simp only [hz, tsum_zero]

theorem ordinalIndexedSynthesis_remainder_support
    (f : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) (i : I) :
    Function.support (wolfeDisjointSynthesis H hH J hsupp f - J i (f i)) ⊆
      wolfeIndexedCrossUnion H i := by
  intro x hx
  by_cases hxi : x ∈ H i
  · exact False.elim (hx (by
      change wolfeDisjointSynthesis H hH J hsupp f x - J i (f i) x = 0
      rw [wolfeDisjointSynthesis_apply_mem H hH J hsupp f hxi, sub_self]))
  · have hi0 : J i (f i) x = 0 := by by_contra hn; exact hxi (hsupp i (f i) hn)
    have hn : wolfeDisjointSynthesis H hH J hsupp f x ≠ 0 := by
      intro hz
      exact hx (by change wolfeDisjointSynthesis H hH J hsupp f x - J i (f i) x = 0; rw [hz, hi0, sub_self])
    obtain ⟨j, hj⟩ := mem_iUnion.mp (ordinalIndexedSynthesis_support H hH J hsupp f hn)
    exact (mem_wolfeIndexedCrossUnion H i x).mpr ⟨j, fun he => hxi (he ▸ hj), hj⟩

theorem ordinalIndexedSynthesis_remainder_norm
    (f : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) (i : I) :
    ‖wolfeDisjointSynthesis H hH J hsupp f - J i (f i)‖ ≤ ‖f‖ := by
  classical
  have he : wolfeDisjointSynthesis H hH J hsupp (f - JLMS.CZeroSum.single i (f i)) =
      wolfeDisjointSynthesis H hH J hsupp f - J i (f i) := by
    rw [map_sub, ordinalIndexedSynthesis_single H hH J hsupp]
  rw [← he, wolfeDisjointSynthesis_norm H hH J hsupp]
  apply JLMS.CZeroSum.norm_le (norm_nonneg f)
  intro j
  by_cases hji : j = i
  · subst j
    simp only [JLMS.CZeroSum.sub_apply, JLMS.CZeroSum.single_apply_self, sub_self, norm_zero]
    exact norm_nonneg f
  · simpa only [JLMS.CZeroSum.sub_apply,
      JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun i => C(D i, 𝕜)) i (f i) hji,
      sub_zero] using f.norm_apply_le_norm j

theorem ordinalIndexed_cross_error (M : JLMS.AtomicDualModel 𝕜 K)
    (W : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(D i, K))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp W)‖ ≤ δ)
    (f : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) (i : I) (x : D i) :
    ‖W (wolfeDisjointSynthesis H hH J hsupp f) (q i x) - W (J i (f i)) (q i x)‖ ≤ δ * ‖f‖ := by
  let φ := (JLMS.evaluation (q i x)).comp W
  let g := wolfeDisjointSynthesis H hH J hsupp f - J i (f i)
  have he : φ g = W (wolfeDisjointSynthesis H hH J hsupp f) (q i x) -
      W (J i (f i)) (q i x) := by simp [φ, g]
  rw [← he, ← ordinalBand_atomic_apply_of_support M φ g
    (ordinalIndexedSynthesis_remainder_support H hH J hsupp f i)]
  exact ((JLMS.atomicRestriction M (wolfeIndexedCrossUnion H i) φ).le_opNorm g).trans
    (mul_le_mul (hmass i x) (ordinalIndexedSynthesis_remainder_norm H hH J hsupp f i)
      (norm_nonneg g) hδ)

theorem ordinalIndexedBandCompression_norm_le
    (W : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(D i, K)) (i : I) :
    ‖ordinalBandCompression W (J i).toContinuousLinearMap (q i)‖ ≤ ‖W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ W.opNorm_nonneg
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg W.opNorm_nonneg (norm_nonneg f))).mpr
  intro x
  exact (JLMS.norm_CZero_apply_le (W (J i f)) (q i x)).trans
    (by simpa only [LinearIsometry.norm_map] using W.le_opNorm (J i f))

def ordinalIndexedRawDiagonal
    (W : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(D i, K)) :
    JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) :=
  JLMS.CZeroSum.mapCLM (fun i => ordinalBandCompression W (J i).toContinuousLinearMap (q i))
    W.opNorm_nonneg (ordinalIndexedBandCompression_norm_le J W q)

theorem ordinalIndexed_factors_of_coordinate_inverses
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (M : JLMS.AtomicDualModel 𝕜 K)
    (W : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (q : ∀ i, C(D i, K))
    (A : E →L[𝕜] F)
    (J₀ : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] E)
    (read : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)))
    (hread : ‖read‖ ≤ 2)
    (hkernel : ∀ f i x, read (A (J₀ f)) i x =
      W (wolfeDisjointSynthesis H hH J hsupp f) (q i x))
    (B : ∀ i, C(D i, 𝕜) →L[𝕜] C(D i, 𝕜))
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hgap : δ < r)
    (hBn : ∀ i, ‖B i‖ ≤ 1 / r)
    (hB : ∀ i, (B i).comp (ordinalBandCompression W (J i).toContinuousLinearMap (q i)) =
      ContinuousLinearMap.id 𝕜 C(D i, 𝕜))
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion H i)
      ((JLMS.evaluation (q i x)).comp W)‖ ≤ δ) :
    ∃ R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)),
      R.comp (A.comp J₀) = ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / (r - δ) := by
  let C := read.comp (A.comp J₀)
  let diagonal := ordinalIndexedRawDiagonal J W q
  let Dinv := JLMS.CZeroSum.mapCLM B (one_div_pos.mpr hr).le hBn
  have hDn : ‖Dinv‖ ≤ 1 / r := JLMS.CZeroSum.norm_mapCLM_le B (one_div_pos.mpr hr).le hBn
  have hDB : Dinv.comp diagonal = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro f
    apply JLMS.CZeroSum.ext
    intro i
    exact congrArg (fun V : C(D i, 𝕜) →L[𝕜] C(D i, 𝕜) => V (f i)) (hB i)
  have herror : ‖C - diagonal‖ ≤ δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hδ
    intro f
    apply JLMS.CZeroSum.norm_le (mul_nonneg hδ (norm_nonneg f))
    intro i
    apply (ContinuousMap.norm_le _ (mul_nonneg hδ (norm_nonneg f))).mpr
    intro x
    change ‖read (A (J₀ f)) i x - W (J i (f i)) (q i x)‖ ≤ δ * ‖f‖
    rw [hkernel]
    exact ordinalIndexed_cross_error H hH J hsupp M W q hδ hcross f i x
  obtain ⟨V, hV, hVn⟩ := wolfe_exists_left_inverse_of_approximation C diagonal Dinv
    hr hδ hgap hDn hDB herror
  refine ⟨V.comp read, ?_, ?_⟩
  · simpa only [C, ContinuousLinearMap.comp_assoc] using hV
  · calc
      ‖V.comp read‖ ≤ ‖V‖ * ‖read‖ := V.opNorm_comp_le read
      _ ≤ (1 / (r - δ)) * 2 := mul_le_mul hVn hread (norm_nonneg read)
        (one_div_pos.mpr (sub_pos.mpr hgap)).le
      _ = 2 / (r - δ) := by ring

variable [T2Space K]

def ordinalIndexedBandInsertIsometry (i : I) [CompactSpace (H i)]
    (hi : IsClopen (H i)) (p : C(H i, D i)) (q : C(D i, H i))
    (hq : Function.RightInverse q p) : C(D i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K where
  toLinearMap := (ordinalBandInsert (𝕜 := 𝕜) (H i) hi p).toLinearMap
  norm_map' := by
    intro f
    change ‖ordinalBandInsert (𝕜 := 𝕜) (H i) hi p f‖ = ‖f‖
    apply le_antisymm
    · exact ((ordinalBandInsert (𝕜 := 𝕜) (H i) hi p).le_opNorm f).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (ordinalBandInsert_norm_le (𝕜 := 𝕜) (H i) hi p) (norm_nonneg f))
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      rw [← ordinalBandInsert_read (H i) hi p q hq f x]
      exact JLMS.norm_CZero_apply_le _ _

variable [∀ i, CompactSpace (H i)]
  (hHo : ∀ i, IsClopen (H i))
  (p : ∀ i, C(H i, D i)) (q : ∀ i, C(D i, H i))
  (hsection : ∀ i, Function.RightInverse (q i) (p i))

def ordinalIndexedGeometricInsertion :
    JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] JLMS.CZero 𝕜 K :=
  wolfeDisjointSynthesis H hH
    (fun i => ordinalIndexedBandInsertIsometry (𝕜 := 𝕜) H i (hHo i) (p i) (q i) (hsection i))
    (fun i f => ordinalBandInsert_support (𝕜 := 𝕜) (H i) (hHo i) (p i) f)

theorem ordinalIndexedGeometricInsertion_norm
    (f : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) :
    ‖ordinalIndexedGeometricInsertion H hH hHo p q hsection f‖ = ‖f‖ :=
  wolfeDisjointSynthesis_norm H hH _ _ f

theorem ordinalIndexed_geometric_factors_from_leaf_mass
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (M : JLMS.AtomicDualModel 𝕜 K)
    (W : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (A : E →L[𝕜] F)
    (J₀ : JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] E)
    (read : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)))
    (hread : ‖read‖ ≤ 2)
    (hkernel : ∀ f i x, read (A (J₀ f)) i x =
      W (ordinalIndexedGeometricInsertion H hH hHo p q hsection f) (q i x).val)
    (S : I → Set K) (hSH : ∀ i, S i ⊆ H i)
    (hq : ∀ i x, (q i x).val ∈ closure (S i))
    (V : I → K → Set K) (hVH : ∀ i y, y ∈ S i → V i y ⊆ H i)
    (hV : ∀ i y, y ∈ S i → IsClopen (V i y))
    (hcV : ∀ i y, y ∈ S i → IsCompact (V i y))
    (hp : ∀ i y (hy : y ∈ S i) z (hz : z ∈ V i y),
      p i ⟨z, hVH i y hy hz⟩ = p i ⟨y, hSH i hy⟩)
    {d ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hgap : 3 * ε + δ < d)
    (hd : ∀ i y (hy : y ∈ S i),
      d ≤ ‖W (JLMS.clopenIndicator (V i y) (hV i y hy) (hcV i y hy)) y‖)
    (hmass : ∀ i y, y ∈ S i → ‖JLMS.atomicRestriction M (H i \ V i y)
      ((JLMS.evaluation y).comp W)‖ ≤ ε)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion H i)
      ((JLMS.evaluation (q i x).val).comp W)‖ ≤ δ) :
    ∃ R : F →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)),
      R.comp (A.comp J₀) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖R‖ ≤ 2 / ((d - 3 * ε) - δ) := by
  let J : ∀ i, C(D i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K :=
    fun i => ordinalIndexedBandInsertIsometry (𝕜 := 𝕜) H i (hHo i) (p i) (q i) (hsection i)
  let qK : ∀ i, C(D i, K) := fun i =>
    ⟨fun x => (q i x).val, continuous_subtype_val.comp (q i).continuous⟩
  have hsupp : ∀ i f, Function.support (J i f) ⊆ H i :=
    fun i f => ordinalBandInsert_support (𝕜 := 𝕜) (H i) (hHo i) (p i) f
  have hreadlocal : ∀ i (f : C(D i, 𝕜)) x, J i f (qK i x) = f x := by
    intro i f x
    exact ordinalBandInsert_read (H i) (hHo i) (p i) (q i) (hsection i) f x
  have hconst : ∀ i y, y ∈ S i → ∀ f : C(D i, 𝕜), ∀ z ∈ V i y, J i f z = J i f y := by
    intro i y hy f z hz
    exact ordinalBandInsert_constant_on_fiber (H i) (hHo i) (p i) f
      ⟨z, hVH i y hy hz⟩ ⟨y, hSH i hy⟩ (hp i y hy z hz)
  have hex (i : I) := ordinalBand_coordinate_inverse_from_leaf_mass M W
    (J i).toContinuousLinearMap (qK i) (H i) (hHo i)
    (isCompact_iff_compactSpace.mpr inferInstance)
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro f
      change ‖J i f‖ ≤ 1 * ‖f‖
      rw [LinearIsometry.norm_map, one_mul])
    (hsupp i) (hq i) (hreadlocal i) (V i) (hVH i) (hV i) (hcV i)
    (hconst i) hε (by linarith : 3 * ε < d) (hd i) (hmass i)
  choose B hB hBn using hex
  exact ordinalIndexed_factors_of_coordinate_inverses H hH J hsupp M W qK
    A J₀ read hread hkernel B (by linarith : 0 < d - 3 * ε) hδ
    (by linarith : δ < d - 3 * ε) hBn hB hcross

end Posets


namespace Posets
variable {𝕜 I : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
  {D : I → Type*} [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1800000
local instance anchoredAssemblyCoordinateGroup (i : I) : NormedAddCommGroup C(D i, 𝕜) := inferInstance
local instance anchoredAssemblyCoordinateSpace (i : I) : NormedSpace 𝕜 C(D i, 𝕜) := inferInstance
local instance anchoredAssemblySumGroup : NormedAddCommGroup (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance
local instance anchoredAssemblySumSpace : NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance

def ordinalCeilingCorrectedCZero
    (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (b : Bool) (A : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    JLMS.CZero 𝕜 (JLMS.OrdinalInterval β) →L[𝕜] JLMS.CZero 𝕜 (JLMS.OrdinalInterval β) :=
  (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((if b then ordinalCeilingCorrectedLeft g hg htop A else ordinalCeilingCorrectedRight g hg htop A).comp
      (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem ordinalCeilingCorrectedCZero_apply_of_range_zero
    (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (b : Bool) (A : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (f : JLMS.CZero 𝕜 (JLMS.OrdinalInterval β)) (hf : ∀ η, f (g η) = 0)
    (x : JLMS.OrdinalInterval β) :
    ordinalCeilingCorrectedCZero g hg htop b A f x =
      A ((JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm f) x -
      A ((JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm f) (g (JLMS.ordinalEmbeddingCeiling g x)) := by
  cases b with
  | false => rfl
  | true =>
      change (A ((JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm f) x -
        A ((JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm f) (g (JLMS.ordinalEmbeddingCeiling g x))) +
          f (g (JLMS.ordinalEmbeddingCeiling g x)) = _
      rw [hf, add_zero]

def ordinalAnchoredGeometricInsertion
    (H : I → Set (JLMS.OrdinalInterval β)) [∀ i, CompactSpace (H i)]
    (hH : Pairwise (fun i j => Disjoint (H i) (H j))) (hHo : ∀ i, IsClopen (H i))
    (p : ∀ i, C(H i, D i)) (q : ∀ i, C(D i, H i))
    (hsection : ∀ i, Function.RightInverse (q i) (p i)) :
    JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ordinalIndexedGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection)

theorem ordinalAnchoredGeometricInsertion_norm_le
    (H : I → Set (JLMS.OrdinalInterval β)) [∀ i, CompactSpace (H i)]
    (hH : Pairwise (fun i j => Disjoint (H i) (H j))) (hHo : ∀ i, IsClopen (H i))
    (p : ∀ i, C(H i, D i)) (q : ∀ i, C(D i, H i))
    (hsection : ∀ i, Function.RightInverse (q i) (p i)) :
    ‖ordinalAnchoredGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) β).symm
    (ordinalIndexedGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection f)‖ ≤ 1 * ‖f‖
  rw [LinearIsometryEquiv.norm_map, ordinalIndexedGeometricInsertion_norm, one_mul]

theorem ordinalAnchored_geometric_factors_from_leaf_mass
    (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β)) (hg : StrictMono g)
    (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (index : I → Iio γ) (hindex : Function.Injective index)
    (H : I → Set (JLMS.OrdinalInterval β)) [∀ i, CompactSpace (H i)]
    (hH : Pairwise (fun i j => Disjoint (H i) (H j))) (hHo : ∀ i, IsClopen (H i))
    (hplace : ∀ i, H i ⊆ JLMS.ordinalSpaceBlockSet g (index i))
    (hanchor : ∀ i, Disjoint (H i) (range g))
    (p : ∀ i, C(H i, D i)) (q : ∀ i, C(D i, H i))
    (hsection : ∀ i, Function.RightInverse (q i) (p i))
    (M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval β))
    (b : Bool) (A : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (W : JLMS.CZero 𝕜 (JLMS.OrdinalInterval β) →L[𝕜] JLMS.CZero 𝕜 (JLMS.OrdinalInterval β))
    (hW : W = ordinalCeilingCorrectedCZero g hg htop b A)
    (S : I → Set (JLMS.OrdinalInterval β)) (hSH : ∀ i, S i ⊆ H i)
    (hq : ∀ i x, (q i x).val ∈ closure (S i))
    (V : I → JLMS.OrdinalInterval β → Set (JLMS.OrdinalInterval β))
    (hVH : ∀ i y, y ∈ S i → V i y ⊆ H i)
    (hV : ∀ i y, y ∈ S i → IsClopen (V i y))
    (hcV : ∀ i y, y ∈ S i → IsCompact (V i y))
    (hp : ∀ i y (hy : y ∈ S i) z (hz : z ∈ V i y),
      p i ⟨z, hVH i y hy hz⟩ = p i ⟨y, hSH i hy⟩)
    {d ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hgap : 3 * ε + δ < d)
    (hd : ∀ i y (hy : y ∈ S i),
      d ≤ ‖W (JLMS.clopenIndicator (V i y) (hV i y hy) (hcV i y hy)) y‖)
    (hmass : ∀ i y, y ∈ S i → ‖JLMS.atomicRestriction M (H i \ V i y)
      ((JLMS.evaluation y).comp W)‖ ≤ ε)
    (hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeIndexedCrossUnion H i)
      ((JLMS.evaluation (q i x).val).comp W)‖ ≤ δ) :
    ∃ R : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)),
      R.comp (A.comp (ordinalAnchoredGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection)) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / ((d - 3 * ε) - δ) := by
  let qK : ∀ i, C(D i, JLMS.OrdinalInterval β) := fun i =>
    ⟨fun x => (q i x).val, continuous_subtype_val.comp (q i).continuous⟩
  have hqplace : ∀ i x, qK i x ∈ JLMS.ordinalSpaceBlockSet g (index i) :=
    fun i x => hplace i (q i x).property
  let read := ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero index hindex qK hqplace
  have hzeroInsert : ∀ f η,
      ordinalIndexedGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection f (g η) = 0 := by
    intro f η
    by_contra hne
    have hs := ordinalIndexedSynthesis_support H hH
      (fun i => ordinalIndexedBandInsertIsometry (𝕜 := 𝕜) H i (hHo i) (p i) (q i) (hsection i))
      (fun i f => ordinalBandInsert_support (𝕜 := 𝕜) (H i) (hHo i) (p i) f) f hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact disjoint_left.mp (hanchor i) hi (mem_range_self η)
  have hkernel : ∀ f i x, read (A (ordinalAnchoredGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection f)) i x =
      W (ordinalIndexedGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection f) (q i x).val := by
    intro f i x
    rw [hW, ordinalCeilingCorrectedCZero_apply_of_range_zero _ _ _ _ _ _ (hzeroInsert f),
      ordinalEmbeddingCeiling_eq_block_right g hg htop (index i) (q i x).val (hqplace i x)]
    rfl
  exact ordinalIndexed_geometric_factors_from_leaf_mass H hH hHo p q hsection M W A
    (ordinalAnchoredGeometricInsertion (𝕜 := 𝕜) H hH hHo p q hsection) read
    (ordinalAnchoredBlockReadback_norm_le g hg htop hzero index hindex qK hqplace)
    hkernel S hSH hq V hVH hV hcV hp hε hδ hgap hd hmass hcross

end Posets

