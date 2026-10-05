import Posets.OrdinalRegularOmegaAssemblyEscape
import Posets.OrdinalBandInsertion
import Posets.WolfeDisjointSynthesis
import Posets.WolfeRankedCrossMassSets

/-! The actual disjoint insertion and the exact support of its off-block
remainder. Its norm is bounded by the full c₀ norm, without summing norms. -/
noncomputable section
open Set Filter Topology
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  {L : ℕ → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
local instance ordinalOmegaInsertCoordinateGroup (i : ℕ) : NormedAddCommGroup C(L i, 𝕜) := inferInstance
local instance ordinalOmegaInsertCoordinateSpace (i : ℕ) : NormedSpace 𝕜 C(L i, 𝕜) := inferInstance
local instance ordinalOmegaInsertSumGroup : NormedAddCommGroup (OrdinalBlockFunctionSum 𝕜 L) := inferInstance
local instance ordinalOmegaInsertSumSpace : NormedSpace 𝕜 (OrdinalBlockFunctionSum 𝕜 L) := inferInstance

variable (H : ℕ → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
  (J : ∀ i, C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K)
  (hsupp : ∀ i f, Function.support (J i f) ⊆ H i)

theorem ordinalOmegaSynthesis_single (i : ℕ) (f : C(L i, 𝕜)) :
    wolfeDisjointSynthesis H hH J hsupp (JLMS.CZeroSum.single i f) = J i f := by
  classical
  change (∑' j, J j (JLMS.CZeroSum.single (𝕜 := 𝕜) (E := fun i => C(L i, 𝕜)) i f j)) = J i f
  rw [tsum_eq_single i]
  · rw [JLMS.CZeroSum.single_apply_self]
  · intro j hji
    rw [JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun i => C(L i, 𝕜)) i f hji, map_zero]

theorem ordinalOmegaSynthesis_support (f : OrdinalBlockFunctionSum 𝕜 L) :
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

theorem ordinalOmegaSynthesis_remainder_support (f : OrdinalBlockFunctionSum 𝕜 L) (i : ℕ) :
    Function.support (wolfeDisjointSynthesis H hH J hsupp f - J i (f i)) ⊆
      wolfeCrossUnion H i := by
  intro x hx
  by_cases hxi : x ∈ H i
  · exact False.elim (hx (by
      change wolfeDisjointSynthesis H hH J hsupp f x - J i (f i) x = 0
      rw [wolfeDisjointSynthesis_apply_mem H hH J hsupp f hxi, sub_self]))
  · have hi0 : J i (f i) x = 0 := by by_contra hn; exact hxi (hsupp i (f i) hn)
    have hn : wolfeDisjointSynthesis H hH J hsupp f x ≠ 0 := by
      intro hz
      exact hx (by change wolfeDisjointSynthesis H hH J hsupp f x - J i (f i) x = 0; rw [hz, hi0, sub_self])
    obtain ⟨j, hj⟩ := mem_iUnion.mp (ordinalOmegaSynthesis_support H hH J hsupp f hn)
    exact (mem_wolfeCrossUnion H i x).mpr ⟨j, fun he => hxi (he ▸ hj), hj⟩

theorem ordinalOmegaSynthesis_remainder_norm (f : OrdinalBlockFunctionSum 𝕜 L) (i : ℕ) :
    ‖wolfeDisjointSynthesis H hH J hsupp f - J i (f i)‖ ≤ ‖f‖ := by
  have he : wolfeDisjointSynthesis H hH J hsupp (f - JLMS.CZeroSum.single i (f i)) =
      wolfeDisjointSynthesis H hH J hsupp f - J i (f i) := by
    rw [map_sub, ordinalOmegaSynthesis_single H hH J hsupp]
  rw [← he, wolfeDisjointSynthesis_norm H hH J hsupp]
  apply JLMS.CZeroSum.norm_le (norm_nonneg f)
  intro j
  by_cases hji : j = i
  · subst j
    simp only [JLMS.CZeroSum.sub_apply, JLMS.CZeroSum.single_apply_self, sub_self, norm_zero]
    exact norm_nonneg f
  · simpa only [JLMS.CZeroSum.sub_apply, JLMS.CZeroSum.single_apply_ne (𝕜 := 𝕜) (E := fun i => C(L i, 𝕜)) i (f i) hji,
      sub_zero] using f.norm_apply_le_norm j

variable [T2Space K]

def ordinalOmegaBandInsertIsometry (i : ℕ) [CompactSpace (H i)]
    (hi : IsClopen (H i)) (p : C(H i, L i)) (q : C(L i, H i))
    (hq : Function.RightInverse q p) : C(L i, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K where
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

@[simp] theorem ordinalOmegaBandInsertIsometry_apply (i : ℕ) [CompactSpace (H i)]
    (hi : IsClopen (H i)) (p : C(H i, L i)) (q : C(L i, H i))
    (hq : Function.RightInverse q p) (f : C(L i, 𝕜)) :
    ordinalOmegaBandInsertIsometry (𝕜 := 𝕜) H i hi p q hq f = ordinalBandInsert (𝕜 := 𝕜) (H i) hi p f := rfl

end Posets



