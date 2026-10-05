import Posets.OrdinalBandInsertion
import Posets.ConvergentBandReadback

/-! Continuous sections turn the actual clopen-band pullbacks into
isometries, and their centered global readback is a genuine retraction. -/
noncomputable section
namespace Posets
open Set Filter Topology
variable {𝕜 K I : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def clopenBandSectionIsometry
    {L : Type*} [TopologicalSpace L] [CompactSpace L]
    (H : Set K) [CompactSpace H] (hH : IsClopen H) (p : C(H, L))
    (q : C(L, H)) (hq : Function.RightInverse q p) : C(L, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K where
  toLinearMap := (ordinalBandInsert H hH p).toLinearMap
  norm_map' f := by
    apply le_antisymm
    · exact ((ordinalBandInsert (𝕜 := 𝕜) H hH p).le_opNorm f).trans
        ((mul_le_mul_of_nonneg_right (ordinalBandInsert_norm_le H hH p) (norm_nonneg f)).trans_eq
          (one_mul _))
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      rw [← ordinalBandInsert_read H hH p q hq f x]
      exact JLMS.norm_CZero_apply_le _ _

@[simp] theorem clopenBandSectionIsometry_apply
    {L : Type*} [TopologicalSpace L] [CompactSpace L]
    (H : Set K) [CompactSpace H] (hH : IsClopen H) (p : C(H, L))
    (q : C(L, H)) (hq : Function.RightInverse q p) (f : C(L, 𝕜)) :
    clopenBandSectionIsometry (𝕜 := 𝕜) H hH p q hq f = ordinalBandInsert H hH p f := rfl

theorem convergent_clopen_band_retraction
    {L : I → Type*} [∀ i, TopologicalSpace (L i)] [∀ i, CompactSpace (L i)]
    (H : I → Set K) [∀ i, CompactSpace (H i)]
    (hH : ∀ i, IsClopen (H i)) (hd : Pairwise (fun i j => Disjoint (H i) (H j)))
    (p : ∀ i, C(H i, L i)) (q : ∀ i, C(L i, H i))
    (hr : ∀ i, Function.RightInverse (q i) (p i)) (z : K)
    (hz : ∀ i, z ∉ H i)
    (hc : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, ∀ x, (q i x).val ∈ U) :
    ∃ J : JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K,
    ∃ Q : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(L i, 𝕜)),
      ‖Q‖ ≤ 2 ∧ Q.comp J.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ := by
  let J := fun i => clopenBandSectionIsometry (𝕜 := 𝕜) (H i) (hH i) (p i) (q i) (hr i)
  have hs : ∀ i f, Function.support (J i f) ⊆ H i :=
    fun i f => ordinalBandInsert_support (H i) (hH i) (p i) f
  let r : ∀ i, C(L i, K) := fun i =>
    (⟨Subtype.val, continuous_subtype_val⟩ : C(H i, K)).comp (q i)
  refine ⟨wolfeDisjointSumIsometry H hd J hs, convergentBandReadback r z hc,
    norm_convergentBandReadback_le r z hc, ?_⟩
  apply convergentBandReadback_comp_synthesis r z hc H hd J hs
    (fun i x => (q i x).property) hz
  intro i f x
  exact ordinalBandInsert_read (H i) (hH i) (p i) (q i) (hr i) f x

end Posets
