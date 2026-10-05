import Posets.OrdinalAmbientCoreBands
import ThesisCommon.Analysis.OrdinalBakerDerived

/-! Compact colour cores and their actual Cantor--Bendixson ranks commute
with the embedding of the ordinal block into the global locally compact space. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
variable {θ γ : Ordinal.{u}}

theorem ordinalAmbientCore_closedEmbedding (e : Iic θ → K) (he : IsOpenEmbedding e) :
    IsClosedEmbedding e := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact θ)
  exact he.continuous.isClosedEmbedding he.injective

theorem ordinalAmbientCore_closure_image (e : Iic θ → K) (he : IsOpenEmbedding e)
    (L : Set (Iic θ)) : closure (e '' L) = e '' closure L :=
  (ordinalAmbientCore_closedEmbedding e he).closure_image_eq L

theorem ordinalAmbientCore_closure_compact (e : Iic θ → K) (he : IsOpenEmbedding e)
    (L : Set (Iic θ)) : IsCompact (closure (e '' L)) := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact θ)
  rw [ordinalAmbientCore_closure_image e he]
  exact isClosed_closure.isCompact.image he.continuous

theorem ordinalAmbientCore_closure_subset_range (e : Iic θ → K) (he : IsOpenEmbedding e)
    (L : Set (Iic θ)) : closure (e '' L) ⊆ range e := by
  rw [ordinalAmbientCore_closure_image e he]
  exact image_subset_range _ _

theorem ordinalAmbientCore_rank_image_iff (e : Iic θ → K) (he : IsOpenEmbedding e)
    (C : Set (Iic θ)) (ρ : Ordinal.{v}) (x : Iic θ) :
    e x ∈ ordinalDerived (e '' C) ρ ↔ x ∈ ordinalDerived C ρ := by
  rw [ordinalDerived_image_closedEmbedding (ordinalAmbientCore_closedEmbedding e he)]
  exact he.injective.mem_set_image

theorem ordinalAmbientCore_rank_closure_iff (e : Iic θ → K) (he : IsOpenEmbedding e)
    (L : Set (Iic θ)) (ρ : Ordinal.{v}) (x : Iic θ) :
    e x ∈ ordinalDerived (closure (e '' L)) ρ ↔ x ∈ ordinalDerived (closure L) ρ := by
  rw [ordinalAmbientCore_closure_image e he]
  exact ordinalAmbientCore_rank_image_iff e he (closure L) ρ x

/-- This reverse transport applies to the compact subcores produced by the
global cross-mass descent; it does not assume that they are whole colour cores. -/
theorem ordinalAmbientCore_rank_preimage_iff (e : Iic θ → K) (he : IsOpenEmbedding e)
    (C : Set K) (hC : C ⊆ range e) (ρ : Ordinal.{v}) (x : Iic θ) :
    x ∈ ordinalDerived (e ⁻¹' C) ρ ↔ e x ∈ ordinalDerived C ρ := by
  have hi : e '' (e ⁻¹' C) = C := image_preimage_eq_of_subset hC
  have hh := ordinalAmbientCore_rank_image_iff e he (e ⁻¹' C) ρ x
  rw [hi] at hh
  exact hh.symm

theorem ordinalAmbientCore_preimage_compact (e : Iic θ → K) (he : IsOpenEmbedding e)
    (C : Set K) (hC : IsCompact C) : IsCompact (e ⁻¹' C) := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact θ)
  exact (hC.isClosed.preimage he.continuous).isCompact

/-- One finite band colour retains the prescribed rank in the ambient space,
and its closed core is compact and entirely inside the original open block. -/
theorem ordinalAmbientCore_exists_coloured_image (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (ρ : Ordinal.{v}) {x : Iic θ}
    (hx : x ∈ ordinalDerived (univ : Set (Iic θ)) ρ) :
    ∃ i : Fin N × Bool,
      let L := ordinalAmbientBandLeaves hθ e he M T S a i.1.val i.2 ε
      IsCompact (closure (e '' L)) ∧ closure (e '' L) ⊆ range e ∧
        e x ∈ ordinalDerived (closure (e '' L)) ρ := by
  obtain ⟨i, hi⟩ := ordinalAmbientCore_exists_coloured_band hθ e he M T S hTS a ha hN ρ hx
  exact ⟨i, ordinalAmbientCore_closure_compact e he _,
    ordinalAmbientCore_closure_subset_range e he _,
    (ordinalAmbientCore_rank_closure_iff e he _ ρ x).mpr hi⟩

end Posets
