import Posets.OrdinalIdealTransportSmallDomain
import Posets.OrdinalIdealTransportSmallCodomain
import Posets.OrdinalIdealTransportCofinalMaps

/-! Uniform head-image and early-row cutoffs for ordinal operator matrices.
These are the two different bounds needed by the triangular index argument. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance cornerCutoffFunctionGroup (α : Ordinal.{0}) : NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance cornerCutoffFunctionSpace (α : Ordinal.{0}) : NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance

def ordinalHeadInclusion (β κ : Ordinal.{0}) : OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 κ :=
  (ordinalHeadProjection κ β).comp (ordinalInitialSegmentExtend β κ)

theorem ordinalHeadInclusion_read (β κ : Ordinal.{0}) (hβ : β ≤ κ)
    (f : OrdinalC 𝕜 κ) :
    ordinalHeadInclusion β κ (ordinalInitialSegmentRead β κ hβ f) = ordinalHeadProjection κ β f := by
  ext x
  change ordinalHeadProjection κ β _ x = _
  simp only [ordinalHeadProjection_apply]
  split_ifs with hx
  · change f ⟨min x.val β, _⟩ = f x
    congr 1
    exact Subtype.ext (min_eq_left hx)
  · rfl

theorem exists_ordinalOperator_head_image_tail {κ β : Ordinal.{0}}
    (hκ : Cardinal.aleph0 < κ.cof) (hβ : β.card < κ.cof) (hβκ : β ≤ κ)
    (T : OrdinalC 𝕜 κ →L[𝕜] OrdinalC 𝕜 κ) :
    ∃ δ < κ, ∀ f, T (ordinalHeadProjection κ β f) ∈ ordinalTailSpace κ δ := by
  obtain ⟨δ, hδ, ht⟩ := exists_smallDomain_operator_tail hκ hβ (T.comp (ordinalHeadInclusion β κ))
  refine ⟨δ, hδ, ?_⟩
  intro f
  have h := ht (ordinalInitialSegmentRead β κ hβκ f)
  change T (ordinalHeadInclusion β κ (ordinalInitialSegmentRead β κ hβκ f)) ∈ _ at h
  rwa [ordinalHeadInclusion_read] at h

theorem exists_ordinalOperator_early_rows_cutoff {κ η : Ordinal.{0}}
    (hκ : Cardinal.aleph0 < κ.cof) (hη : η.card < κ.cof) (hηκ : η ≤ κ)
    (T : OrdinalC 𝕜 κ →L[𝕜] OrdinalC 𝕜 κ) :
    ∃ τ < κ, ∀ f, (∀ y : OrdinalInterval κ, y.val ≤ τ → f y = 0) →
      f ⟨κ, Ordinal.zero_le _, le_rfl⟩ = 0 →
      ∀ x : OrdinalInterval κ, x.val ≤ η → T f x = 0 := by
  obtain ⟨τ, hτ, hkill⟩ := exists_smallCodomain_operator_annihilating_tail hκ hη
    ((ordinalInitialSegmentRead η κ hηκ).comp T)
  refine ⟨τ, hτ, ?_⟩
  intro f hf htop x hx
  have h := congrArg (fun z : OrdinalC 𝕜 η => z ⟨x.val, x.property.1, hx⟩)
    (hkill f hf htop)
  exact h

end Posets
