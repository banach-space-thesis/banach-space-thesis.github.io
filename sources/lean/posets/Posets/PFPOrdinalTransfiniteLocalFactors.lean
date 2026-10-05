import Posets.PFPOrdinalTransfinitePaddedSelection
import Posets.OrdinalColouredBandLocalInverse

/-! Uniform local reciprocal/Neumann factors extracted from the selected
transfinite cores. All maps and inverses are conclusions of the actual
rank and leaf-mass construction. The reading points stay in their cores. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
open ThesisCommon
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

theorem exists_local_factors (i : Iio Λ) :
    ∃ J : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)) →ₗᵢ[𝕜]
        JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
    ∃ q : C(JLMS.OrdinalInterval (Ordinal.omega0 ^ R.unit (F.index i)),
        JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
    ∃ B : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)) →L[𝕜]
        JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)),
      B.comp (ordinalBandCompression
        (if F.colour then R.pfpNormalizedZeroOperator hγ T
         else ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T)
        J.toContinuousLinearMap q) = ContinuousLinearMap.id 𝕜 _ ∧
      ‖B‖ ≤ 100 / 47 ∧
      (∀ f, Function.support (J f) ⊆ range (R.pfpPaddedEmbedding hγ (F.index i))) ∧
      ∀ x, q x ∈ F.core i := by
  classical
  let b := R.unit (F.index i)
  let ρ := b * ((2*N+2 : ℕ) : Ordinal)
  let θ := Ordinal.omega0 ^ ρ
  let e : Iic θ → JLMS.OrdinalInterval (Ordinal.omega0 ^ γ) :=
    R.pfpPaddedEmbedding hγ (F.index i)
  have he : IsOpenEmbedding e := R.pfpPaddedEmbedding_isOpen hγ (F.index i)
  let A : Set Ordinal.{u} := Subtype.val '' (e ⁻¹' F.core i)
  have hAc : IsCompact A :=
    (ordinalAmbientCore_preimage_compact e he (F.core i) (F.compact i)).image continuous_subtype_val
  have hAθ : A ⊆ Iic θ := by
    rintro y ⟨v, _, rfl⟩
    exact v.property
  have hAr : (ordinalDerived A ρ).Nonempty := by
    have hr := (ordinalAmbientCore_rank_preimage_iff e he (F.core i) (F.block i) ρ
      ⟨θ, show θ ≤ θ from le_rfl⟩).mpr (F.rank i)
    rw [show A = Subtype.val '' (e ⁻¹' F.core i) from rfl,
      ordinalDerived_image_closedEmbedding
        (isClosed_Iic : IsClosed (Iic θ)).isClosedEmbedding_subtypeVal]
    exact ⟨_, mem_image_of_mem _ hr⟩
  have hb : b ≠ 0 := (Ordinal.omega0_pos.trans_le (R.unit_infinite (F.index i))).ne'
  have habs : 1 + b = b := Ordinal.one_add_of_omega0_le (R.unit_infinite (F.index i))
  let G := Classical.choice (ordinal_finite_band_exists_geometry b hb habs N
    (F.band i).val (F.band i).isLt.le A hAc hAθ hAr)
  have hA : A ⊆ Subtype.val '' closure (ordinalAmbientBandLeaves
      (R.pfpPaddedTop (F.index i)) e he (JLMS.ordinalAtomicDualModel _)
      (R.pfpNormalizedZeroOperator hγ T)
      (ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T)
      (R.pfpPaddedLevels (F.index i)) (F.band i).val F.colour (1 / 100)) := by
    rintro y ⟨v, hv, rfl⟩
    refine ⟨v, ?_, rfl⟩
    have hc := F.leaf_closure i hv
    rw [ordinalAmbientCore_closure_image e he] at hc
    exact he.injective.mem_set_image.mp hc
  obtain ⟨J, q, B, hB, hBn, hJs, hq⟩ := ordinalSeparatedBand_coordinate_inverse_of_colour
    (R.pfpPaddedTop (F.index i)) e he (JLMS.ordinalAtomicDualModel _)
    (R.pfpNormalizedZeroOperator hγ T)
    (ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T)
    (R.pfpPaddedLevels (F.index i)) (ordinalPaddedBandLevels_monotone b N)
    (F.band i).val F.colour (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : 3 * (1 / 100 : ℝ) < 1 / 2) G
    (ordinalPaddedBandLevels_apply b N (F.band i).val (by omega))
    (by
      change (ordinalPaddedBandLevels b N ((F.band i).val + 1)).val = _
      rw [ordinalPaddedBandLevels_apply b N ((F.band i).val+1) (by omega)]
      congr 2) hA
  refine ⟨J, q, B, hB, ?_, hJs, ?_⟩
  · norm_num at hBn ⊢
    exact hBn
  · intro x
    obtain ⟨v, hv, hvq⟩ := hq x
    obtain ⟨w, hw, hwv⟩ := hv
    have hwv' : w = v := Subtype.ext hwv
    exact hvq ▸ (hwv' ▸ hw)

end PFPOrdinalTransfinitePaddedCores
end Posets
