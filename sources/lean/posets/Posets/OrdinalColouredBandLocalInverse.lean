import Posets.OrdinalBandCoordinateInverse
import Posets.ClopenBandSectionIsometry
import Posets.OrdinalClosedCopySeparatedAmbientCells
import Posets.OrdinalRegularOmegaAssemblyPrefix

/-! Uniform local coordinate inverses from actual coloured ordinal cores.
The insertion, reading section, and coordinate inverse are constructed;
no local preservation or factorization is supplied as a premise. -/
noncomputable section
namespace Posets
open Set Topology
open ThesisCommon
universe u v
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2400000

theorem ordinalSeparatedBand_coordinate_inverse_of_colour
    {θ γ upper lower b : Ordinal.{u}} {F : Set Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e)
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (a : ℕ → Iic γ) (ha : Monotone a) (n : ℕ) (c : Bool)
    {ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < 1 / 2)
    (G : OrdinalSeparatedBandCoreGeometry F θ upper lower b)
    (hlower : (a n).val = lower) (hupper : (a (n+1)).val = upper)
    (hF : F ⊆ Subtype.val '' closure (ordinalAmbientBandLeaves hθ e he M T S a n c ε)) :
    ∃ J : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K,
    ∃ q : C(JLMS.OrdinalInterval (Ordinal.omega0 ^ b), K),
    ∃ B : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b),
      B.comp (ordinalBandCompression (if c then T else S) J.toContinuousLinearMap q) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖B‖ ≤ 1 / (1 / 2 - 3 * ε) ∧
      (∀ f, Function.support (J f) ⊆ range e) ∧
      (∀ x, q x ∈ e '' ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' F)) := by
  classical
  let H := ordinalSeparatedBandAmbientSet G e
  have hH : IsClopen H := ordinalSeparatedBandAmbientSet_isClopen G e he
  have hcH : IsCompact H := ordinalSeparatedBandAmbientSet_isCompact G e he
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hcH
  let P := ordinalOmegaPrefixCoordinate G.model (ordinalSeparatedBandAmbientCoordinate G e he)
    (Ordinal.omega0 ^ b)
  let Q := ordinalOmegaPrefixSection G.model (ordinalSeparatedBandAmbientSection G e he) G.model_large
  have hPQ : Function.RightInverse Q P :=
    ordinalOmegaPrefix_section G.model _ _ (ordinalSeparatedBandAmbientSection_rightInverse G e he)
      G.model_large
  let J := clopenBandSectionIsometry (𝕜 := 𝕜) H hH P Q hPQ
  let q : C(JLMS.OrdinalInterval (Ordinal.omega0 ^ b), K) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(H, K)).comp Q
  let leaves := ordinalAmbientBandLeaves hθ e he M T S a n c ε
  let Z : Set K := e '' leaves ∩ H
  let V := ordinalAmbientCeilingCellAt e (a n).val
  have hHcell : H = e '' ordinalTowerCell θ (ordinalTowerLevel θ (a (n+1)).val)
      G.upperPoint.val := by
    change e '' ((Subtype.val : Iic θ → Ordinal.{u}) ⁻¹' G.H) = _
    rw [G.cell_eq, hupper]
    congr 1
    ext x
    change (x.val ≤ θ ∧ _) ↔ _
    exact and_iff_right x.property
  have hZimage : Z = e '' (leaves ∩ ordinalTowerCell θ
      (ordinalTowerLevel θ (a (n+1)).val) G.upperPoint.val) := by
    rw [show Z = e '' leaves ∩ H from rfl, hHcell]
    exact (image_inter he.injective).symm
  have hleaf (y : K) (hy : y ∈ Z) :
      ∃ hV : IsClopen (V y), ∃ hcV : IsCompact (V y), V y ⊆ H ∧
        wolfeMass M (wolfeOperatorRow (if c then T else S) y) (H \ V y) < ε ∧
        (1 / 2 : ℝ) ≤ ‖(if c then T else S) (JLMS.clopenIndicator (V y) hV hcV) y‖ := by
    have hy' := hZimage ▸ hy
    have hh := ordinalAmbientBandLeaf_image_estimates hθ e he M T S a ha n c ε
      G.upperPoint.val hy'
    simpa only [← hHcell] using hh
  choose hVo hVc hVs hVm hVd using hleaf
  have hqc (x : JLMS.OrdinalInterval (Ordinal.omega0 ^ b)) : q x ∈ closure Z :=
    ordinalSeparatedBandAmbientSection_leaf_closure G e he leaves hF
      (G.model (ordinalOmegaPrefixInclusion G.model_large x))
  have hread (f : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b)) (x) : J f (q x) = f x :=
    ordinalBandInsert_read H hH P Q hPQ f x
  have hJn : ‖J.toContinuousLinearMap‖ ≤ 1 := ordinalBandInsert_norm_le H hH P
  have hsupp (f : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b)) : Function.support (J f) ⊆ H :=
    ordinalBandInsert_support H hH P f
  have hconst (y : K) (hy : y ∈ Z) (f : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b))
      (z : K) (hz : z ∈ V y) : J f z = J f y := by
    have hz' : z ∈ ordinalAmbientCeilingCellAt e lower y := by
      simpa only [V, hlower] using hz
    have hp := ordinalSeparatedBandAmbientCoordinate_constant_on_ceilingCellAt G e he
      (⟨y, hy.2⟩ : H) (⟨z, hVs y hy hz⟩ : H) hz'
    exact ordinalBandInsert_constant_on_fiber H hH P f ⟨z, hVs y hy hz⟩ ⟨y, hy.2⟩
      (ordinalOmegaPrefixCoordinate_constant G.model _ _ hp.symm)
  obtain ⟨B, hB, hBn⟩ := ordinalBand_coordinate_inverse_from_leaf_mass M (if c then T else S)
    J.toContinuousLinearMap q H hH hcH hJn hsupp hqc hread V hVs hVo hVc hconst hε hgap
    hVd (fun y hy => (hVm y hy).le)
  refine ⟨J, q, B, hB, hBn, ?_, ?_⟩
  · intro f
    exact (hsupp f).trans (ordinalSeparatedBandAmbientSet_subset_range G e)
  · intro x
    exact ordinalSeparatedBandAmbientSection_core G e he
      (G.model (ordinalOmegaPrefixInclusion G.model_large x))

end Posets
