import Posets.OrdinalTransfiniteRankUnits
import Posets.OrdinalPrincipalTransfiniteSource
import Posets.OrdinalInfiniteCrossMass
import Posets.OrdinalCeilingOperatorCorrection
import Posets.OrdinalPaddedBandColours
import Posets.OrdinalColouredBandLocalInverse
import JLMS.OrdinalAtomicMatrix
import JLMS.OrdinalSpaceMultipleSum
import Posets.OrdinalRegularOmegaBandParameters

/-! Concrete operator selection on genuine transfinite sources.
All cores, band geometries and local inverses are constructed from an actual
splitting.  The finite colour count is chosen before its source boundary map. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
open ThesisCommon
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1800000
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

namespace OrdinalTransfiniteRankUnits
variable {Λ γ : Ordinal.{u}} {N : ℕ}
  (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)

abbrev paddedSequence : OrdinalPrincipalTransfiniteSequence Λ (Ordinal.omega0 ^ γ) :=
  R.asSourceSequence (by omega) hγ

def sourceRank (i : Iio Λ) : Ordinal.{u} := R.unit i * ((2*N+2 : ℕ) : Ordinal)

theorem sourceTopLevel (i : Iio Λ) :
    (R.paddedSequence hγ).endpoint i ∈ ordinalTowerLevel
      ((R.paddedSequence hγ).endpoint i) (R.sourceRank i) :=
  ordinalPaddedBand_top_level (R.unit i)
    (Ordinal.omega0_pos.trans_le (R.unit_infinite i)).ne' N

def bandLevels (i : Iio Λ) : ℕ → Iic (R.sourceRank i) :=
  ordinalPaddedBandLevels (R.unit i) N

theorem bandLevels_monotone (i : Iio Λ) : Monotone (R.bandLevels i) :=
  ordinalPaddedBandLevels_monotone (R.unit i) N

end OrdinalTransfiniteRankUnits

variable {𝕜 : Type*} [RCLike 𝕜] {Λ γ : Ordinal.{u}} {N : ℕ}

structure OrdinalTransfiniteColouredCores
    (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)
    (M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)))
    (T S : JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) →L[𝕜]
      JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))) (ε δ : ℝ) where
  colour : Bool
  index : Iio Λ → Iio Λ
  injective : Function.Injective index
  band : Iio Λ → Fin N
  core : Iio Λ → Set (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))
  compact : ∀ i, IsCompact (core i)
  leaf_closure : ∀ i, core i ⊆ closure ((R.paddedSequence hγ).sourceEmbedding (index i) ''
    ordinalAmbientBandLeaves (R.sourceTopLevel hγ (index i))
      ((R.paddedSequence hγ).sourceEmbedding (index i))
      ((R.paddedSequence hγ).sourceEmbedding_isOpen (index i)) M T S
      (R.bandLevels (index i)) (band i).val colour ε)
  block : ∀ i, core i ⊆ range ((R.paddedSequence hγ).sourceEmbedding (index i))
  rank : ∀ i, (R.paddedSequence hγ).sourceEmbedding (index i)
      ⟨(R.paddedSequence hγ).endpoint (index i),
        le_refl ((R.paddedSequence hγ).endpoint (index i))⟩ ∈
    ordinalDerived (core i) (R.sourceRank (index i))
  cross : ∀ i x, x ∈ core i → wolfeMass M (wolfeOperatorRow (if colour then T else S) x)
    (wolfeIndexedCrossUnion (fun j => range ((R.paddedSequence hγ).sourceEmbedding (index j))) i) < δ

theorem exists_ordinalTransfiniteColouredCores
    (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)
    (M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)))
    (T S : JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) →L[𝕜]
      JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) {ε δ : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ) :
    Nonempty (OrdinalTransfiniteColouredCores R hγ M T S ε δ) := by
  letI : Infinite (Iio Λ) := JLMS.ordinalIioInfinite Λ R.infinite
  let P := R.paddedSequence hγ
  obtain ⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_infinite_crossMass M (JLMS.scattered_ordinalInterval _) T S hTS
      P.endpoint R.sourceRank (R.sourceTopLevel hγ) (fun i => P.sourceEmbedding i) P.sourceEmbedding_isOpen
      P.sourceEmbedding_ranges_disjoint R.bandLevels R.bandLevels_monotone hN hδ R.sourceRank
      (fun i => ⟨P.endpoint i, le_refl (P.endpoint i)⟩)
      (fun i => ordinalTower_top_mem_subtypeDerived (R.sourceTopLevel hγ i))
  exact ⟨⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩⟩

namespace OrdinalTransfiniteColouredCores
variable {R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)} {hγ : IsSuccLimit γ}
  {M : JLMS.AtomicDualModel 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))} {ε δ : ℝ}
  (F : OrdinalTransfiniteColouredCores R hγ M T S ε δ)

def sourceCore (i : Iio Λ) : Set (Iic ((R.paddedSequence hγ).endpoint (F.index i))) :=
  (R.paddedSequence hγ).sourceEmbedding (F.index i) ⁻¹' F.core i

def ordinalCore (i : Iio Λ) : Set Ordinal.{u} := Subtype.val '' F.sourceCore i

theorem sourceCore_compact (i : Iio Λ) : IsCompact (F.sourceCore i) :=
  ordinalAmbientCore_preimage_compact _ ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i))
    _ (F.compact i)

theorem sourceCore_leaf_closure (i : Iio Λ) : F.sourceCore i ⊆ closure
    (ordinalAmbientBandLeaves (R.sourceTopLevel hγ (F.index i))
      ((R.paddedSequence hγ).sourceEmbedding (F.index i))
      ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i)) M T S
      (R.bandLevels (F.index i)) (F.band i).val F.colour ε) := by
  intro x hx
  have h := F.leaf_closure i hx
  rw [ordinalAmbientCore_closure_image _
    ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i))] at h
  exact ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i)).injective.mem_set_image.mp h

theorem sourceCore_rank (i : Iio Λ) :
    (⟨(R.paddedSequence hγ).endpoint (F.index i),
      le_refl ((R.paddedSequence hγ).endpoint (F.index i))⟩ :
      Iic ((R.paddedSequence hγ).endpoint (F.index i))) ∈
      ordinalDerived (F.sourceCore i) (R.sourceRank (F.index i)) :=
  (ordinalAmbientCore_rank_preimage_iff _ ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i))
    _ (F.block i) _ _).mpr (F.rank i)

theorem ordinalCore_compact (i : Iio Λ) : IsCompact (F.ordinalCore i) :=
  (F.sourceCore_compact i).image continuous_subtype_val

theorem ordinalCore_subset (i : Iio Λ) :
    F.ordinalCore i ⊆ Iic ((R.paddedSequence hγ).endpoint (F.index i)) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem ordinalCore_rank (i : Iio Λ) :
    (R.paddedSequence hγ).endpoint (F.index i) ∈
      ordinalDerived (F.ordinalCore i) (R.sourceRank (F.index i)) := by
  rw [ordinalCore, ordinalDerived_image_closedEmbedding isClosed_Iic.isClosedEmbedding_subtypeVal]
  exact mem_image_of_mem Subtype.val (F.sourceCore_rank i)

theorem ordinalCore_leaf_closure (i : Iio Λ) : F.ordinalCore i ⊆ Subtype.val '' closure
    (ordinalAmbientBandLeaves (R.sourceTopLevel hγ (F.index i))
      ((R.paddedSequence hγ).sourceEmbedding (F.index i))
      ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i)) M T S
      (R.bandLevels (F.index i)) (F.band i).val F.colour ε) :=
  image_mono (F.sourceCore_leaf_closure i)

theorem bandGeometry (i : Iio Λ) : Nonempty (OrdinalSeparatedBandCoreGeometry (F.ordinalCore i)
    ((R.paddedSequence hγ).endpoint (F.index i))
    (R.unit (F.index i) * ((2*(F.band i).val+2 : ℕ) : Ordinal))
    (R.unit (F.index i) * ((2*(F.band i).val : ℕ) : Ordinal)) (R.unit (F.index i))) :=
  ordinal_finite_band_exists_geometry _
    (Ordinal.omega0_pos.trans_le (R.unit_infinite (F.index i))).ne'
    (Ordinal.one_add_of_omega0_le (R.unit_infinite (F.index i))) N (F.band i).val (F.band i).isLt.le
    (F.ordinalCore i) (F.ordinalCore_compact i) (F.ordinalCore_subset i) ⟨_, F.ordinalCore_rank i⟩

theorem localInverse {ε : ℝ}
    (F : OrdinalTransfiniteColouredCores R hγ M T S ε δ)
    (hε : 0 ≤ ε) (hgap : 3*ε < 1/2) (i : Iio Λ) :
    ∃ J : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)) →ₗᵢ[𝕜]
        JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
    ∃ q : C(JLMS.OrdinalInterval (Ordinal.omega0 ^ R.unit (F.index i)),
        JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)),
    ∃ B : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)) →L[𝕜]
        JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ R.unit (F.index i)),
      B.comp (ordinalBandCompression (if F.colour then T else S) J.toContinuousLinearMap q) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖B‖ ≤ 1/(1/2-3*ε) ∧
      (∀ f, Function.support (J f) ⊆ range ((R.paddedSequence hγ).sourceEmbedding (F.index i))) ∧
      (∀ x, q x ∈ F.core i) := by
  obtain ⟨G⟩ := F.bandGeometry i
  have hl : (R.bandLevels (F.index i) (F.band i).val).val =
      R.unit (F.index i) * ((2*(F.band i).val : ℕ) : Ordinal) :=
    ordinalPaddedBandLevels_apply _ N _ (by have := (F.band i).isLt; omega)
  have hu : (R.bandLevels (F.index i) ((F.band i).val+1)).val =
      R.unit (F.index i) * ((2*(F.band i).val+2 : ℕ) : Ordinal) := by
    rw [OrdinalTransfiniteRankUnits.bandLevels,
      ordinalPaddedBandLevels_apply _ N _ (by have := (F.band i).isLt; omega)]
    congr 1
  obtain ⟨J, q, B, hB, hBn, hJ, hq⟩ := ordinalSeparatedBand_coordinate_inverse_of_colour
    (R.sourceTopLevel hγ (F.index i)) ((R.paddedSequence hγ).sourceEmbedding (F.index i))
    ((R.paddedSequence hγ).sourceEmbedding_isOpen (F.index i)) M T S
    (R.bandLevels (F.index i)) (R.bandLevels_monotone (F.index i)) (F.band i).val F.colour
    hε hgap G hl hu (F.ordinalCore_leaf_closure i)
  refine ⟨J, q, B, hB, hBn, hJ, ?_⟩
  intro x
  obtain ⟨z, hz, hzq⟩ := hq x
  obtain ⟨w, hw, hwz⟩ := hz
  have he : w = z := Subtype.ext hwz
  subst w
  exact hzq ▸ hw

end OrdinalTransfiniteColouredCores

theorem exists_ordinalTransfiniteCorrectedColouredCores
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ)
    (T S : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (N : ℕ) (R : OrdinalTransfiniteRankUnits γ.cof.ord γ (2*N+2)),
      let hγ := Ordinal.aleph0_le_cof.mp hc.le
      let P := R.paddedSequence hγ
      let T₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
        (ordinalCeilingCorrectedLeft P.blockMap P.blockMap_strictMono P.blockMap_endpoint T)
      let S₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
        (ordinalCeilingCorrectedRight P.blockMap P.blockMap_strictMono P.blockMap_endpoint S)
      ‖T₀‖ + ‖S₀‖ < N*ε ∧ Nonempty (OrdinalTransfiniteColouredCores R hγ
        (JLMS.ordinalAtomicDualModel (Ordinal.omega0 ^ γ)) T₀ S₀ ε δ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2*‖T‖+1+2*‖S‖)/ε)
  have hN' : 2*‖T‖+1+2*‖S‖ < (N : ℝ)*ε := (div_lt_iff₀ hε).mp hN
  obtain ⟨R⟩ := exists_ordinalPrincipalTransfiniteRankUnits γ hP hc hgap (2*N+2) (by omega)
  refine ⟨N, R, ?_⟩
  let hγ := Ordinal.aleph0_le_cof.mp hc.le
  let P := R.paddedSequence hγ
  let T₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
    (ordinalCeilingCorrectedLeft P.blockMap P.blockMap_strictMono P.blockMap_endpoint T)
  let S₀ := JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ)
    (ordinalCeilingCorrectedRight P.blockMap P.blockMap_strictMono P.blockMap_endpoint S)
  have hTn : ‖T₀‖ ≤ 2*‖T‖+1 := by
    simpa only [T₀, JLMS.ordinalZeroOperator, JLMS.norm_operatorConjugation] using
      ordinalCeilingCorrectedLeft_norm_le P.blockMap P.blockMap_strictMono P.blockMap_endpoint T
  have hSn : ‖S₀‖ ≤ 2*‖S‖ := by
    simpa only [S₀, JLMS.ordinalZeroOperator, JLMS.norm_operatorConjugation] using
      ordinalCeilingCorrectedRight_norm_le P.blockMap P.blockMap_strictMono P.blockMap_endpoint S
  have hn : ‖T₀‖+‖S₀‖ < N*ε := by linarith
  have hsum : T₀+S₀ = ContinuousLinearMap.id 𝕜 _ := by
    dsimp only [T₀, S₀, JLMS.ordinalZeroOperator]
    rw [← map_add, ordinalCeiling_corrected_sum _ _ _ T S hTS]
    ext f x
    simpa only [JLMS.operatorConjugation_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun v => v x)
        ((JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) (Ordinal.omega0 ^ γ)).apply_symm_apply f)
  exact ⟨hn, exists_ordinalTransfiniteColouredCores R hγ
    (JLMS.ordinalAtomicDualModel _) T₀ S₀ hsum hn hδ⟩

end Posets

