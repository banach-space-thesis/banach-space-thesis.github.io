import Posets.PFPOrdinalAnchorNormalization
import Posets.OrdinalTransfiniteRankUnits
import Posets.OrdinalPrincipalTransfiniteSource
import Posets.OrdinalInfiniteCrossMass
import Posets.OrdinalPaddedBandColours
import JLMS.OrdinalAtomicMatrix
import JLMS.OrdinalSpaceMultipleSum

/-! Operator-driven full-cardinality core selection at higher ranks of
uncountable cofinality. The source copies are actual disjoint open ordinal
blocks, and ceiling normalization removes the boundary term. No local
factorization or preservation assertion is assumed. -/

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

namespace OrdinalTransfiniteRankUnits
variable {Λ γ : Ordinal.{u}} {N : ℕ}
  (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)

def pfpPaddedSequence : OrdinalPrincipalTransfiniteSequence Λ (Ordinal.omega0 ^ γ) :=
  R.asSourceSequence (by omega) hγ

def pfpPaddedEmbedding (i : Iio Λ) :
    C(Iic (Ordinal.omega0 ^ (R.unit i * ((2*N+2 : ℕ) : Ordinal))),
      JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)) :=
  (R.pfpPaddedSequence hγ).sourceEmbedding i

theorem pfpPaddedEmbedding_isOpen (i : Iio Λ) : IsOpenEmbedding (R.pfpPaddedEmbedding hγ i) :=
  (R.pfpPaddedSequence hγ).sourceEmbedding_isOpen i

theorem pfpPaddedEmbedding_disjoint : Pairwise (fun i j =>
    Disjoint (range (R.pfpPaddedEmbedding hγ i)) (range (R.pfpPaddedEmbedding hγ j))) :=
  (R.pfpPaddedSequence hγ).sourceEmbedding_ranges_disjoint

def pfpNormalizedOperator
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) :=
  pfpOrdinalAnchorNormalize (R.pfpPaddedSequence hγ).blockMap
    (R.pfpPaddedSequence hγ).blockMap_strictMono (R.pfpPaddedSequence hγ).blockMap_endpoint T

def pfpNormalizedZeroOperator
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) :=
  JLMS.ordinalZeroOperator (Ordinal.omega0 ^ γ) (R.pfpNormalizedOperator hγ T)

theorem pfpNormalizedZeroOperator_budget
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) :
    ‖R.pfpNormalizedZeroOperator hγ T‖ +
      ‖ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T‖ ≤ 1 + 4 * ‖T‖ := by
  have hn : ‖R.pfpNormalizedZeroOperator hγ T‖ ≤ 2 * ‖T‖ := by
    change ‖JLMS.operatorConjugation _ (R.pfpNormalizedOperator hγ T)‖ ≤ _
    rw [JLMS.norm_operatorConjugation]
    exact norm_pfpOrdinalAnchorNormalize_le _ _ _ T
  have hs := norm_sub_le (ContinuousLinearMap.id 𝕜
    (JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))))
      (R.pfpNormalizedZeroOperator hγ T)
  have hi := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜)
    (E := JLMS.CZero 𝕜 (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ)))
  linarith

def pfpPaddedLevels (i : Iio Λ) := ordinalPaddedBandLevels (R.unit i) N

theorem pfpPaddedTop (i : Iio Λ) :
    Ordinal.omega0 ^ (R.unit i * ((2*N+2 : ℕ) : Ordinal)) ∈
      ordinalTowerLevel (Ordinal.omega0 ^ (R.unit i * ((2*N+2 : ℕ) : Ordinal)))
        (R.unit i * ((2*N+2 : ℕ) : Ordinal)) :=
  ordinalPaddedBand_top_level (R.unit i)
    (Ordinal.omega0_pos.trans_le (R.unit_infinite i)).ne' N

end OrdinalTransfiniteRankUnits

structure PFPOrdinalTransfinitePaddedCores {Λ γ : Ordinal.{u}} {N : ℕ}
    (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ))
    (ε δ : ℝ) where
  colour : Bool
  index : Iio Λ → Iio Λ
  injective : Function.Injective index
  band : Iio Λ → Fin N
  core : Iio Λ → Set (JLMS.OrdinalInterval (Ordinal.omega0 ^ γ))
  compact : ∀ i, IsCompact (core i)
  leaf_closure : ∀ i, core i ⊆ closure (R.pfpPaddedEmbedding hγ (index i) ''
    ordinalAmbientBandLeaves (R.pfpPaddedTop (index i))
      (R.pfpPaddedEmbedding hγ (index i)) (R.pfpPaddedEmbedding_isOpen hγ (index i))
      (JLMS.ordinalAtomicDualModel _) (R.pfpNormalizedZeroOperator hγ T)
      (ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T)
      (R.pfpPaddedLevels (index i)) (band i).val colour ε)
  block : ∀ i, core i ⊆ range (R.pfpPaddedEmbedding hγ (index i))
  rank : ∀ i, R.pfpPaddedEmbedding hγ (index i)
      ⟨Ordinal.omega0 ^ (R.unit (index i) * ((2*N+2 : ℕ) : Ordinal)),
        show Ordinal.omega0 ^ (R.unit (index i) * ((2*N+2 : ℕ) : Ordinal)) ≤
          Ordinal.omega0 ^ (R.unit (index i) * ((2*N+2 : ℕ) : Ordinal)) from le_rfl⟩ ∈
    ordinalDerived (core i) (R.unit (index i) * ((2*N+2 : ℕ) : Ordinal))
  cross : ∀ i x, x ∈ core i →
    wolfeMass (JLMS.ordinalAtomicDualModel _) (wolfeOperatorRow
      (if colour then R.pfpNormalizedZeroOperator hγ T
       else ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T) x)
      (wolfeIndexedCrossUnion (fun j => range (R.pfpPaddedEmbedding hγ (index j))) i) < δ

theorem exists_pfpOrdinalTransfinitePaddedCores {Λ γ : Ordinal.{u}} {N : ℕ}
    (R : OrdinalTransfiniteRankUnits Λ γ (2*N+2)) (hγ : IsSuccLimit γ)
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ))
    {ε δ : ℝ} (hN : 1 + 4 * ‖T‖ < N * ε) (hδ : 0 < δ) :
    Nonempty (PFPOrdinalTransfinitePaddedCores R hγ T ε δ) := by
  letI : Infinite (Iio Λ) := JLMS.ordinalIioInfinite Λ R.infinite
  let ρ : Iio Λ → Ordinal.{u} := fun i => R.unit i * ((2*N+2 : ℕ) : Ordinal)
  let θ : Iio Λ → Ordinal.{u} := fun i => Ordinal.omega0 ^ ρ i
  let x : ∀ i, Iic (θ i) := fun i => ⟨θ i, show θ i ≤ θ i from le_rfl⟩
  have hx (i : Iio Λ) : x i ∈ ordinalDerived (univ : Set (Iic (θ i))) (ρ i) := by
    have ht := R.pfpPaddedTop i
    change θ i ∈ ordinalDerived (Iic (θ i)) (ρ i) at ht
    have he := ordinalDerived_image_closedEmbedding
      (isClosed_Iic : IsClosed (Iic (θ i))).isClosedEmbedding_subtypeVal univ (ρ i)
    rw [image_univ, Subtype.range_coe] at he
    rw [he] at ht
    obtain ⟨y, hy, hyx⟩ := ht
    exact (show y = x i from Subtype.ext hyx) ▸ hy
  obtain ⟨c, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_infinite_crossMass (JLMS.ordinalAtomicDualModel _)
      (JLMS.scattered_ordinalInterval _) (R.pfpNormalizedZeroOperator hγ T)
      (ContinuousLinearMap.id 𝕜 _ - R.pfpNormalizedZeroOperator hγ T)
      (by abel) θ ρ R.pfpPaddedTop (fun i => R.pfpPaddedEmbedding hγ i)
      (R.pfpPaddedEmbedding_isOpen hγ) (R.pfpPaddedEmbedding_disjoint hγ)
      R.pfpPaddedLevels (fun i => ordinalPaddedBandLevels_monotone (R.unit i) N)
      ((R.pfpNormalizedZeroOperator_budget hγ T).trans_lt hN) hδ ρ x hx
  exact ⟨⟨c, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩⟩

theorem exists_pfpOrdinalTransfinitePaddedSelection
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ)
    (T : JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ) →L[𝕜] JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ γ)) :
    ∃ N : ℕ, ∃ R : OrdinalTransfiniteRankUnits γ.cof.ord γ (2*N+2),
      Nonempty (PFPOrdinalTransfinitePaddedCores R (Ordinal.aleph0_le_cof.mp hc.le) T
        (1 / 100) (1 / 100)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + 4 * ‖T‖) / (1 / 100 : ℝ))
  have hN' : 1 + 4 * ‖T‖ < N * (1 / 100 : ℝ) :=
    (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)).mp hN
  obtain ⟨R⟩ := exists_ordinalPrincipalTransfiniteRankUnits γ hP hc hgap (2*N+2) (by omega)
  exact ⟨N, R, exists_pfpOrdinalTransfinitePaddedCores R _ T hN' (by norm_num)⟩

end Posets
