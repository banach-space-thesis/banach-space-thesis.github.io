import Posets.OrdinalVariableUnitOuterBlocks
import Posets.OrdinalAmbientCoreBandsSequence

/-! Complementary operators on the actual global half-open power space
yield cofinally large coloured compact cores in the varying-unit blocks. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

local instance variableUnitCoresWeakOrdinal : WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩

local instance variableUnitCoresLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace

namespace OrdinalVariableUnitParameters
variable {γ : Ordinal.{u}} {N : ℕ} (P : OrdinalVariableUnitParameters γ N)

def bandLevels (n : ℕ) : ℕ → Iic (P.sourceRank n) :=
  ordinalRankUnitOmegaBandLevels (P.sourceUnit n) N 2

theorem bandLevels_monotone (n : ℕ) : Monotone (P.bandLevels n) :=
  ordinalRankUnitOmegaBandLevels_monotone (P.sourceUnit n) N 2

theorem bandLevels_apply_le (n k : ℕ) (hk : k ≤ N) :
    (P.bandLevels n k).val = P.sourceUnit n * ((k*2 : ℕ) : Ordinal) :=
  ordinalRankUnitOmegaBandLevels_apply_le (P.sourceUnit n) N 2 k hk

theorem bandLevels_gap (n k : ℕ) (hk : k < N) :
    (P.bandLevels n k).val + P.sourceUnit n * 2 = (P.bandLevels n (k+1)).val :=
  ordinalRankUnitOmegaBandLevels_gap (P.sourceUnit n) N 2 k hk

end OrdinalVariableUnitParameters

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ}

structure OrdinalVariableUnitColouredCores
    (P : OrdinalVariableUnitParameters γ N)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ)))
    (T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))) (ε δ : ℝ) where
  colour : Bool
  index : ℕ → ℕ
  strictMono : StrictMono index
  band : ℕ → Fin N
  core : ℕ → Set (Iio (Ordinal.omega0 ^ γ))
  compact : ∀ i, IsCompact (core i)
  leaf_closure : ∀ i, core i ⊆ closure (P.embedding (index i) ''
    ordinalAmbientBandLeaves (P.source_top_level (index i))
      (P.embedding (index i)) (P.embedding_isOpen (index i)) M T S
      (P.bandLevels (index i)) (band i).val colour ε)
  block : ∀ i, core i ⊆ range (P.embedding (index i))
  rank : ∀ i, P.embedding (index i)
      ⟨P.source (index i), show P.source (index i) ≤ P.source (index i) from le_rfl⟩ ∈
    ordinalDerived (core i) (P.sourceRank (index i))
  cross : ∀ i x, x ∈ core i →
    wolfeMass M (wolfeOperatorRow (if colour then T else S) x)
      (wolfeCrossUnion (fun j => range (P.embedding (index j))) i) < δ

theorem exists_ordinalVariableUnitColouredCores
    (P : OrdinalVariableUnitParameters γ N)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ)))
    (T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    {ε δ : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ) :
    Nonempty (OrdinalVariableUnitColouredCores P M T S ε δ) := by
  obtain ⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_sequence_crossMass M
      (JLMS.scattered_subtype JLMS.scattered_ordinal _) T S hTS
      P.source P.sourceRank P.source_top_level (fun i => P.embedding i)
      P.embedding_isOpen P.outerBlock_disjoint
      P.bandLevels P.bandLevels_monotone hN hδ P.sourceRank
      (fun i => ⟨P.source i, show P.source i ≤ P.source i from le_rfl⟩)
      (fun i => ordinalTower_top_mem_subtypeDerived (P.source_top_level i))
  exact ⟨⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩⟩

end Posets
