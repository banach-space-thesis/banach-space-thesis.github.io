import Posets.OrdinalAmbientCoreBandsSequence
import Posets.OrdinalRankUnitOmegaBandParameters

/-! The actual coloured compact cores for the first limit power of an
arbitrary ordinal power base. The operators and atomic model live throughout
on the half-open global ordinal space. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

local instance ordinalRankUnitOmegaCoresWeakOrdinal : WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩

local instance ordinalRankUnitOmegaCoresLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace

def ordinalRankUnitOmegaOuterHeight (N i : ℕ) : ℕ := (N+1)*(i+1)

theorem ordinalRankUnitOmegaOuterHeight_strictMono (N : ℕ) :
    StrictMono (ordinalRankUnitOmegaOuterHeight N) := by
  intro i j hij
  exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 1) (Nat.succ_pos N)

def ordinalRankUnitOmegaSourceHeight (N i : ℕ) : ℕ := (N+1)*(i+2)

def ordinalRankUnitOmegaSource (ρ : Ordinal.{u}) (N i : ℕ) : Ordinal.{u} :=
  ordinalRankUnitOmegaBase ρ ^ (ordinalRankUnitOmegaSourceHeight N i : Ordinal)

def ordinalRankUnitOmegaSourceRank (ρ : Ordinal.{u}) (N i : ℕ) : Ordinal.{u} :=
  ρ * (ordinalRankUnitOmegaSourceHeight N i : Ordinal)

def ordinalRankUnitOmegaSourceEmbedding (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (N i : ℕ) : C(Iic (ordinalRankUnitOmegaSource ρ N i), Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) :=
  ordinalRankUnitOmegaOuterBlock ρ hρ (ordinalRankUnitOmegaOuterHeight N i)
    (ordinalRankUnitOmegaSourceHeight N i)
    (ordinalRankUnitOmegaOuterHeight_strictMono N (Nat.lt_succ_self i))

theorem ordinalRankUnitOmegaSourceEmbedding_isOpen (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) (N i : ℕ) :
    IsOpenEmbedding (ordinalRankUnitOmegaSourceEmbedding ρ hρ N i) := by
  unfold ordinalRankUnitOmegaSourceEmbedding ordinalRankUnitOmegaOuterBlock
  apply ordinalOuterBlockMap_isOpenEmbedding

theorem ordinalRankUnitOmegaSource_top_level (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) (N i : ℕ) :
    ordinalRankUnitOmegaSource ρ N i ∈ ordinalTowerLevel
      (ordinalRankUnitOmegaSource ρ N i) (ordinalRankUnitOmegaSourceRank ρ N i) :=
  ordinal_rank_unit_finite_power_top_level ρ hρ _
    (Nat.mul_pos (Nat.succ_pos N) (by omega))

variable {𝕜 : Type*} [RCLike 𝕜]

structure OrdinalRankUnitOmegaColouredCores
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)))
    (T S : JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))) (N : ℕ) (ε δ : ℝ) where
  colour : Bool
  index : ℕ → ℕ
  strictMono : StrictMono index
  band : ℕ → Fin N
  core : ℕ → Set (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))
  compact : ∀ i, IsCompact (core i)
  leaf_closure : ∀ i, core i ⊆ closure (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (index i) ''
    ordinalAmbientBandLeaves (ordinalRankUnitOmegaSource_top_level ρ hρ N (index i))
      (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (index i))
      (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (index i)) M T S
      (ordinalRankUnitOmegaBandLevels ρ N (index i+2)) (band i).val colour ε)
  block : ∀ i, core i ⊆ range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (index i))
  rank : ∀ i, ordinalRankUnitOmegaSourceEmbedding ρ hρ N (index i)
      ⟨ordinalRankUnitOmegaSource ρ N (index i), show ordinalRankUnitOmegaSource ρ N (index i) ≤
        ordinalRankUnitOmegaSource ρ N (index i) from le_rfl⟩ ∈
    ordinalDerived (core i) (ordinalRankUnitOmegaSourceRank ρ N (index i))
  cross : ∀ i x, x ∈ core i →
    wolfeMass M (wolfeOperatorRow (if colour then T else S) x)
      (wolfeCrossUnion (fun j => range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (index j))) i) < δ

/-- Concrete application of finite band colouring and the proved cross-mass
descent. No operator-preservation conclusion is assumed in this selection. -/
theorem exists_ordinalRankUnitOmegaColouredCores
    (ρ : Ordinal.{u}) (hρ : Ordinal.omega0 ≤ ρ)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)))
    (T S : JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    {N : ℕ} {ε δ : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ) :
    Nonempty (OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ) := by
  have hdisj : Pairwise (fun i j =>
      Disjoint (range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N i))
        (range (ordinalRankUnitOmegaSourceEmbedding ρ hρ N j))) :=
    ordinalRankUnitOmegaOuterFamily_disjoint ρ hρ
      (ordinalRankUnitOmegaOuterHeight N) (ordinalRankUnitOmegaOuterHeight_strictMono N)
  obtain ⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_sequence_crossMass M
      (JLMS.scattered_subtype JLMS.scattered_ordinal _) T S hTS
      (ordinalRankUnitOmegaSource ρ N) (ordinalRankUnitOmegaSourceRank ρ N)
      (ordinalRankUnitOmegaSource_top_level ρ hρ N)
      (fun i => ordinalRankUnitOmegaSourceEmbedding ρ hρ N i)
      (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N) hdisj
      (fun i => ordinalRankUnitOmegaBandLevels ρ N (i+2))
      (fun i => ordinalRankUnitOmegaBandLevels_monotone ρ N (i+2)) hN hδ
      (ordinalRankUnitOmegaSourceRank ρ N)
      (fun i => ⟨ordinalRankUnitOmegaSource ρ N i, show ordinalRankUnitOmegaSource ρ N i ≤
        ordinalRankUnitOmegaSource ρ N i from le_rfl⟩)
      (fun i => ordinalTower_top_mem_subtypeDerived (ordinalRankUnitOmegaSource_top_level ρ hρ N i))
  exact ⟨⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩⟩

end Posets

