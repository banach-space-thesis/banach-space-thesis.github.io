import Posets.OrdinalAmbientCoreBandsSequence
import Posets.OrdinalRegularOmegaBandParameters

/-! The actual coloured compact cores for the first limit power of an
uncountable initial ordinal. The operators and atomic model live throughout
on the half-open global ordinal space. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

local instance ordinalRegularOmegaCoresWeakOrdinal : WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩

local instance ordinalRegularOmegaCoresLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace

def ordinalRegularOmegaOuterHeight (N i : ℕ) : ℕ := (N+1)*(i+1)

theorem ordinalRegularOmegaOuterHeight_strictMono (N : ℕ) :
    StrictMono (ordinalRegularOmegaOuterHeight N) := by
  intro i j hij
  exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 1) (Nat.succ_pos N)

def ordinalRegularOmegaSourceHeight (N i : ℕ) : ℕ := (N+1)*(i+2)

def ordinalRegularOmegaSource (c : Cardinal.{u}) (N i : ℕ) : Ordinal.{u} :=
  c.ord ^ (ordinalRegularOmegaSourceHeight N i : Ordinal)

def ordinalRegularOmegaSourceRank (c : Cardinal.{u}) (N i : ℕ) : Ordinal.{u} :=
  c.ord * (ordinalRegularOmegaSourceHeight N i : Ordinal)

def ordinalRegularOmegaSourceEmbedding (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (N i : ℕ) : C(Iic (ordinalRegularOmegaSource c N i), Iio (c.ord ^ Ordinal.omega0)) :=
  ordinalRegularOmegaOuterBlock c hc.le (ordinalRegularOmegaOuterHeight N i)
    (ordinalRegularOmegaSourceHeight N i)
    (ordinalRegularOmegaOuterHeight_strictMono N (Nat.lt_succ_self i))

theorem ordinalRegularOmegaSourceEmbedding_isOpen (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) (N i : ℕ) :
    IsOpenEmbedding (ordinalRegularOmegaSourceEmbedding c hc N i) := by
  unfold ordinalRegularOmegaSourceEmbedding ordinalRegularOmegaOuterBlock
  apply ordinalOuterBlockMap_isOpenEmbedding

theorem ordinalRegularOmegaSource_top_level (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) (N i : ℕ) :
    ordinalRegularOmegaSource c N i ∈ ordinalTowerLevel
      (ordinalRegularOmegaSource c N i) (ordinalRegularOmegaSourceRank c N i) :=
  ordinal_initial_finite_power_top_level c hc _
    (Nat.mul_pos (Nat.succ_pos N) (by omega))

variable {𝕜 : Type*} [RCLike 𝕜]

structure OrdinalRegularOmegaColouredCores
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
    (T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) (N : ℕ) (ε δ : ℝ) where
  colour : Bool
  index : ℕ → ℕ
  strictMono : StrictMono index
  band : ℕ → Fin N
  core : ℕ → Set (Iio (c.ord ^ Ordinal.omega0))
  compact : ∀ i, IsCompact (core i)
  leaf_closure : ∀ i, core i ⊆ closure (ordinalRegularOmegaSourceEmbedding c hc N (index i) ''
    ordinalAmbientBandLeaves (ordinalRegularOmegaSource_top_level c hc N (index i))
      (ordinalRegularOmegaSourceEmbedding c hc N (index i))
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (index i)) M T S
      (ordinalRegularOmegaBandLevels c N (index i+2)) (band i).val colour ε)
  block : ∀ i, core i ⊆ range (ordinalRegularOmegaSourceEmbedding c hc N (index i))
  rank : ∀ i, ordinalRegularOmegaSourceEmbedding c hc N (index i)
      ⟨ordinalRegularOmegaSource c N (index i), show ordinalRegularOmegaSource c N (index i) ≤
        ordinalRegularOmegaSource c N (index i) from le_rfl⟩ ∈
    ordinalDerived (core i) (ordinalRegularOmegaSourceRank c N (index i))
  cross : ∀ i x, x ∈ core i →
    wolfeMass M (wolfeOperatorRow (if colour then T else S) x)
      (wolfeCrossUnion (fun j => range (ordinalRegularOmegaSourceEmbedding c hc N (index j))) i) < δ

/-- Concrete application of finite band colouring and the proved cross-mass
descent. No operator-preservation conclusion is assumed in this selection. -/
theorem exists_ordinalRegularOmegaColouredCores
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c)
    (M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
    (T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
      JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    {N : ℕ} {ε δ : ℝ} (hN : ‖T‖ + ‖S‖ < N * ε) (hδ : 0 < δ) :
    Nonempty (OrdinalRegularOmegaColouredCores c hc M T S N ε δ) := by
  have hdisj : Pairwise (fun i j =>
      Disjoint (range (ordinalRegularOmegaSourceEmbedding c hc N i))
        (range (ordinalRegularOmegaSourceEmbedding c hc N j))) :=
    ordinalRegularOmegaOuterFamily_disjoint c hc.le
      (ordinalRegularOmegaOuterHeight N) (ordinalRegularOmegaOuterHeight_strictMono N)
  obtain ⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_sequence_crossMass M
      (JLMS.scattered_subtype JLMS.scattered_ordinal _) T S hTS
      (ordinalRegularOmegaSource c N) (ordinalRegularOmegaSourceRank c N)
      (ordinalRegularOmegaSource_top_level c hc N)
      (fun i => ordinalRegularOmegaSourceEmbedding c hc N i)
      (ordinalRegularOmegaSourceEmbedding_isOpen c hc N) hdisj
      (fun i => ordinalRegularOmegaBandLevels c N (i+2))
      (fun i => ordinalRegularOmegaBandLevels_monotone c N (i+2)) hN hδ
      (ordinalRegularOmegaSourceRank c N)
      (fun i => ⟨ordinalRegularOmegaSource c N i, show ordinalRegularOmegaSource c N i ≤
        ordinalRegularOmegaSource c N i from le_rfl⟩)
      (fun i => ordinalTower_top_mem_subtypeDerived (ordinalRegularOmegaSource_top_level c hc N i))
  exact ⟨⟨b, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩⟩

end Posets
