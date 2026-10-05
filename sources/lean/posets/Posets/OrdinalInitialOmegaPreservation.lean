import Posets.OrdinalOmegaSelectedFactorization
import Posets.OrdinalRegularOmegaPreservation
import Posets.OrdinalIdealTransportBelowOmegaPower

/-! Operator preservation at κ^ω for every uncountable initial cardinal,
including singular cardinals. The full range κ≤α<κ^(ω²) follows by transport. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000

local instance ordinalInitialOmegaPreservationWeakOrdinal :
    WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩

local instance ordinalInitialOmegaPreservationLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace

variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalInitialOmega_halfOpen_hasCPFP (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) :
    HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) 640 := by
  apply ordinalOmegaHalfOpen_hasCPFP_of_block_splittings c hc.le
  intro T S hTS
  let M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0)) :=
    (JLMS.exists_atomicDualModel (JLMS.scattered_subtype JLMS.scattered_ordinal _)).some
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖T‖ + ‖S‖) / (1 / 100 : ℝ))
  have hN' : ‖T‖ + ‖S‖ < N * (1 / 100 : ℝ) :=
    (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)).mp hN
  obtain ⟨F⟩ := exists_ordinalRegularOmegaColouredCores c hc M T S hTS hN'
    (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨J, R, hf, hJ, hR⟩ := F.tail.lossSelected_block_factorization
  refine ⟨F.tail.colour, (fun i => F.tail.index i + 1), ?_, F.tail_target_start,
    J, R, hf, hJ, hR⟩
  intro i j hij
  exact Nat.add_lt_add_right (F.tail.strictMono hij) 1

theorem ordinalInitialOmega_halfOpen_hasUPFP (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))) :=
  ordinalOmegaHalfOpen_hasUPFP_of_hasCPFP640 c (ordinalInitialOmega_halfOpen_hasCPFP c hc)

theorem ordinalInitialOmega_hasUPFP (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ Ordinal.omega0)) :=
  ordinalOmegaContinuous_hasUPFP_of_halfOpen c hc.le (ordinalInitialOmega_halfOpen_hasUPFP c hc)

theorem ordinalInitialOmegaMiddle_hasUPFP {𝕜 : Type} [RCLike 𝕜]
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c)
    (α : Ordinal.{0}) (hlo : c.ord ^ Ordinal.omega0 ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  ordinalOmegaMiddle_hasUPFP_of_base c hc.le (ordinalInitialOmega_hasUPFP c hc) α hlo hhi

theorem proposition_3_1_initial_belowOmegaSquare {𝕜 : Type} [RCLike 𝕜]
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c)
    (α : Ordinal.{0}) (hlo : c.ord ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) : Proposition_3_1 𝕜 α := by
  by_cases hω : α < c.ord ^ Ordinal.omega0
  · exact proposition_3_1_uncountable_belowOmegaPower hc hlo hω
  · exact ordinalOmegaMiddle_proposition_3_1_of_base c hc.le
      (ordinalInitialOmega_hasUPFP (𝕜 := 𝕜) c hc).hasPFP α (le_of_not_gt hω) hhi

end Posets
