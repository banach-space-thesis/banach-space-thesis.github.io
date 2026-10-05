import Posets.OrdinalRankUnitOmegaSelectedFactorization
import Posets.OrdinalPrincipalOmegaAssemblyFactorization
import Posets.OrdinalInitialOmegaPreservation

/-! Unconditional preservation at the first limit power of any rank unit
at least omega. In particular this reaches κ^(ω²), for every uncountable κ. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000

local instance ordinalRankUnitPreservationWeakOrdinal :
    WeaklyLocallyCompactSpace Ordinal.{u} where
  exists_compact_mem_nhds x := ⟨Iic x, ordinalClosedCore_interval_compact x,
    (ordinal_isClopen_Iic x).isOpen.mem_nhds (show x ≤ x from le_rfl)⟩

local instance ordinalRankUnitPreservationLocallyCompact (Γ : Ordinal.{u}) :
    LocallyCompactSpace (Iio Γ) := isOpen_Iio.locallyCompactSpace

variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalRankUnitOmega_halfOpen_hasCPFP (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) :
    HasCPFP 𝕜 (JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))) 640 := by
  have hB : Ordinal.omega0 < ordinalRankUnitOmegaBase ρ := by
    simpa only [ordinalRankUnitOmegaBase, Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
        (Ordinal.one_lt_omega0.trans_le hρ)
  apply ordinalPrincipalOmegaHalfOpen_hasCPFP_of_block_splittings _ hB
    (Ordinal.principal_add_omega0_opow ρ)
  intro T S hTS
  let M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) :=
    (JLMS.exists_atomicDualModel (JLMS.scattered_subtype JLMS.scattered_ordinal _)).some
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖T‖ + ‖S‖) / (1 / 100 : ℝ))
  have hN' : ‖T‖ + ‖S‖ < N * (1 / 100 : ℝ) :=
    (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 100)).mp hN
  obtain ⟨F⟩ := exists_ordinalRankUnitOmegaColouredCores ρ hρ M T S hTS hN'
    (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨J, R, hf, hJ, hR⟩ := F.selected_block_factorization
  refine ⟨F.colour, (fun i => F.index i + 1), ?_, by dsimp; omega, J, R, hf, hJ, hR⟩
  intro i j hij
  exact Nat.add_lt_add_right (F.strictMono hij) 1

theorem ordinalRankUnitOmega_halfOpen_hasUPFP (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) :
    HasUPFP 𝕜 (JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))) :=
  ordinalPrincipalOmegaHalfOpen_hasUPFP_of_hasCPFP640 _ (ordinalRankUnitOmega_halfOpen_hasCPFP ρ hρ)

theorem ordinalRankUnitOmega_hasUPFP (ρ : Ordinal.{u})
    (hρ : Ordinal.omega0 ≤ ρ) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ (ρ * Ordinal.omega0))) := by
  have hB : Ordinal.omega0 < ordinalRankUnitOmegaBase ρ := by
    simpa only [ordinalRankUnitOmegaBase, Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
        (Ordinal.one_lt_omega0.trans_le hρ)
  have h := ordinalPrincipalOmegaContinuous_hasUPFP_of_halfOpen _ hB
    (Ordinal.principal_add_omega0_opow ρ) (ordinalRankUnitOmega_halfOpen_hasUPFP (𝕜 := 𝕜) ρ hρ)
  have he : ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0 =
      Ordinal.omega0 ^ (ρ * Ordinal.omega0) := (Ordinal.opow_mul _ _ _).symm
  exact h.of_equiv (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv

theorem ordinalInitialOmegaSquare_hasUPFP (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{u})))) := by
  have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le)
  have hκω : Ordinal.omega0 ≤ c.ord * Ordinal.omega0 := Ordinal.le_mul_right _ hκ
  have h := ordinalRankUnitOmega_hasUPFP (𝕜 := 𝕜) (c.ord * Ordinal.omega0)
    hκω
  have heω : Ordinal.omega0 ^ (2 : Ordinal.{u}) = Ordinal.omega0 * Ordinal.omega0 := by
    rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
  have he : Ordinal.omega0 ^ ((c.ord * Ordinal.omega0) * Ordinal.omega0) =
      c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{u})) := by
    rw [mul_assoc, Ordinal.opow_mul, ordinal_uncountable_initial_omega_power hc, heω]
  exact h.of_equiv (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv

theorem proposition_3_1_initialOmegaSquare {𝕜 : Type} [RCLike 𝕜]
    (c : Cardinal.{0}) (hc : Cardinal.aleph0 < c) :
    Proposition_3_1 𝕜 (c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0})))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (ordinalInitialOmegaSquare_hasUPFP (𝕜 := 𝕜) c hc).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
