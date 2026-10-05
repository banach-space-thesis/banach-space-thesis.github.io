import Posets.OrdinalRegularOmegaMiddlePowers
import Posets.OrdinalIdealTransportLowRank
import Posets.PrimaryFactorizationTransport

/-! Actual Banach-space equivalence throughout κ^ω ≤ α < κ^(ω²).
The equivalence works for every infinite initial base, including singular bases.
Its bounds may depend on α. The factorisation corollary explicitly requires
the factorisation property of the κ^ω model. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def ordinalOmegaMiddlePowerEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0})) :
    OrdinalSpace 𝕜 (c.ord ^ β) ≃L[𝕜] OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) :=
  (ordinalSpaceEndpointZeroBoundedEquiv _
    (ordinalInitialPower_infinite c hc β (Ordinal.one_lt_omega0.le.trans hlo))).trans
    ((ordinalOmegaMiddleEndpointPowerEquiv c hc β hlo hhi).trans
      (ordinalSpaceEndpointZeroBoundedEquiv _ (ordinalOmegaMiddle_base_infinite c hc)).symm)

def ordinalOmegaMiddleSquareEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c) :
    OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) ≃L[𝕜]
      OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) × OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) :=
  ordinalSpaceInitialPowerSquareEquiv c hc Ordinal.omega0 (Ordinal.nat_lt_omega0 2).le
    (by simpa only [Ordinal.card_omega0] using hc)

def ordinalOmegaMiddlePowerMultipleEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{0}) (hlo : Ordinal.omega0 ≤ β)
    (hhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0}))
    (η : Ordinal.{0}) (hη : 0 < η) (hηκ : η < c.ord) :
    OrdinalSpace 𝕜 (c.ord ^ β * η) ≃L[𝕜] OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) := by
  refine Classical.choice ?_
  have hβ : 1 ≤ β := Ordinal.one_lt_omega0.le.trans hlo
  have hinf := ordinalInitialPower_infinite c hc β hβ
  by_cases hηω : η < Ordinal.omega0
  · obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hηω
    have hmpos : 0 < m := by
      have : (0 : Ordinal.{0}) < (m : Ordinal) := by simpa only [← hm] using hη
      exact_mod_cast this
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hm]
    exact ⟨(ordinalSpaceFinitePower (𝕜 := 𝕜) _ hinf n).trans
      ((ContinuousLinearEquiv.piCongrRight
        (fun _ : Fin (n+1) => ordinalOmegaMiddlePowerEquiv c hc β hlo hhi)).trans
          (finitePiCollapseEquiv (ordinalOmegaMiddleSquareEquiv c hc) n))⟩
  · have hκ : c.ord ≤ c.ord ^ β := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
        (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)) hβ
    have habs : η + c.ord ^ β = c.ord ^ β :=
      Ordinal.principal_add_iff_add_left_eq_self.mp
        (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) β)
        η (hηκ.trans_le hκ)
    exact ⟨(ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
      (hinf.trans (Ordinal.le_mul_left _ hη))).trans
        ((ordinalOmegaMiddleEndpointMultiplyEquiv c hc _ η hinf (le_of_not_gt hηω)
          (Cardinal.lt_ord.mp hηκ).le (Or.inr habs)
          (ordinalOmegaMiddleEndpointPowerEquiv c hc β hlo hhi)).trans
            (ordinalSpaceEndpointZeroBoundedEquiv _ (ordinalOmegaMiddle_base_infinite c hc)).symm)⟩

def ordinalOmegaMiddleEquiv (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{0}) (hlo : c.ord ^ Ordinal.omega0 ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) :
    OrdinalSpace 𝕜 α ≃L[𝕜] OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0) := by
  refine Classical.choice ?_
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hα : α ≠ 0 := ((Ordinal.opow_pos _ (zero_lt_one.trans hκ)).trans_le hlo).ne'
  let β := Ordinal.log c.ord α
  have hβ : Ordinal.omega0 ≤ β := Ordinal.le_log_of_opow_le hκ hlo
  have hβhi : β < Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
    (Ordinal.lt_opow_iff_log_lt hκ hα).mp hhi
  let η := α / (c.ord ^ β)
  have hη : 0 < η := Ordinal.div_opow_log_pos c.ord hα
  have hηκ : η < c.ord := Ordinal.div_opow_log_lt α hκ
  let ρ := α % (c.ord ^ β)
  have hρ : ρ < c.ord ^ β := Ordinal.mod_lt _ (Ordinal.opow_pos β (zero_lt_one.trans hκ)).ne'
  have he : α = c.ord ^ β * η + ρ := (Ordinal.div_add_mod α _).symm
  exact ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
    ((ordinalSpacePowerRemainder c hc β η ρ (Ordinal.one_lt_omega0.le.trans hβ) hη hρ).trans
      (ordinalOmegaMiddlePowerMultipleEquiv c hc β hβ hβhi η hη hηκ))⟩

theorem ordinalOmegaMiddle_hasUPFP_of_base (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (hbase : HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0)))
    (α : Ordinal.{0}) (hlo : c.ord ^ Ordinal.omega0 ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  hbase.of_equiv (ordinalOmegaMiddleEquiv c hc α hlo hhi).symm

theorem ordinalOmegaMiddle_hasPFP_of_base (c : Cardinal.{0}) (hc : Cardinal.aleph0 ≤ c)
    (hbase : HasPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0)))
    (α : Ordinal.{0}) (hlo : c.ord ^ Ordinal.omega0 ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) :
    HasPFP 𝕜 (OrdinalSpace 𝕜 α) :=
  hasPFP_of_equiv hbase (ordinalOmegaMiddleEquiv c hc α hlo hhi).symm

theorem ordinalOmegaMiddle_proposition_3_1_of_base (c : Cardinal.{0})
    (hc : Cardinal.aleph0 ≤ c)
    (hbase : HasPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ Ordinal.omega0)))
    (α : Ordinal.{0}) (hlo : c.ord ^ Ordinal.omega0 ≤ α)
    (hhi : α < c.ord ^ (Ordinal.omega0 ^ (2 : Ordinal.{0}))) : Proposition_3_1 𝕜 α := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP
    (ordinalOmegaMiddle_hasPFP_of_base c hc hbase α hlo hhi)
  exact ⟨h.2, fun _ => h.1⟩

end Posets
