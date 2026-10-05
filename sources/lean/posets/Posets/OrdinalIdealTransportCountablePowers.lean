import Posets.OrdinalIdealTransportOmega
import JLMS.OrdinalSpacePowerSuccessor

/-! The primary factorisation theorem for finite positive powers of ω.
The actual ordinal block maps identify these function spaces with c₀;
the all-operator dichotomy is then transported from the proved scalar case. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance countablePowerEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance countablePowerEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance countablePowerSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance countablePowerSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalNatIioOmegaEquiv : ℕ ≃ Set.Iio (Ordinal.omega0 : Ordinal.{0}) :=
  Equiv.ofBijective (fun n => ⟨n, Ordinal.nat_lt_omega0 n⟩) (by
    constructor
    · intro n m h
      have hval := congrArg Subtype.val h
      change (n : Ordinal.{0}) = m at hval
      exact_mod_cast hval
    · intro a
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp a.property
      exact ⟨n, Subtype.ext hn.symm⟩)

def ordinalFinitePowerEndpointCZeroEquiv (n : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0})) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : ℕ => 𝕜) := by
  induction n with
  | zero =>
    rw [show ((0+1 : ℕ) : Ordinal.{0}) = 1 by norm_num, Ordinal.opow_one]
    exact (JLMS.ordinalOmegaEndpointCZeroIsometry (𝕜 := 𝕜)).toContinuousLinearEquiv
  | succ n e =>
    have hn : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    let b : JLMS.ordinalEndpointZero 𝕜
        (Ordinal.omega0 ^ ((n+1+1 : ℕ) : Ordinal.{0})) ≃L[𝕜]
        JLMS.CZeroSum 𝕜 (fun _ : Set.Iio (Ordinal.omega0 : Ordinal.{0}) =>
          JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}))) := by
      have hb := JLMS.ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜)
        Cardinal.aleph0 le_rfl ((n+1 : ℕ) : Ordinal.{0}) hn
      rw [Cardinal.ord_aleph0] at hb
      simpa only [Ordinal.natCast_succ] using hb
    exact b.trans ((JLMS.CZeroSum.reindex (𝕜 := 𝕜)
      (E := fun _ : Set.Iio (Ordinal.omega0 : Ordinal.{0}) =>
        JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0})))
      ordinalNatIioOmegaEquiv).toContinuousLinearEquiv.trans
      ((JLMS.CZeroSum.congrRight (fun _ : ℕ => e)
        (norm_nonneg _) (norm_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)).trans
        (JLMS.CZeroSum.infiniteReplicateIsometry (𝕜 := 𝕜) ℕ 𝕜).symm.toContinuousLinearEquiv))

def ordinalFinitePowerCZeroEquiv (n : ℕ) :
    OrdinalSpace 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0})) ≃L[𝕜]
      CZeroSum 𝕜 := by
  have hn : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hinf : Ordinal.omega0 ≤ Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos hn
  exact (JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ hinf).trans
    ((ordinalFinitePowerEndpointCZeroEquiv n).trans
      ((JLMS.ordinalSpaceOmegaCZeroEquiv (𝕜 := 𝕜)).symm.trans ordinalOmegaCZeroEquiv))

theorem ordinalFinitePower_hasUPFP (n : ℕ) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}))) :=
  scalar_cZero_hasUPFP.of_equiv (ordinalFinitePowerCZeroEquiv n).symm

theorem proposition_3_1_omega_finitePower (n : ℕ) :
    Proposition_3_1 𝕜 (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0})) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0})
      (Ordinal.omega0 ^ ((n+1 : ℕ) : Ordinal.{0}))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (𝕜 := 𝕜)
    (ordinalFinitePower_hasUPFP (𝕜 := 𝕜) n).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
