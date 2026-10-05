import Posets.OrdinalIdealTransportSingularBelowSquare
import JLMS.OrdinalSpacePowerSuccessor

/-! All positive finite powers of a singular infinite initial ordinal have
continuous-function spaces isomorphic to the initial space itself. This is
proved by actual successor-block decompositions and full singular replication. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance singularPowerEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularPowerEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def singularInitialFinitePowerEndpointEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    ordinalEndpointZero 𝕜 (c.ord ^ ((n+1 : ℕ) : Ordinal)) ≃L[𝕜]
      ordinalEndpointZero 𝕜 c.ord := by
  induction n with
  | zero =>
      rw [show ((0+1 : ℕ) : Ordinal.{0}) = 1 by norm_num, Ordinal.opow_one]
  | succ n ih =>
      have hβ : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have he : ((n+1+1 : ℕ) : Ordinal.{0}) = Order.succ ((n+1 : ℕ) : Ordinal) :=
        Ordinal.natCast_succ (n+1)
      change ordinalEndpointZero 𝕜 (c.ord ^ ((n+1+1 : ℕ) : Ordinal)) ≃L[𝕜] _
      rw [he]
      exact (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc _ hβ).trans
        ((CZeroSum.congrRight (fun _ : Set.Iio c.ord => ih)
          (norm_nonneg _) (norm_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)).trans
          (ordinalEndpointZeroSingularInitialReplication (𝕜 := 𝕜) c hc hs).symm)

def singularInitialFinitePowerEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    OrdinalSpace 𝕜 (c.ord ^ ((n+1 : ℕ) : Ordinal)) ≃L[𝕜] OrdinalSpace 𝕜 c.ord := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hβ : (1 : Ordinal.{0}) ≤ ((n+1 : ℕ) : Ordinal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  exact (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
    (ordinalInitialPower_infinite c hc _ hβ)).trans
      ((singularInitialFinitePowerEndpointEquiv hc hs n).trans
        (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord hκ).symm)

theorem singularInitialFinitePower_hasUPFP {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ ((n+1 : ℕ) : Ordinal))) :=
  (singularInitialOrdinal_hasUPFP hc hs).of_equiv (singularInitialFinitePowerEquiv hc hs n).symm

theorem proposition_3_1_singular_finitePower {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (n : ℕ) :
    Proposition_3_1 𝕜 (c.ord ^ ((n+1 : ℕ) : Ordinal)) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (c.ord ^ ((n+1 : ℕ) : Ordinal))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (singularInitialFinitePower_hasUPFP (𝕜 := 𝕜) hc hs n).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
