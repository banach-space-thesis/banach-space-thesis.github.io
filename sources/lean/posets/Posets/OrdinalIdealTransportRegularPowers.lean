import Posets.OrdinalIdealTransportRegularSquare
import JLMS.OrdinalSpacePowerSuccessor

/-! Finite powers from the second onward reduce to the square by actual
successor-block decompositions and the square's full replication. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance regularPowerEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance regularPowerEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def initialHigherFinitePowerEndpointEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) :
    ordinalEndpointZero 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal)) ≃L[𝕜]
      ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal)) := by
  induction n with
  | zero =>
      rw [show ((0+2 : ℕ) : Ordinal.{0}) = 2 by norm_num]
  | succ n ih =>
      have hβ : (1 : Ordinal.{0}) ≤ ((n+2 : ℕ) : Ordinal) := by
        exact_mod_cast (show 1 ≤ n+2 by omega)
      have he : ((n+2+1 : ℕ) : Ordinal.{0}) = Order.succ ((n+2 : ℕ) : Ordinal) :=
        Ordinal.natCast_succ (n+2)
      have r : ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal)) ≃L[𝕜]
          CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal))) := by
        have r := ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc 1 le_rfl
        rw [Ordinal.succ_one] at r
        exact r
      change ordinalEndpointZero 𝕜 (c.ord ^ ((n+2+1 : ℕ) : Ordinal)) ≃L[𝕜] _
      rw [he]
      exact (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc _ hβ).trans
        ((CZeroSum.congrRight (fun _ : Set.Iio c.ord => ih)
          (norm_nonneg _) (norm_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)).trans r.symm)

def initialHigherFinitePowerEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) :
    OrdinalSpace 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal)) ≃L[𝕜]
      OrdinalSpace 𝕜 (c.ord * c.ord) := by
  have hβ : (1 : Ordinal.{0}) ≤ ((n+2 : ℕ) : Ordinal) := by
    exact_mod_cast (show 1 ≤ n+2 by omega)
  have hpow : c.ord ^ (2 : Ordinal) = c.ord * c.ord := by
    rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
  exact (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
    (ordinalInitialPower_infinite c hc _ hβ)).trans
      ((initialHigherFinitePowerEndpointEquiv hc n).trans
        ((ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
          (ordinalInitialPower_infinite c hc 2 one_le_two)).symm.trans
            (ordinalSpaceCongrIsometry (𝕜 := 𝕜) hpow).toContinuousLinearEquiv))

theorem regularInitialHigherFinitePower_hasUPFP {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal))) :=
  (regularInitialSquare_hasUPFP hc hu).of_equiv (initialHigherFinitePowerEquiv hu.le n).symm

theorem proposition_3_1_regular_higherFinitePower {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) :
    Proposition_3_1 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal)) := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) (c.ord ^ ((n+2 : ℕ) : Ordinal))) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (regularInitialHigherFinitePower_hasUPFP (𝕜 := 𝕜) hc hu n).hasPFP
  exact ⟨h.2, fun _ => h.1⟩

end Posets
