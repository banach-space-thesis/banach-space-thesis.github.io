import JLMS.OrdinalSpacePowerBlocks
import JLMS.OrdinalSpacePowerSuccessor
import JLMS.CZeroSumCoordinateAbsorption

/-!
# Limit powers in Kislyakov's Corollary 3.2 and Lemma 3.2

The continuous cofinal exponent sequence splits κ^γ into blocks whose
lengths are successor powers of κ. Its cofinality summand is absorbed by
the first block. Uniform successor-power replication and Fubini then
identify the whole space with κ copies of itself.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance powerLimitFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance powerLimitFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance powerLimitEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerLimitEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerLimitSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance powerLimitSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

def ordinalPowerBlockPredecessor (γ ξ : Ordinal.{u}) : Ordinal.{u} :=
  2 + ordinalFundamentalExtension γ (Ordinal.exists_fundamental_sequence γ).choose ξ

theorem two_le_ordinalPowerBlockPredecessor (γ ξ : Ordinal.{u}) :
    2 ≤ ordinalPowerBlockPredecessor γ ξ := Ordinal.le_add_right _ _

theorem ordinalPowerBlockPredecessor_spec (γ ξ : Ordinal.{u}) :
    ordinalCofinalExponent γ (Order.succ ξ) = Order.succ (ordinalPowerBlockPredecessor γ ξ) :=
  ordinalCofinalExponent_succ γ ξ

theorem ordinalPowerLimit_cofinality_infinite (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) :
    Ordinal.omega0 ≤ γ.cof.ord := by
  simpa using Cardinal.ord_le_ord.mpr (Ordinal.aleph0_le_cof.mpr hγ)

theorem ordinalPowerLimit_cofinality_absorption (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hcard : γ.card ≤ c) (ξ : Ordinal.{u}) :
    γ.cof.ord + c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ) =
      c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ) := by
  have hcof : γ.cof.ord ≤ c.ord := Cardinal.ord_le_ord.mpr ((Ordinal.cof_le_card γ).trans hcard)
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le
    (by simpa using Cardinal.ord_le_ord.mpr hc)
  have hp : 1 < Order.succ (ordinalPowerBlockPredecessor γ ξ) :=
    (show (1 : Ordinal) < 2 by norm_num).trans_le
      ((two_le_ordinalPowerBlockPredecessor γ ξ).trans (Order.le_succ _))
  have hlt : c.ord < c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ) := by
    simpa only [Ordinal.opow_one] using (Ordinal.opow_lt_opow_iff_right hκ).mpr hp
  exact Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _) _ (hcof.trans_lt hlt)

/-- The actual varying successor-power sum in Kislyakov Corollary 3.2. -/
def ordinalEndpointZeroPowerLimitSum (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) (hcard : γ.card ≤ c) :
    ordinalEndpointZero 𝕜 (c.ord ^ γ) ≃L[𝕜]
      CZeroSum 𝕜 (fun ξ : Set.Iio γ.cof.ord =>
        ordinalEndpointZero 𝕜 (c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ.val))) := by
  let L := ordinalCofinalPowerMap c.ord γ
    (Ordinal.one_lt_omega0.trans_le (by simpa using Cardinal.ord_le_ord.mpr hc)) hγ
  let E : Set.Iio γ.cof.ord → Type _ := fun ξ =>
    ordinalEndpointZero 𝕜 (c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ.val))
  let d : CZeroSum 𝕜 (fun ξ : Set.Iio γ.cof.ord =>
      ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength L ξ)) ≃ₗᵢ[𝕜] CZeroSum 𝕜 E :=
    CZeroSum.congrRightIsometry (fun ξ => ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) (by
      change ordinalSpaceBlockLength L ξ = c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ.val)
      rw [ordinalCofinalPowerMap_blockLength c hc γ hγ ξ, ordinalPowerBlockPredecessor_spec]))
  let e : ordinalEndpointZero 𝕜 (c.ord ^ γ) ≃L[𝕜]
      ordinalEndpointZero 𝕜 γ.cof.ord × CZeroSum 𝕜 E :=
    (ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) L
      (ordinalCofinalPowerMap_strictMono _ _ _ _) (ordinalCofinalPowerMap_zero _ _ _ _)
      (ordinalCofinalPowerMap_endpoint _ _ _ _) (ordinalCofinalPowerMap_infinite_blocks c hc γ hγ)).trans
        ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr d.toContinuousLinearEquiv)
  let ξ₀ : Set.Iio γ.cof.ord := ⟨0, Ordinal.omega0_pos.trans_le (ordinalPowerLimit_cofinality_infinite γ hγ)⟩
  let a : (ordinalEndpointZero 𝕜 γ.cof.ord × E ξ₀) ≃L[𝕜] E ξ₀ :=
    ordinalEndpointZeroAbsorbLeft _ _ (ordinalPowerLimit_cofinality_infinite γ hγ)
      (ordinalInitialPower_infinite c hc _
        (one_le_two.trans ((two_le_ordinalPowerBlockPredecessor γ ξ₀.val).trans (Order.le_succ _))))
      (ordinalPowerLimit_cofinality_absorption c hc γ hcard ξ₀.val)
  exact e.trans (cZeroSumAbsorbsAt (𝕜 := 𝕜) E ξ₀ a)

/-- The limit-exponent step of Kislyakov Lemma 3.2. -/
def ordinalEndpointZeroPowerLimitReplication (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) (hcard : γ.card ≤ c) :
    ordinalEndpointZero 𝕜 (c.ord ^ γ) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ γ)) := by
  let E : Set.Iio γ.cof.ord → Type _ := fun ξ =>
    ordinalEndpointZero 𝕜 (c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ.val))
  let e := ordinalEndpointZeroPowerLimitSum (𝕜 := 𝕜) c hc γ hγ hcard
  let r := fun ξ : Set.Iio γ.cof.ord =>
    ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc
      (ordinalPowerBlockPredecessor γ ξ.val) (one_le_two.trans (two_le_ordinalPowerBlockPredecessor γ ξ.val))
  have hr (ξ : Set.Iio γ.cof.ord) : ‖(r ξ).toContinuousLinearMap‖ ≤ 64 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalEndpointZeroPowerSuccessorReplication_le (𝕜 := 𝕜) c hc _ _)
  have hri (ξ : Set.Iio γ.cof.ord) : ‖(r ξ).symm.toContinuousLinearMap‖ ≤ 64 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalEndpointZeroPowerSuccessorReplication_symm_le (𝕜 := 𝕜) c hc _ _)
  let R := CZeroSum.congrRight r (by norm_num : (0 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 64) hr hri
  let F := CZeroSum.commuteIsometry (𝕜 := 𝕜)
    (E := fun (ξ : Set.Iio γ.cof.ord) (_ : Set.Iio c.ord) => E ξ)
  let D := CZeroSum.congrRight (fun _ : Set.Iio c.ord => e.symm)
    (norm_nonneg _) (norm_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)
  exact e.trans (R.trans (F.toContinuousLinearEquiv.trans D))

end JLMS
