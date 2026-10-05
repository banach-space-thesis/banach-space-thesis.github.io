import LPCK.OrdinalBackground
import LPCK.MainStatements
import Posets.OrdinalHigherLimitCofinalPreservation
import JLMS.OrdinalSpacePowerSquare
import ThesisCommon.Analysis.LpArbitraryProducts

/-! Genuine c0 self-equivalence of higher initial-ordinal powers, and the
sequence-space theorem on the canonical powers whose rank has countable
cofinality. The cofinality restriction is explicit: these results do not
replace the original arbitrary-ordinal target. -/
noncomputable section
open Set Topology
open scoped ENNReal
namespace LPCK
open ThesisCommon
universe u
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

def jlmsInfiniteCZeroCountableSelfIsometry (I X : Type*) [Infinite I]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    JLMS.CZeroSum 𝕜 (fun _ : I => X) ≃ₗᵢ[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : ℕ => JLMS.CZeroSum 𝕜 (fun _ : I => X)) :=
  (JLMS.CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : I => X)
    ((Equiv.prodComm ℕ I).trans (infiniteCountableProductEquiv I))).trans
      (JLMS.CZeroSum.prodIsometry (𝕜 := 𝕜) (E := fun (_ : ℕ) (_ : I) => X)).symm

def initialPowerCZeroEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (hcard : γ.card ≤ c) :
    OrdinalContinuous 𝕜 (c.ord ^ γ) ≃L[𝕜]
      CZeroSum (OrdinalContinuous 𝕜 (c.ord ^ γ)) := by
  letI := JLMS.ordinalIioInfinite c.ord (by simpa using Cardinal.ord_le_ord.mpr hc)
  let r : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ γ) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Iio c.ord => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ γ)) :=
    Classical.choice (JLMS.nonempty_ordinalEndpointZeroPowerReplication
      (𝕜 := 𝕜) c hc γ hγ hcard)
  let e : OrdinalContinuous 𝕜 (c.ord ^ γ) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : Iio c.ord => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ γ)) :=
    (JLMS.ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) (c.ord ^ γ)
      (JLMS.ordinalInitialPower_infinite c hc γ (one_le_two.trans hγ))).trans r
  let f : JLMS.CZeroSum 𝕜 (fun _ : ℕ =>
      JLMS.CZeroSum 𝕜 (fun _ : Iio c.ord => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ γ))) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : ℕ => OrdinalContinuous 𝕜 (c.ord ^ γ)) :=
    JLMS.CZeroSum.congrRight (𝕜 := 𝕜)
      (fun _ : ℕ => e.symm) (norm_nonneg e.symm.toContinuousLinearMap)
      (norm_nonneg e.toContinuousLinearMap) (fun _ => le_rfl)
      (fun _ => by simp only [ContinuousLinearEquiv.symm_symm]; exact le_rfl)
  exact e.trans ((jlmsInfiniteCZeroCountableSelfIsometry (𝕜 := 𝕜) (Iio c.ord)
    (JLMS.ordinalEndpointZero 𝕜 (c.ord ^ γ))).toContinuousLinearEquiv.trans
      (f.trans (jlmsCZeroMapIsometry (𝕜 := 𝕜)).toContinuousLinearEquiv))

theorem initialCanonical_sequence_of_base (c : Cardinal.{u})
    (hc : Cardinal.aleph0 < c) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (hcard : γ.card ≤ c)
    (hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ γ))) (p : BanachExponent) :
    Theorem_1_1 𝕜 (c.ord ^ γ) p := by
  have hr0 : c.ord * γ ≠ 0 := (mul_pos
    (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc.le))
    (zero_lt_one.trans_le (one_le_two.trans hγ))).ne'
  have he : Ordinal.omega0 ^ (c.ord * γ) = c.ord ^ γ :=
    Posets.ordinal_uncountable_initial_power_rank hc γ
  have hD : ordinalDerived (Icc 0 (c.ord ^ γ)) (c.ord * γ) = {c.ord ^ γ} := by
    rw [← he]
    have hs : Icc (0 : Ordinal.{u}) (Ordinal.omega0 ^ (c.ord * γ)) =
        Iic (Ordinal.omega0 ^ (c.ord * γ)) := by ext x; simp
    rw [hs]
    exact ordinalDerived_Iic_power_self hr0
  have hsum : HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 (c.ord ^ γ))) := by
    by_cases hpTop : p.val = ∞
    · have hp : p = ⟨∞, by simp⟩ := Subtype.ext hpTop
      subst p
      exact hX.ordinal_infinity hD
    by_cases hpOne : p.val = 1
    · have hp : p = ⟨1, le_rfl⟩ := Subtype.ext hpOne
      subst p
      exact hX.ellOne_of_cZero_equiv (initialPowerCZeroEquiv c hc.le γ hγ hcard)
    have hreal : 1 < p.val.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (by simp) hpTop).mpr
          (lt_of_le_of_ne p.property (Ne.symm hpOne))
    exact (ordinal_lp_finite_upfp_primary_of_dual_equiv_ellOne hD hpTop hreal hX
      (ordinalContinuousDualEllOneEquiv (c.ord ^ γ))).1
  exact ⟨hsum, hsum.lp_isPrimary⟩

theorem theorem_1_1_initial_higher_countable_cofinal
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 < c) (η : Ordinal.{u}) (hη : η ≠ 0)
    (hcard : (Ordinal.omega0 ^ η).card ≤ c)
    (hcf : (c.ord * Ordinal.omega0 ^ η).cof = Cardinal.aleph0) (p : BanachExponent) :
    Theorem_1_1 𝕜 (c.ord ^ (Ordinal.omega0 ^ η)) p := by
  have hγ : 2 ≤ Ordinal.omega0 ^ η := (Ordinal.nat_lt_omega0 2).le.trans
    (by simpa only [Ordinal.opow_one] using
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.one_le_iff_ne_zero.mpr hη)))
  exact initialCanonical_sequence_of_base c hc _ hγ hcard
    (Posets.ordinalInitialHigherLimit_hasUPFP c hc η hη hcf) p

end LPCK
