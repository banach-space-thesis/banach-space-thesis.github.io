import PFP.OrdinalInitialCoefficientPolymorphic
import PFP.OrdinalLpSeparableRange
import PFP.OrdinalFiniteMultipleAbsorption
import ThesisCommon.Analysis.PrimaryIsometry

/-! The actual finite-quotient reduction for Corollary 4.10(i), with independent
scalar, outer-index and ordinal universes. Finite powers are absorbed in the
outer infinite sum; no coefficient-space primariness is asserted here. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type*)
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
theorem corollary_4_10_i_initial_poly {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) :
    Corollary_4_10_i 𝕜 Γ c.ord :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ c.ord
    (ordinalContinuous_hasUPFP_of_infinite_initial 𝕜 hc)

theorem corollary_4_10_i_initial_finite_quotient_poly {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{u})
    (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) :
    Corollary_4_10_i 𝕜 Γ α := by
  obtain ⟨n, ρ, hρ, heq⟩ := JLMS.exists_initial_finite_quotient_remainder c hc α hlo hhi
  have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
    calc
      c.ord = c.ord * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
  let e : OrdinalContinuous 𝕜 α ≃L[𝕜]
      OrdinalContinuous 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) :=
    (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜) heq).toContinuousLinearEquiv.trans
      (JLMS.ordinalSpaceSmallRemainder c hc _ ρ hmul hρ)
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  intro hΓ p hp
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  have hp0 : 0 < p.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p.val))) hp
  let E : lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p.val ≃L[𝕜]
      lp (fun _ : Γ => OrdinalContinuous 𝕜 c.ord) p.val :=
    (lpMapEquiv p.val e).trans (lpOrdinalFiniteMultipleEquiv c.ord hκ n p.val hp0)
  have h := corollary_4_10_i_initial_poly 𝕜 Γ hc hΓ p hp
  exact ⟨h.1.of_equiv E.symm, h.2.of_equiv E.symm⟩


end PFP

