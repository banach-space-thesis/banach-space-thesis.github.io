import PFP.OrdinalLpSeparableRange
import PFP.OrdinalFiniteMultipleAbsorption
import Posets.OrdinalIdealTransportBelowOmegaPower
import ThesisCommon.Analysis.PrimaryIsometry

/-! Corollary 4.10(i) on the existing proved uncountable coefficient range:
κ ≤ α < κ^ω for an uncountable initial ordinal κ. Finite positive multiples
of κ are handled by actual outer-index absorption, even when the coefficient
space itself does not have PFP. This is a partial result, not the unrestricted
Corollary 4.10(i). Posets' analytic coefficient theorems here use small universes. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type) [RCLike 𝕜] (Γ : Type*)
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

theorem corollary_4_10_i_initial {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c) :
    Corollary_4_10_i 𝕜 Γ c.ord :=
  corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ c.ord
    (Posets.infiniteInitialOrdinal_hasUPFP hc)

theorem corollary_4_10_i_initial_finite_quotient {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{0})
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
  have h := corollary_4_10_i_initial 𝕜 Γ hc hΓ p hp
  exact ⟨h.1.of_equiv E.symm, h.2.of_equiv E.symm⟩

theorem corollary_4_10_i_below_initial_omega_power {c : Cardinal.{0}}
    (hu : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ≤ α) (hhi : α < c.ord ^ Ordinal.omega0) :
    Corollary_4_10_i 𝕜 Γ α := by
  by_cases hω : α < c.ord * Ordinal.omega0
  · exact corollary_4_10_i_initial_finite_quotient 𝕜 Γ hu.le α hlo hω
  apply corollary_4_10_i_of_coefficient_hasUPFP 𝕜 Γ α
  by_cases hsq : α < c.ord * c.ord
  · by_cases hc : c.IsRegular
    · exact Posets.initialOrdinalInfiniteQuotient_hasUPFP hc hu (le_of_not_gt hω) hsq
    · exact Posets.singularInitialBelowSquare_hasUPFP hu.le hc hlo hsq.le
  · exact Posets.initialHigherBelowOmega_hasUPFP hu (le_of_not_gt hsq) hhi

end PFP
