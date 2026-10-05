import Posets.OrdinalIdealTransportHigherMultiples
import Posets.OrdinalIdealTransportSingularBelowSquare

/-! Logarithmic normalization closes the whole finite-exponent interval,
not just the exact ordinal powers. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def initialHigherBelowOmegaEquiv {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    (α : Ordinal.{0}) (hlo : c.ord * c.ord ≤ α) (hhi : α < c.ord ^ Ordinal.omega0) :
    OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord * c.ord) := by
  refine Classical.choice ?_
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le
    (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le)
  have hpow : c.ord ^ (2 : Ordinal) = c.ord * c.ord := by
    rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
  obtain ⟨γ, hγ, η, hη, hηκ, ρ, hρ, heq⟩ :=
    exists_ordinal_power_quotient_remainder (κ := c.ord) (α := α) hκ (by rwa [hpow])
  have hγα : c.ord ^ γ ≤ α := by
    rw [heq]
    exact (Ordinal.le_mul_left _ hη).trans (Ordinal.le_add_right _ _)
  have hγω : γ < Ordinal.omega0 := (Ordinal.opow_lt_opow_iff_right hκ).mp (hγα.trans_lt hhi)
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hγω
  have hm2 : 2 ≤ m := by rw [hm] at hγ; exact_mod_cast hγ
  let n := m - 2
  have hmn : m = n + 2 := (Nat.sub_add_cancel hm2).symm
  have e : OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord ^ γ * η) :=
    (ordinalSpaceCongrIsometry (𝕜 := 𝕜) heq).toContinuousLinearEquiv.trans
      (ordinalSpacePowerRemainder c hu.le γ η ρ (one_le_two.trans hγ) hη hρ)
  rw [hm, hmn] at e
  exact ⟨e.trans (initialHigherFinitePowerMultipleEquiv hu n η hη hηκ)⟩

theorem initialHigherBelowOmega_hasUPFP {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord * c.ord ≤ α) (hhi : α < c.ord ^ Ordinal.omega0) :
    HasUPFP 𝕜 (OrdinalSpace 𝕜 α) := by
  have hsquare : HasUPFP 𝕜 (OrdinalSpace 𝕜 (c.ord * c.ord)) := by
    by_cases hc : c.IsRegular
    · exact regularInitialSquare_hasUPFP hc hu
    · have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le
        (by simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le)
      exact singularInitialBelowSquare_hasUPFP hu.le hc (Ordinal.le_mul_left _ hκ) le_rfl
  exact hsquare.of_equiv (initialHigherBelowOmegaEquiv hu α hlo hhi).symm

theorem proposition_3_1_uncountable_belowOmegaPower
    {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c)
    {α : Ordinal.{0}} (hlo : c.ord ≤ α) (hhi : α < c.ord ^ Ordinal.omega0) :
    Proposition_3_1 𝕜 α := by
  by_cases hsq : α < c.ord * c.ord
  · by_cases hc : c.IsRegular
    · exact proposition_3_1_regular_belowSquare hc hu hlo hsq
    · exact proposition_3_1_singular_belowSquare hu.le hc hlo hsq.le
  · intro _
    letI : Nonempty (Set.Icc (0 : Ordinal.{0}) α) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
    have h := uniqueMaximal_of_hasPFP
      (initialHigherBelowOmega_hasUPFP (𝕜 := 𝕜) hu (le_of_not_gt hsq) hhi).hasPFP
    exact ⟨h.2, fun _ => h.1⟩

end Posets
