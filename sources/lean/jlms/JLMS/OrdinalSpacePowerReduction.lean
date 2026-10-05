import JLMS.OrdinalSpaceAbsorption
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Power normalization in Kislyakov's sufficient classification

Above κ², ordinal logarithm and division give α=κ^γ η+ρ with γ≥2,
0<η<κ and ρ<κ^γ. Additive principality absorbs this remainder at the
level of continuous-function spaces. No classification theorem is used.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordinal_power_quotient_remainder {κ α : Ordinal.{u}}
    (hκ : 1 < κ) (hα : κ ^ (2 : Ordinal) ≤ α) :
    ∃ γ : Ordinal.{u}, 2 ≤ γ ∧ ∃ η : Ordinal.{u}, 0 < η ∧ η < κ ∧
      ∃ ρ < κ ^ γ, α = κ ^ γ * η + ρ := by
  have hα0 : α ≠ 0 := ne_of_gt ((Ordinal.opow_pos 2 (zero_lt_one.trans hκ)).trans_le hα)
  let γ := Ordinal.log κ α
  refine ⟨γ, Ordinal.le_log_of_opow_le hκ hα, α / (κ ^ γ),
    Ordinal.div_opow_log_pos κ hα0, Ordinal.div_opow_log_lt α hκ,
    α % (κ ^ γ), Ordinal.mod_lt _ (Ordinal.opow_pos γ (zero_lt_one.trans hκ)).ne', ?_⟩
  exact (Ordinal.div_add_mod α (κ ^ γ)).symm

theorem add_eq_of_principal_le {β α ρ : Ordinal.{u}}
    (hβ : Ordinal.Principal (· + ·) β) (hβα : β ≤ α) (hρ : ρ < β) : ρ + α = α := by
  have hr : ρ + β = β := Ordinal.principal_add_iff_add_left_eq_self.mp hβ ρ hρ
  calc
    ρ + α = ρ + (β + (α - β)) := congrArg (ρ + ·) (Ordinal.add_sub_cancel_of_le hβα).symm
    _ = β + (α - β) := by rw [← add_assoc, hr]
    _ = α := Ordinal.add_sub_cancel_of_le hβα

def ordinalSpacePowerRemainder (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ η ρ : Ordinal.{u}) (hγ : 1 ≤ γ) (hη : 0 < η) (hρ : ρ < c.ord ^ γ) :
    OrdinalC 𝕜 (c.ord ^ γ * η + ρ) ≃L[𝕜] OrdinalC 𝕜 (c.ord ^ γ * η) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by simpa using Cardinal.ord_le_ord.mpr hc
  have hpow : c.ord ≤ c.ord ^ γ := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le hκ) hγ
  have hprod : c.ord ^ γ ≤ c.ord ^ γ * η := by
    simpa only [mul_one] using mul_le_mul_left' (Order.one_le_iff_pos.mpr hη) (c.ord ^ γ)
  apply ordinalSpaceAbsorbRight _ ρ ((hκ.trans hpow).trans hprod)
  exact add_eq_of_principal_le
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) γ) hprod hρ

theorem exists_ordinalSpace_power_normalForm (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α : Ordinal.{u}) (hα : c.ord ^ (2 : Ordinal) ≤ α) :
    ∃ γ : Ordinal.{u}, 2 ≤ γ ∧ ∃ η : Ordinal.{u}, 0 < η ∧ η < c.ord ∧
      Nonempty (OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord ^ γ * η)) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (by simpa using Cardinal.ord_le_ord.mpr hc)
  obtain ⟨γ, hγ, η, hη, hηκ, ρ, hρ, he⟩ := exists_ordinal_power_quotient_remainder hκ hα
  refine ⟨γ, hγ, η, hη, hηκ, ⟨?_⟩⟩
  exact (ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
    (ordinalSpacePowerRemainder c hc γ η ρ (one_le_two.trans hγ) hη hρ)

theorem exists_ordinalSpace_power_normalForm_cardBound (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{u}) (hcard : α.card ≤ c)
    (hα : c.ord ^ (2 : Ordinal) ≤ α) :
    ∃ γ : Ordinal.{u}, 2 ≤ γ ∧ γ.card ≤ c ∧
      ∃ η : Ordinal.{u}, 0 < η ∧ η < c.ord ∧
        Nonempty (OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord ^ γ * η)) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (by simpa using Cardinal.ord_le_ord.mpr hc)
  have hκ0 : 0 < c.ord := zero_lt_one.trans hκ
  have hα0 : α ≠ 0 := ne_of_gt ((Ordinal.opow_pos 2 hκ0).trans_le hα)
  let γ := Ordinal.log c.ord α
  let η := α / (c.ord ^ γ)
  let ρ := α % (c.ord ^ γ)
  have hγ : (2 : Ordinal) ≤ γ := Ordinal.le_log_of_opow_le hκ hα
  have hγcard : γ.card ≤ c :=
    (Ordinal.card_le_card (Ordinal.log_le_self c.ord α)).trans hcard
  have hη : 0 < η := Ordinal.div_opow_log_pos c.ord hα0
  have hηκ : η < c.ord := Ordinal.div_opow_log_lt α hκ
  have hρ : ρ < c.ord ^ γ := Ordinal.mod_lt _ (Ordinal.opow_pos γ hκ0).ne'
  have he : α = c.ord ^ γ * η + ρ := (Ordinal.div_add_mod α (c.ord ^ γ)).symm
  exact ⟨γ, hγ, hγcard, η, hη, hηκ,
    ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
      (ordinalSpacePowerRemainder c hc γ η ρ (one_le_two.trans hγ) hη hρ)⟩⟩

end JLMS
