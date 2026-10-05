import UPFP.MainStatements
import LPCK.OrdinalDualCotype
import LPCK.CountableOrdinalSequence
import LPCK.InitialPowerSequence
import LPCK.CountableExponentSequence
import LPCK.RegularInitialSequence
import LPCK.AllOrdinalSmallUniverse
import LPCK.AllOrdinalTheorem

/-! The original all-ordinal corollary and its specialised applications. -/
noncomputable section
namespace UPFP
open ThesisCommon
section AllScalars
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_1_5_proof (α : Ordinal) : Corollary_1_5 𝕜 α :=
  LPCK.theorem_1_1_proof 𝕜 α ⟨1, le_rfl⟩

theorem corollary_1_5_of_base (α : Ordinal)
    (hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 α)) : Corollary_1_5 𝕜 α := by
  have h := LPCK.ordinal_ellOne_hasUPFP_of_base α hX
  exact ⟨h, h.lp_isPrimary⟩

theorem corollary_1_5_countable {α : Ordinal}
    (hα : α < (Cardinal.aleph 1).ord) : Corollary_1_5 𝕜 α :=
  LPCK.theorem_1_1_countable hα ⟨1, le_rfl⟩

theorem corollary_1_5_smallOrdinal (α : Ordinal.{0}) : Corollary_1_5 𝕜 α :=
  LPCK.theorem_1_1_smallOrdinal 𝕜 α ⟨1, le_rfl⟩

end AllScalars
section SmallScalar
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

theorem corollary_1_5_initial_below_countable_exponent (c : Cardinal.{0})
    (hc : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ^ (2 : Ordinal.{0}) ≤ α)
    (hhi : α < c.ord ^ (Cardinal.aleph 1).ord) : Corollary_1_5 𝕜 α :=
  LPCK.theorem_1_1_initial_below_countable_exponent c hc α hlo hhi ⟨1, le_rfl⟩

theorem corollary_1_5_initial_higher_countable_cofinal
    (c : Cardinal) (hc : Cardinal.aleph0 < c) (η : Ordinal) (hη : η ≠ 0)
    (hcard : (Ordinal.omega0 ^ η).card ≤ c)
    (hcf : (c.ord * Ordinal.omega0 ^ η).cof = Cardinal.aleph0) :
    Corollary_1_5 𝕜 (c.ord ^ (Ordinal.omega0 ^ η)) :=
  LPCK.theorem_1_1_initial_higher_countable_cofinal c hc η hη hcard hcf ⟨1, le_rfl⟩

theorem corollary_1_5_regular_initial_below_omega_multiple (c : Cardinal.{0})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (α : Ordinal.{0})
    (hlo : c.ord ≤ α) (hhi : α < c.ord * Ordinal.omega0) : Corollary_1_5 𝕜 α :=
  LPCK.theorem_1_1_regular_initial_below_omega_multiple c hc hu α hlo hhi ⟨1, le_rfl⟩

theorem corollary_1_5_exceptional_equiv (c : Cardinal.{0})
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) (α : Ordinal)
    (e : OrdinalContinuous 𝕜 α ≃L[𝕜]
      OrdinalContinuous 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal))) : Corollary_1_5 𝕜 α := by
  have h := (LPCK.theorem_1_1_regular_initial_finite_multiple (𝕜 := 𝕜)
    c hc hu n ⟨1, le_rfl⟩).1.of_equiv (lpMapEquiv 1 e.symm)
  exact ⟨h, h.lp_isPrimary⟩

theorem corollary_1_5_initial_below_countable_exponent_full (c : Cardinal.{0})
    (hu : Cardinal.aleph0 < c) (α : Ordinal.{0}) (hlo : c.ord ≤ α)
    (hhi : α < c.ord ^ (Cardinal.aleph 1).ord) : Corollary_1_5 𝕜 α := by
  by_cases hsq : α < c.ord * c.ord
  · by_cases hc : c.IsRegular
    · by_cases hsmall : α < c.ord * Ordinal.omega0
      · exact corollary_1_5_regular_initial_below_omega_multiple c hc hu α hlo hsmall
      · exact corollary_1_5_of_base α
          (Posets.initialOrdinalInfiniteQuotient_hasUPFP hc hu (le_of_not_gt hsmall) hsq)
    · exact corollary_1_5_of_base α
        (Posets.singularInitialBelowSquare_hasUPFP hu.le hc hlo hsq.le)
  · apply corollary_1_5_initial_below_countable_exponent c hu α _ hhi
    have he : c.ord ^ (2 : Ordinal.{0}) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    rw [he]
    exact le_of_not_gt hsq

end SmallScalar
end UPFP
