import PFP.PrincipalOrdinalCoefficientProofs
import PFP.OrdinalSingularInitialEquivalences
import PFP.CountableOrdinalCoefficientProofs

/-! Initial-ordinal coefficient spaces in arbitrary universes. The uncountable
case is an application of the actual principal-rank factorisation theorem and
the ordinal fixed-point identity; the singular reductions use genuine bounded
linear isomorphisms. No regularity hypothesis is imposed on the initial result. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜]

theorem ordinalContinuous_hasUPFP_of_uncountable_initial
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 c.ord) := by
  have hω : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hc
  have h := ordinalContinuous_hasUPFP_of_principal_rank 𝕜 c.ord
    (Ordinal.principal_add_ord hc.le) hω
  exact h.of_equiv (JLMS.ordinalSpaceCongrIsometry (𝕜 := 𝕜)
    (Posets.ordinal_uncountable_initial_omega_power hc)).toContinuousLinearEquiv

theorem ordinalContinuous_hasUPFP_of_infinite_initial
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 c.ord) := by
  rcases hc.eq_or_lt with he | he
  · subst c
    apply ordinalContinuous_hasUPFP_of_countable_infinite 𝕜
    · exact Cardinal.ord_lt_ord.mpr Cardinal.aleph0_lt_aleph_one
    · simp only [Cardinal.ord_aleph0, le_refl]
  · exact ordinalContinuous_hasUPFP_of_uncountable_initial 𝕜 he

theorem ordinalContinuous_hasUPFP_of_singular_below_square
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    {α : Ordinal.{u}} (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 α) :=
  (ordinalContinuous_hasUPFP_of_infinite_initial 𝕜 hc).of_equiv
    (Posets.UniverseSingularInitial.singularInitialBelowSquareEquiv
      (𝕜 := 𝕜) hc hs α hlo hhi).symm

theorem ordinalContinuous_hasUPFP_of_singular_square
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    HasUPFP 𝕜 (OrdinalContinuous 𝕜 (c.ord ^ (2 : Ordinal))) := by
  rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
  apply ordinalContinuous_hasUPFP_of_singular_below_square 𝕜 hc hs
  · calc
      c.ord = c.ord * 1 := (mul_one _).symm
      _ ≤ c.ord * c.ord := mul_le_mul_left'
        (Ordinal.one_lt_omega0.le.trans (Cardinal.omega0_le_ord.mpr hc)) _
  · exact le_rfl

end PFP
