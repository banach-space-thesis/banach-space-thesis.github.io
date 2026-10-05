import JLMS.FiniteAutomaticContinuity
import JLMS.OrdinalScattered

/-!
# The finite ordinal case of Theorem 1.3

The inequality α < ω alone implies that [0,α] is finite. This discharges
the finite-dimensional branch of Section 9 from its original hypothesis.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_ordinalInterval_of_lt_omega0 {α : Ordinal.{u}} (hα : α < Ordinal.omega0) :
    Finite (OrdinalInterval α) := by
  have hs : Order.succ α < Ordinal.omega0 := Ordinal.isSuccLimit_omega0.succ_lt hα
  haveI : Finite (Set.Iio (Order.succ α)) := Cardinal.mk_lt_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph0, Ordinal.card_lt_aleph0]
    exact hs)
  exact Finite.of_injective
    (fun x : OrdinalInterval α => (⟨x.val, Order.lt_succ_iff.mpr x.property.2⟩ :
      Set.Iio (Order.succ α)))
    (fun _ _ h => Subtype.ext (congrArg (fun x : Set.Iio (Order.succ α) => x.val) h))

theorem theorem_1_3_of_lt_omega0 (α : Ordinal.{u}) (hα : α < Ordinal.omega0) :
    Theorem_1_3 𝕜 α := by
  letI := finite_ordinalInterval_of_lt_omega0 hα
  exact theorem_1_3_of_finite α

end JLMS
