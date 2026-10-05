import JLMS.OrdinalSpaceEndpointZero
import JLMS.OrdinalSpaceFinitePower
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Absorbing small ordinal remainders

Kislyakov's equations (1.1)–(1.3) remove the remainder below the initial
ordinal in the classification proof. Finite remainders are absorbed by
moving finitely many isolated points; infinite remainders use the two
clopen summands and commutation of their product.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalSuccessorLeft (α : Ordinal.{u}) :
    OrdinalInterval α → OrdinalInterval (Order.succ α) :=
  fun x => ⟨x.val, x.property.1, x.property.2.trans (Order.le_succ α)⟩

def ordinalSuccessorLast (α : Ordinal.{u}) :
    OrdinalInterval (0 : Ordinal.{u}) → OrdinalInterval (Order.succ α) :=
  fun _ => ⟨Order.succ α, Ordinal.zero_le _, le_rfl⟩

theorem ordinalSuccessor_bijective (α : Ordinal.{u}) :
    Function.Bijective (Sum.elim (ordinalSuccessorLeft α) (ordinalSuccessorLast α)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        exact Subtype.ext (congrArg (fun z : OrdinalInterval (Order.succ α) => z.val) h)
      | inr y =>
        have he := congrArg (fun z : OrdinalInterval (Order.succ α) => z.val) h
        change x.val = Order.succ α at he
        exact False.elim ((Order.lt_succ α).not_ge (he ▸ x.property.2))
    | inr x =>
      cases y with
      | inl y =>
        have he := congrArg (fun z : OrdinalInterval (Order.succ α) => z.val) h
        change Order.succ α = y.val at he
        exact False.elim ((Order.lt_succ α).not_ge (he.symm ▸ y.property.2))
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact le_antisymm (x.property.2.trans y.property.1) (y.property.2.trans x.property.1)
  · intro y
    by_cases hy : y.val ≤ α
    · exact ⟨.inl ⟨y.val, y.property.1, hy⟩, Subtype.ext rfl⟩
    · refine ⟨.inr ⟨0, le_rfl, le_rfl⟩, Subtype.ext ?_⟩
      exact le_antisymm (Order.succ_le_iff.mpr (lt_of_not_ge hy)) y.property.2

def ordinalSuccessorInterval (α : Ordinal.{u}) :
    OrdinalInterval α ⊕ OrdinalInterval (0 : Ordinal.{u}) ≃ₜ OrdinalInterval (Order.succ α) :=
  let h : Continuous (Sum.elim (ordinalSuccessorLeft α) (ordinalSuccessorLast α)) :=
    (continuous_subtype_val.subtype_mk _).sumElim continuous_const
  (Equiv.ofBijective _ (ordinalSuccessor_bijective α)).toHomeomorphOfContinuousClosed h h.isClosedMap

def ordinalSpaceSuccessorEquiv (α : Ordinal.{u}) :
    OrdinalC 𝕜 (Order.succ α) ≃L[𝕜] OrdinalC 𝕜 α × 𝕜 :=
  (continuousMapDomainIsometry (𝕜 := 𝕜) (ordinalSuccessorInterval α)).toContinuousLinearEquiv.trans
    (continuousMapSumIsometry.toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr ordinalZeroEvaluation))

def ordinalSpaceAbsorbSuccessor (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    OrdinalC 𝕜 (Order.succ α) ≃L[𝕜] OrdinalC 𝕜 α :=
  (ordinalSpaceSuccessorEquiv α).trans ((ContinuousLinearEquiv.prodComm 𝕜 _ _).trans
    (Classical.choose (exists_ordinalIsolatedSplit (𝕜 := 𝕜) α hα)).symm)

def ordinalSpaceAbsorbNat (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) (n : ℕ) :
    OrdinalC 𝕜 (α + n) ≃L[𝕜] OrdinalC 𝕜 α := by
  induction n with
  | zero => exact (ordinalSpaceCongrIsometry (by simp : α + (0 : ℕ) = α)).toContinuousLinearEquiv
  | succ n e =>
    have heq : α + (n.succ : Ordinal) = Order.succ (α + n) := by
      rw [Ordinal.natCast_succ, Ordinal.add_succ]
    exact (ordinalSpaceCongrIsometry heq).toContinuousLinearEquiv.trans
      ((ordinalSpaceAbsorbSuccessor (α + n) (hα.trans (Ordinal.le_add_right α n))).trans e)

def ordinalSpaceAddCommEquiv (α β : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) (hβ : Ordinal.omega0 ≤ β) :
    OrdinalC 𝕜 (α + β) ≃L[𝕜] OrdinalC 𝕜 (β + α) :=
  (ordinalSpaceAddIsometry α β hβ).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.prodComm 𝕜 _ _).trans
      (ordinalSpaceAddIsometry β α hα).toContinuousLinearEquiv.symm)

def ordinalSpaceAbsorbRight (α ρ : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α)
    (hρα : ρ + α = α) : OrdinalC 𝕜 (α + ρ) ≃L[𝕜] OrdinalC 𝕜 α := by
  classical
  by_cases hρ : Ordinal.omega0 ≤ ρ
  · exact (ordinalSpaceAddCommEquiv α ρ hα hρ).trans
      (ordinalSpaceCongrIsometry hρα).toContinuousLinearEquiv
  · have hex := Ordinal.lt_omega0.mp (lt_of_not_ge hρ)
    let n := Classical.choose hex
    have hn : ρ = (n : Ordinal) := Classical.choose_spec hex
    exact (ordinalSpaceCongrIsometry (congrArg (α + ·) hn)).toContinuousLinearEquiv.trans
      (ordinalSpaceAbsorbNat α hα n)

theorem small_add_eq_of_initial_le (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α ρ : Ordinal.{u}) (hα : c.ord ≤ α) (hρ : ρ < c.ord) : ρ + α = α := by
  have hr : ρ + c.ord = c.ord :=
    Ordinal.principal_add_iff_add_left_eq_self.mp (Ordinal.principal_add_ord hc) ρ hρ
  calc
    ρ + α = ρ + (c.ord + (α - c.ord)) :=
      congrArg (ρ + ·) (Ordinal.add_sub_cancel_of_le hα).symm
    _ = c.ord + (α - c.ord) := by rw [← add_assoc, hr]
    _ = α := Ordinal.add_sub_cancel_of_le hα

/-- Remove the remainder below the initial ordinal, as in Kislyakov Lemma 3.4. -/
def ordinalSpaceSmallRemainder (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (α ρ : Ordinal.{u}) (hα : c.ord ≤ α) (hρ : ρ < c.ord) :
    OrdinalC 𝕜 (α + ρ) ≃L[𝕜] OrdinalC 𝕜 α := by
  have hκ : Ordinal.omega0 ≤ c.ord := by simpa using Cardinal.ord_le_ord.mpr hc
  exact ordinalSpaceAbsorbRight α ρ (hκ.trans hα)
    (small_add_eq_of_initial_le c hc α ρ hα hρ)

end JLMS
