import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-! The actual set mappings and free sets used in the uncountable-sum arguments.
These definitions impose no regularity or cofinality assumption. The two-sided
condition refers to inverse incidence fibres, not inverse images of singleton
sets under the function with codomain `Set Γ`. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

/-- The manuscript's convention that a set mapping does not contain its argument. -/
def IsSetMapping (F : Γ → Set Γ) : Prop := ∀ γ, γ ∉ F γ

/-- Both directed interactions vanish between every distinct pair in the set. -/
def IsSetMappingFree (F : Γ → Set Γ) (H : Set Γ) : Prop :=
  ∀ α ∈ H, ∀ β ∈ H, α ≠ β → α ∉ F β ∧ β ∉ F α

/-- Outgoing values and incoming incidence fibres are both countable. -/
def HasTwoSidedCountableValues (F : Γ → Set Γ) : Prop :=
  (∀ γ, (F γ).Countable) ∧ (∀ γ, {δ | γ ∈ F δ}.Countable)

/-- A countable cover of a set of cardinality κ has a full-size member when
cf(κ)>aleph-zero. The cover need not be disjoint and κ need not be regular. -/
theorem countable_union_cofinal_pigeonhole {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hcof : Cardinal.aleph0 < κ.ord.cof)
    (S : Set Γ) (hS : Cardinal.mk S = κ) (A : ℕ → Set Γ)
    (hA : S = ⋃ n, A n) : ∃ n, Cardinal.mk (A n) = κ := by
  classical
  have hex (x : S) : ∃ n, x.val ∈ A n := by
    apply Set.mem_iUnion.mp
    rw [← hA]
    exact x.property
  choose n hn using hex
  let f : S → ULift.{u} ℕ := fun x => ⟨n x⟩
  have hfcard : Cardinal.mk (ULift.{u} ℕ) < (Cardinal.mk S).ord.cof := by
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, hS] using hcof
  obtain ⟨j, hj⟩ := Cardinal.infinite_pigeonhole f (hS ▸ hκ) hfcard
  refine ⟨j.down, le_antisymm ?_ ?_⟩
  · rw [← hS]
    apply Cardinal.mk_le_mk_of_subset
    rw [hA]
    exact Set.subset_iUnion A j.down
  · rw [← hS, ← hj]
    let g : (f ⁻¹' {j}) → A j.down := fun x => ⟨x.val.val, by
      have hx : f x.val = j := x.property
      have he : n x.val = j.down := congrArg ULift.down hx
      rw [← he]
      exact hn x.val⟩
    apply Cardinal.mk_le_of_injective (f := g)
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A j.down => z.val) h

/-- The genuine initial ordinal of cardinality aleph-one, represented in the
same universe as its cardinal, with its canonical well order. -/
abbrev OmegaOneIndex : Type u := (Cardinal.aleph 1 : Cardinal.{u}).ord.toType

/-- The concrete counterexample from Remark 4.23: all strict predecessors. -/
def omegaOnePredecessors (α : OmegaOneIndex.{u}) : Set OmegaOneIndex.{u} := Set.Iio α

theorem mk_omegaOneIndex : Cardinal.mk OmegaOneIndex.{u} = Cardinal.aleph 1 := by
  exact Cardinal.mk_ord_toType _

theorem omegaOnePredecessors_isSetMapping : IsSetMapping omegaOnePredecessors.{u} := by
  intro α
  exact lt_irrefl α

theorem omegaOnePredecessors_countable (α : OmegaOneIndex.{u}) :
    (omegaOnePredecessors α).Countable := by
  apply (Cardinal.countable_iff_lt_aleph_one _).mpr
  exact Cardinal.mk_Iio_ord_toType α

/-- In fact every free subset of the predecessor mapping has at most one point. -/
theorem omegaOnePredecessors_free_subsingleton (H : Set OmegaOneIndex.{u})
    (hH : IsSetMappingFree omegaOnePredecessors H) : H.Subsingleton := by
  intro α hα β hβ
  by_contra hne
  obtain ⟨hab, hba⟩ := hH α hα β hβ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hab hlt
  · exact hba hgt

end ThesisCommon
