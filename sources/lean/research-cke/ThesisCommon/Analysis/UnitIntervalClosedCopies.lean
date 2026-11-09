import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas

/-! The countable closed-cover indivisibility of [0,1] used by LPCK.
Baire gives relative interior, then a nondegenerate closed subinterval.
The homeomorphism onto this closed copy is constructed explicitly. -/
noncomputable section
namespace ThesisCommon

def unitSubintervalRealHomeomorph (a b : UnitInterval) :
    Set.Icc a b ≃ₜ Set.Icc (a : ℝ) (b : ℝ) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, ⟨a.property.1.trans x.property.1, x.property.2.trans b.property.2⟩⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def unitSubintervalHomeomorph (a b : UnitInterval) (hab : a < b) :
    UnitInterval ≃ₜ Set.Icc a b :=
  (iccHomeoI (a : ℝ) (b : ℝ) hab).symm.trans (unitSubintervalRealHomeomorph a b).symm

theorem unitInterval_closed_cover_contains_interval {ι : Type*} [Countable ι]
    (A : ι → Set UnitInterval) (hA : ∀ i, IsClosed (A i))
    (hcover : ⋃ i, A i = Set.univ) :
    ∃ (i : ι) (a b : UnitInterval), a < b ∧ Set.Icc a b ⊆ A i := by
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hA hcover
  obtain ⟨a, b, hab, hsub⟩ := isOpen_interior.exists_Ioo_subset hi
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  refine ⟨i, c, d, hcd, ?_⟩
  intro x hx
  exact interior_subset (hsub ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩)

theorem unitInterval_closed_cover_contains_copy {ι : Type*} [Countable ι]
    (A : ι → Set UnitInterval) (hA : ∀ i, IsClosed (A i))
    (hcover : ⋃ i, A i = Set.univ) :
    ∃ (i : ι) (B : Set UnitInterval), IsClosed B ∧ B ⊆ A i ∧ Nonempty (UnitInterval ≃ₜ B) := by
  obtain ⟨i, a, b, hab, hsub⟩ := unitInterval_closed_cover_contains_interval A hA hcover
  exact ⟨i, Set.Icc a b, isClosed_Icc, hsub, ⟨unitSubintervalHomeomorph a b hab⟩⟩

end ThesisCommon
