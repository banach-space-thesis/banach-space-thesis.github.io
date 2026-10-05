import Mathlib.Order.BooleanSubalgebra

/-! Algebraic properties of least covers in a Boolean subalgebra, and the
actual relative splitting step they imply.  The least-cover input is
constructed for closed AL fragment subalgebras in
`ALFragmentOrderCompleteness`; it is not a classification hypothesis. -/
namespace ThesisCommon
variable {B : Type*} [BooleanAlgebra B]
variable (S : BooleanSubalgebra B) (H : B → B)
variable (hH : ∀ a, H a ∈ S ∧ a ≤ H a ∧ ∀ b ∈ S, a ≤ b → H a ≤ b)
include hH

theorem booleanRelativeHull_mono : Monotone H := by
  intro a b hab
  exact (hH a).2.2 (H b) (hH b).1 (hab.trans (hH b).2.1)

theorem booleanRelativeHull_bot : H ⊥ = ⊥ :=
  bot_unique ((hH ⊥).2.2 ⊥ S.bot_mem le_rfl)

theorem booleanRelativeHull_eq_bot_iff (a : B) : H a = ⊥ ↔ a = ⊥ := by
  constructor
  · intro ha
    exact bot_unique ((hH a).2.1.trans_eq ha)
  · rintro rfl
    exact booleanRelativeHull_bot S H hH

theorem booleanRelativeHull_sup (a b : B) : H (a ⊔ b) = H a ⊔ H b := by
  apply le_antisymm
  · exact (hH (a ⊔ b)).2.2 _ (S.sup_mem (hH a).1 (hH b).1)
      (sup_le_sup (hH a).2.1 (hH b).2.1)
  · exact sup_le (booleanRelativeHull_mono S H hH le_sup_left)
      (booleanRelativeHull_mono S H hH le_sup_right)

theorem booleanRelativeHull_inf_of_mem (a : B) {b : B} (hb : b ∈ S) :
    H (a ⊓ b) = H a ⊓ b := by
  apply le_antisymm
  · exact (hH (a ⊓ b)).2.2 (H a ⊓ b) (S.inf_mem (hH a).1 hb)
      (inf_le_inf_right b (hH a).2.1)
  · have hcover : a ≤ H (a ⊓ b) ⊔ bᶜ := by
      calc
        a = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
        _ ≤ H (a ⊓ b) ⊔ bᶜ := sup_le_sup (hH (a ⊓ b)).2.1 inf_le_right
    have h := (hH a).2.2 _ (S.sup_mem (hH (a ⊓ b)).1 (S.compl_mem hb)) hcover
    calc
      H a ⊓ b ≤ (H (a ⊓ b) ⊔ bᶜ) ⊓ b := inf_le_inf_right b h
      _ ≤ H (a ⊓ b) := by rw [inf_sup_right, compl_inf_self, sup_bot_eq]; exact inf_le_left

/-- Failure of relative atomicity gives two disjoint subelements having the
same nonzero least cover in the subalgebra. -/
theorem exists_disjoint_same_booleanRelativeHull {a b : B} (hba : b ≤ a)
    (hb : ∀ s ∈ S, b ≠ a ⊓ s) :
    ∃ u v : B, u ≤ a ∧ v ≤ a ∧ Disjoint u v ∧
      H u = H v ∧ H u ≠ ⊥ := by
  let c := a \ b
  have hbc : Disjoint b c := disjoint_sdiff_self_right
  have hac : a = b ⊔ c := by exact (sup_sdiff_cancel_right hba).symm
  have hd : H b ⊓ H c ≠ ⊥ := by
    intro hz
    have hHd : Disjoint (H b) (H c) := disjoint_iff.mpr hz
    have hcb : c ⊓ H b = ⊥ := (hHd.symm.mono_left (hH c).2.1).eq_bot
    apply hb (H b) (hH b).1
    rw [hac, inf_sup_right, inf_eq_left.mpr (hH b).2.1, hcb, sup_bot_eq]
  let d := H b ⊓ H c
  have hdS : d ∈ S := S.inf_mem (hH b).1 (hH c).1
  have hbu : H (b ⊓ d) = d := by
    rw [booleanRelativeHull_inf_of_mem S H hH b hdS]
    exact inf_eq_right.mpr inf_le_left
  have hcv : H (c ⊓ d) = d := by
    rw [booleanRelativeHull_inf_of_mem S H hH c hdS]
    exact inf_eq_right.mpr inf_le_right
  exact ⟨b ⊓ d, c ⊓ d, inf_le_left.trans hba, inf_le_left.trans sdiff_le,
    hbc.mono inf_le_left inf_le_left, hbu.trans hcv.symm, by rw [hbu]; exact hd⟩

end ThesisCommon
