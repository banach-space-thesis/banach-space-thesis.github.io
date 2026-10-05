import ThesisCommon.Analysis.BooleanRelativeHull
import Mathlib.Order.Zorn

/-! Qualitative relative splitting can be extended to a partition whose two
members both have full relative support.  Suprema and least covers are actual
inputs; the theorem constructs the partition by Zorn's lemma. -/
noncomputable section
open Set
namespace ThesisCommon
variable {B : Type*} [BooleanAlgebra B]

theorem exists_boolean_partition_same_relativeHull
    (hSup : ∀ s : Set B, ∃ b, IsLUB s b)
    (S : BooleanSubalgebra B) (H : B → B)
    (hH : ∀ a, H a ∈ S ∧ a ≤ H a ∧ ∀ b ∈ S, a ≤ b → H a ≤ b)
    (a : B)
    (hsplit : ∀ b : B, b ≠ ⊥ → b ≤ a →
      ∃ u v : B, u ≤ b ∧ v ≤ b ∧ Disjoint u v ∧ u ≠ ⊥ ∧ v ≠ ⊥ ∧ H u = H v) :
    ∃ u v : B, u ⊔ v = a ∧ Disjoint u v ∧ H u = H a ∧ H v = H a := by
  classical
  let P : Set (B × B) := {p | p.1 ≤ a ∧ p.2 ≤ a ∧ Disjoint p.1 p.2 ∧ H p.1 = H p.2}
  have hchain : ∀ c ⊆ P, IsChain (· ≤ ·) c → ∃ p ∈ P, ∀ q ∈ c, q ≤ p := by
    intro c hc hcc
    obtain ⟨u, hu⟩ := hSup (Prod.fst '' c)
    obtain ⟨v, hv⟩ := hSup (Prod.snd '' c)
    have huv : Disjoint u v := by
      apply le_compl_iff_disjoint_right.mp
      apply hu.2
      rintro _ ⟨p, hp, rfl⟩
      have hvp : v ≤ p.1ᶜ := by
        apply hv.2
        rintro _ ⟨q, hq, rfl⟩
        have hd : Disjoint p.1 q.2 := by
          rcases hcc.total hp hq with hpq | hqp
          · exact (hc hq).2.2.1.mono_left hpq.1
          · exact (hc hp).2.2.1.mono_right hqp.2
        exact hd.le_compl_left
      simpa only [compl_compl] using compl_le_compl hvp
    have hHu : H u ≤ H v := by
      apply (hH u).2.2 _ (hH v).1
      apply hu.2
      rintro _ ⟨p, hp, rfl⟩
      calc
        p.1 ≤ H p.1 := (hH _).2.1
        _ = H p.2 := (hc hp).2.2.2
        _ ≤ H v := booleanRelativeHull_mono S H hH (hv.1 ⟨p, hp, rfl⟩)
    have hHv : H v ≤ H u := by
      apply (hH v).2.2 _ (hH u).1
      apply hv.2
      rintro _ ⟨p, hp, rfl⟩
      calc
        p.2 ≤ H p.2 := (hH _).2.1
        _ = H p.1 := (hc hp).2.2.2.symm
        _ ≤ H u := booleanRelativeHull_mono S H hH (hu.1 ⟨p, hp, rfl⟩)
    refine ⟨(u, v), ⟨?_, ?_, huv, hHu.antisymm hHv⟩, ?_⟩
    · exact hu.2 (by rintro _ ⟨p, hp, rfl⟩; exact (hc hp).1)
    · exact hv.2 (by rintro _ ⟨p, hp, rfl⟩; exact (hc hp).2.1)
    · intro p hp
      exact ⟨hu.1 ⟨p, hp, rfl⟩, hv.1 ⟨p, hp, rfl⟩⟩
  obtain ⟨p, hp, hmax⟩ := zorn_le₀ P hchain
  have hcover : p.1 ⊔ p.2 = a := by
    apply le_antisymm (sup_le hp.1 hp.2.1)
    by_contra hbad
    have hr : a \ (p.1 ⊔ p.2) ≠ ⊥ := fun hr => hbad (sdiff_eq_bot_iff.mp hr)
    obtain ⟨u, v, hu, hv, huv, hune, _, heq⟩ := hsplit _ hr sdiff_le
    have hup : Disjoint u (p.1 ⊔ p.2) := disjoint_sdiff_self_left.mono_left hu
    have hvp : Disjoint v (p.1 ⊔ p.2) := disjoint_sdiff_self_left.mono_left hv
    have hnew : (p.1 ⊔ u, p.2 ⊔ v) ∈ P := by
      refine ⟨sup_le hp.1 (hu.trans sdiff_le), sup_le hp.2.1 (hv.trans sdiff_le), ?_, ?_⟩
      · exact disjoint_sup_left.mpr ⟨disjoint_sup_right.mpr
          ⟨hp.2.2.1, hvp.symm.mono_left le_sup_left⟩,
          disjoint_sup_right.mpr ⟨hup.mono_right le_sup_right, huv⟩⟩
      · rw [booleanRelativeHull_sup S H hH, booleanRelativeHull_sup S H hH,
          hp.2.2.2, heq]
    have hm := hmax hnew (show p ≤ (p.1 ⊔ u, p.2 ⊔ v) from ⟨le_sup_left, le_sup_left⟩)
    have hule : u ≤ p.1 := le_sup_right.trans hm.1
    exact hune (disjoint_self.mp ((hup.mono_right le_sup_left).mono_right hule))
  have hHcover : H a = H p.1 := by
    rw [← hcover, booleanRelativeHull_sup S H hH, hp.2.2.2, sup_idem]
  exact ⟨p.1, p.2, hcover, hp.2.2.1, hHcover.symm, hp.2.2.2.symm.trans hHcover.symm⟩

end ThesisCommon
