import JLMS.OrdinalSupportBounds
import Mathlib.SetTheory.Ordinal.Topology

/-!
# Common points of countably many closed cofinal sets

Countable iteration stays below an endpoint of uncountable cofinality. Taking
successive bounds of one point from every set yields a common limit point.
This supplies simultaneous block boundaries for countably many operators.
-/

noncomputable section
namespace JLMS
universe u

theorem exists_common_closed_ordinal_above {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (s : ℕ → Set Ordinal.{u})
    (hclosed : ∀ n, IsClosed (s n))
    (hcofinal : ∀ n β, β < α → ∃ δ < α, β < δ ∧ δ ∈ s n)
    (β : Ordinal.{u}) (hβ : β < α) :
    ∃ δ < α, β < δ ∧ ∀ n, δ ∈ s n := by
  let choosePoint (n : ℕ) (a : Set.Iio α) : Ordinal.{u} :=
    Classical.choose (hcofinal n a.val a.prop)
  have hp (n : ℕ) (a : Set.Iio α) :
      choosePoint n a < α ∧ a.val < choosePoint n a ∧ choosePoint n a ∈ s n :=
    Classical.choose_spec (hcofinal n a.val a.prop)
  let next (a : Set.Iio α) : Set.Iio α :=
    ⟨⨆ n, choosePoint n a,
      Ordinal.iSup_lt_ord_lift (by simpa using hα) (fun n => (hp n a).1)⟩
  have hnext (a : Set.Iio α) : a.val < (next a).val :=
    (hp 0 a).2.1.trans_le (Ordinal.le_iSup (fun n => choosePoint n a) 0)
  let a (m : ℕ) := next^[m] ⟨β, hβ⟩
  let b (m : ℕ) := (a m).val
  have hstep (m : ℕ) : a (m + 1) = next (a m) :=
    Function.iterate_succ_apply' next m ⟨β, hβ⟩
  let δ := ⨆ m, b m
  have hδ : δ < α := Ordinal.iSup_lt_ord_lift (by simpa using hα) (fun m => (a m).prop)
  have hβδ : β < δ := (hnext ⟨β, hβ⟩).trans_le
    (by simpa only [b, hstep] using Ordinal.le_iSup b 1)
  refine ⟨δ, hδ, hβδ, ?_⟩
  intro n
  have hs : (⨆ m, choosePoint n (a m)) = δ := by
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro m
      have hh := Ordinal.le_iSup (fun k => choosePoint k (a m)) n
      change choosePoint n (a m) ≤ (next (a m)).val at hh
      rw [← hstep] at hh
      exact hh.trans (Ordinal.le_iSup b (m + 1))
    · apply Ordinal.iSup_le
      intro m
      exact (hp n (a m)).2.1.le.trans
        (Ordinal.le_iSup (fun k => choosePoint n (a k)) m)
  rw [← hs]
  have hsub : Set.range (fun m : ℕ => choosePoint n (a m)) ⊆ s n := by
    rintro _ ⟨m, rfl⟩
    exact (hp n (a m)).2.2
  exact (hclosed n).closure_subset (closure_mono hsub
    (csSup_mem_closure (Set.range_nonempty _) (Ordinal.bddAbove_range _)))

/-- Cofinality below an initial regular ordinal bounds its set enumerator. -/
theorem enumOrd_lt_of_cofinal_below {α : Ordinal.{u}} {s : Set Ordinal.{u}}
    (hsmall : ∀ ν < α, ν.card < α.cof)
    (hcofinal : ∀ β < α, ∃ δ < α, β < δ ∧ δ ∈ s)
    (ν : Ordinal.{u}) (hν : ν < α) : Ordinal.enumOrd s ν < α := by
  have hall : ∀ ν : Ordinal.{u}, ν < α → Ordinal.enumOrd s ν < α := by
    intro ν
    induction ν using Ordinal.induction with
    | h ν ih =>
      intro hν
      let b (ξ : Ordinal.{u}) (_ : ξ < ν) := Ordinal.enumOrd s ξ
      have hb : Ordinal.bsup ν b < α := Ordinal.bsup_lt_ord (hsmall ν hν)
        (fun ξ hξ => ih ξ hξ (hξ.trans hν))
      obtain ⟨δ, hδ, hbδ, hδs⟩ := hcofinal (Ordinal.bsup ν b) hb
      exact (Ordinal.enumOrd_le_of_forall_lt hδs
        (fun ξ hξ => (Ordinal.le_bsup b ξ hξ).trans_lt hbδ)).trans_lt hδ
  exact hall ν hν

end JLMS
