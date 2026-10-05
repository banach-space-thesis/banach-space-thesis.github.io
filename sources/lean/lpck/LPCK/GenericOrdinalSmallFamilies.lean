/- Universe-polymorphic extension of Posets.OrdinalIdealTransportSmallFamilies. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalSmallDomain
import JLMS.OrdinalClosedIntersections
import JLMS.OrdinalMatrixTailRows

/-! Common cutoffs and closed cofinal intersections for a family whose
cardinality is smaller than the ordinal's cofinality. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192

theorem exists_smallIndex_ordinal_tail {α : Ordinal.{u}} {I : Type u}
    (hα : Cardinal.aleph0 < α.cof) (hI : Cardinal.mk I < α.cof)
    (f : I → OrdinalC 𝕜 α) :
    ∃ β < α, ∀ i, f i ∈ ordinalTailSpace α β := by
  have h (i) := exists_constant_ordinalC_tail hα (f i)
  choose b hb hf using h
  refine ⟨⨆ i, b i, Ordinal.iSup_lt_ord hI hb, ?_⟩
  intro i x hx
  exact hf i x ((Ordinal.le_iSup b i).trans_lt hx)

theorem exists_smallIndex_ordinal_ellOne_cutoff {α : Ordinal.{u}} {I : Type u}
    (hα : Cardinal.aleph0 < α.cof) (hI : Cardinal.mk I < α.cof)
    (a : I → ellOneOn 𝕜 (OrdinalInterval α)) :
    ∃ β < α, ∀ i (x : OrdinalInterval α), β < x.val → x.val < α → a i x = 0 := by
  have h (i) := exists_ordinal_ellOne_cutoff hα (a i)
  choose b hb hf using h
  refine ⟨⨆ i, b i, Ordinal.iSup_lt_ord hI hb, ?_⟩
  intro i x hx hxα
  exact hf i x ((Ordinal.le_iSup b i).trans_lt hx) hxα

theorem exists_smallIndex_closed_ordinal_above {α : Ordinal.{u}} {I : Type u} [Nonempty I]
    (hα : Cardinal.aleph0 < α.cof) (hI : Cardinal.mk I < α.cof)
    (s : I → Set Ordinal.{u}) (hclosed : ∀ i, IsClosed (s i))
    (hcofinal : ∀ i β, β < α → ∃ δ < α, β < δ ∧ δ ∈ s i)
    (β : Ordinal.{u}) (hβ : β < α) :
    ∃ δ < α, β < δ ∧ ∀ i, δ ∈ s i := by
  let choosePoint (i : I) (a : Set.Iio α) : Ordinal.{u} :=
    Classical.choose (hcofinal i a.val a.property)
  have hp (i : I) (a : Set.Iio α) :
      choosePoint i a < α ∧ a.val < choosePoint i a ∧ choosePoint i a ∈ s i :=
    Classical.choose_spec (hcofinal i a.val a.property)
  let next (a : Set.Iio α) : Set.Iio α :=
    ⟨⨆ i, choosePoint i a, Ordinal.iSup_lt_ord hI (fun i => (hp i a).1)⟩
  have hnext (a : Set.Iio α) : a.val < (next a).val :=
    (hp (Classical.choice ‹Nonempty I›) a).2.1.trans_le
      (Ordinal.le_iSup (fun i => choosePoint i a) _)
  let a (m : ℕ) := next^[m] ⟨β, hβ⟩
  let b (m : ℕ) := (a m).val
  have hstep (m : ℕ) : a (m+1) = next (a m) :=
    Function.iterate_succ_apply' next m ⟨β, hβ⟩
  let δ := ⨆ m, b m
  have hδ : δ < α := Ordinal.iSup_lt_ord_lift (by simpa using hα) (fun m => (a m).property)
  have hβδ : β < δ := (hnext ⟨β, hβ⟩).trans_le
    (by simpa only [b, hstep] using Ordinal.le_iSup b 1)
  refine ⟨δ, hδ, hβδ, ?_⟩
  intro i
  have hs : (⨆ m, choosePoint i (a m)) = δ := by
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro m
      have hh := Ordinal.le_iSup (fun j => choosePoint j (a m)) i
      change choosePoint i (a m) ≤ (next (a m)).val at hh
      rw [← hstep] at hh
      exact hh.trans (Ordinal.le_iSup b (m+1))
    · apply Ordinal.iSup_le
      intro m
      exact (hp i (a m)).2.1.le.trans (Ordinal.le_iSup (fun n => choosePoint i (a n)) m)
  rw [← hs]
  have hsub : Set.range (fun m : ℕ => choosePoint i (a m)) ⊆ s i := by
    rintro _ ⟨m, rfl⟩
    exact (hp i (a m)).2.2
  exact (hclosed i).closure_subset (closure_mono hsub
    (csSup_mem_closure (Set.range_nonempty _) (Ordinal.bddAbove_range _)))

end LPCK.GenericOrdinal



