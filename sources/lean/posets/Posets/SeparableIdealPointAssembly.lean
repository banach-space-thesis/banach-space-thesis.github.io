import Posets.SeparableIdealOrdinalModel
import Mathlib.Logic.Denumerable

/-! Ordinal gluing at one point of a countable compact metric space. -/
noncomputable section
open Set ThesisCommon Topology
namespace Posets

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Countable K]

omit [CompactSpace K] in
theorem infinite_nonempty_shells_of_not_isOpen_singleton (p : K)
    (hp : ¬ IsOpen ({p} : Set K)) :
    Infinite {n : ℕ // (countableClopenShell p n).Nonempty} := by
  classical
  by_contra h
  haveI : Finite {n : ℕ // (countableClopenShell p n).Nonempty} := not_infinite_iff_finite.mp h
  have hc : IsClosed (⋃ n : {n : ℕ // (countableClopenShell p n).Nonempty},
      countableClopenShell p n.val) :=
    isClosed_iUnion_of_finite fun n => (countableClopenShell_isClopen p n.val).isClosed
  have he : (⋃ n : {n : ℕ // (countableClopenShell p n).Nonempty},
      countableClopenShell p n.val) = ({p} : Set K)ᶜ := by
    ext x
    constructor
    · intro hx hxp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact countableClopenShell_not_mem p n.val (hxp ▸ hn)
    · intro hx
      obtain ⟨n, hn⟩ := countableClopenShell_covers p hx
      exact mem_iUnion.mpr ⟨⟨n, x, hn⟩, hn⟩
  exact hp (by simpa only [he, compl_compl] using hc.isOpen_compl)

theorem hasOrdinalCompactModel_of_nonisolated_point (p : K)
    (hp : ¬ IsOpen ({p} : Set K))
    (hpieces : ∀ n : ℕ, (countableClopenShell p n).Nonempty →
      HasOrdinalCompactModel (countableClopenShell p n)) :
    HasOrdinalCompactModel K := by
  classical
  let I := {n : ℕ // (countableClopenShell p n).Nonempty}
  letI : Infinite I := infinite_nonempty_shells_of_not_isOpen_singleton p hp
  let e : ℕ ≃ I := Classical.choice nonempty_equiv_of_countable
  choose a ha using fun n : ℕ => hpieces (e n).val (e n).property
  let d : ∀ n, countableClopenShell p (e n).val ≃ₜ OrdinalInterval (a n) :=
    fun n => Classical.choice (ha n)
  let f : (Σ n, OrdinalInterval (a n)) → K := fun z => (d z.1).symm z.2 |>.val
  have hc : Continuous f := continuous_sigma fun n =>
    continuous_subtype_val.comp (d n).symm.continuous
  have hi : Function.Injective f := by
    rintro ⟨n, x⟩ ⟨m, y⟩ h
    change ((d n).symm x).val = ((d m).symm y).val at h
    have hnm : n = m := by
      apply e.injective
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (countableClopenShell_disjoint p hne)
        ((d n).symm x).property (h ▸ ((d m).symm y).property)
    subst m
    congr 1
    exact (d n).symm.injective (Subtype.ext h)
  have ho : IsOpenMap f := isOpenMap_sigma.mpr fun n =>
    (countableClopenShell_isClopen p (e n).val).isOpen.isOpenEmbedding_subtypeVal.isOpenMap.comp
      (d n).symm.isOpenMap
  have hr : range f = ({p} : Set K)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨n, y⟩, hxy⟩ h
      have he : ((d n).symm y).val = p := hxy.trans h
      exact countableClopenShell_not_mem p (e n).val
        (Eq.mp (congrArg (fun z : K => z ∈ countableClopenShell p (e n).val) he)
          ((d n).symm y).property)
    · intro hx
      obtain ⟨m, hm⟩ := countableClopenShell_covers p hx
      let i : I := ⟨m, x, hm⟩
      obtain ⟨n, hn⟩ := e.surjective i
      have hnval : (e n).val = m := congrArg Subtype.val hn
      let y : countableClopenShell p (e n).val := ⟨x, hnval ▸ hm⟩
      exact ⟨⟨n, d n y⟩, by simp [f, y]⟩
  let q : OnePoint (Σ n, OrdinalInterval (a n)) ≃ₜ K :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p f
      (IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho).isEmbedding hr
  exact ⟨ordinalBlockSup a, ⟨q.symm.trans (ordinalOnePointSumHomeomorph a)⟩⟩

/-- Every compact piece away from the chosen point may be assembled into
an ordinal model of the whole space. Isolated points require only a finite sum. -/
theorem hasOrdinalCompactModel_of_compact_pieces_away (p : K)
    (hpieces : ∀ B : Set K, IsCompact B → B.Nonempty → Disjoint B {p} →
      HasOrdinalCompactModel B) : HasOrdinalCompactModel K := by
  classical
  by_cases hp : IsOpen ({p} : Set K)
  · by_cases hn : (({p} : Set K)ᶜ).Nonempty
    · have hright := hpieces ({p}ᶜ) hp.isClosed_compl.isCompact hn
        (disjoint_compl_left : Disjoint ({p} : Set K)ᶜ {p})
      have hmodel : HasOrdinalCompactModel (univ : Set K) :=
        hasOrdinalCompactModel_of_clopen_pieces univ isCompact_univ {p}
          ⟨isClosed_singleton, hp⟩
          ((hasOrdinalCompactModel_singleton p).of_homeomorph
            (Homeomorph.setCongr (Set.univ_inter _)))
          (hright.of_homeomorph (Homeomorph.setCongr (by ext x; simp)))
      exact hmodel.of_homeomorph (Homeomorph.Set.univ K).symm
    · have hall : ∀ x : K, x = p := by
        intro x
        by_contra hx
        exact hn ⟨x, hx⟩
      letI : Unique K := ⟨⟨p⟩, hall⟩
      exact (hasOrdinalCompactModel_singleton p).of_homeomorph
        (Homeomorph.homeomorphOfUnique K ({p} : Set K))
  · apply hasOrdinalCompactModel_of_nonisolated_point p hp
    intro n hn
    apply hpieces _ (countableCompactShell_isCompact p n) hn
    exact Set.disjoint_singleton_right.mpr (countableClopenShell_not_mem p n)

end Posets
