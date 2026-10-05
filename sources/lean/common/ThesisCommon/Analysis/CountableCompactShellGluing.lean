import ThesisCommon.Analysis.CountableCompactShells
import ThesisCommon.Analysis.OrdinalOnePointSum
import Mathlib.Logic.Denumerable

/-! The induction gluing step for countable compact metric classification.
Empty shells are removed by an actual reindexing. If every remaining compact
shell has an ordinal model, their one-point compactification has one too. -/
noncomputable section
open Set Topology
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K] [CompactSpace K] [Countable K]

def countableNonemptyShells (p : K) : Set ℕ :=
  {n | (countableClopenShell p n).Nonempty}

theorem countableNonemptyShells_infinite (p : K) (hp : ¬IsOpen ({p} : Set K)) :
    (countableNonemptyShells p).Infinite := by
  classical
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have heq : countableClopenNest p (N + 1) = {p} := by
    ext x
    constructor
    · intro hx
      by_contra hxp
      obtain ⟨n, hn⟩ := countableClopenShell_covers p hxp
      have hnN : n ≤ N := hN (show n ∈ countableNonemptyShells p from ⟨x, hn⟩)
      exact hn.2 (countableClopenNest_antitone p (Nat.succ_le_succ hnN) hx)
    · intro hx
      have hxp : x = p := hx
      rw [hxp]
      exact countableClopenNest_mem p (N + 1)
  exact hp (heq ▸ (countableClopenNest_isClopen p (N + 1)).isOpen)

theorem countableCompactShell_glue_ordinal_models (p : K)
    (hp : ¬IsOpen ({p} : Set K))
    (hmodel : ∀ n, (countableClopenShell p n).Nonempty →
      ∃ α : Ordinal.{u}, Nonempty ((countableClopenShell p n) ≃ₜ OrdinalInterval α)) :
    ∃ α : Ordinal.{u}, Nonempty (K ≃ₜ OrdinalInterval α) := by
  classical
  let S := countableNonemptyShells p
  letI : Infinite S := (countableNonemptyShells_infinite p hp).to_subtype
  let en : ℕ ≃ S := Classical.choice inferInstance
  let H : ℕ → Type u := fun n => countableClopenShell p (en n).val
  let f : (Σ n, H n) → K := fun z => z.2.val
  have hinj : Function.Injective f := by
    rintro ⟨n, x⟩ ⟨m, y⟩ hxy
    have hval : x.val = y.val := hxy
    have hnm : n = m := by
      apply en.injective
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (countableClopenShell_disjoint p hne)
        x.property (hval ▸ y.property)
    subst m
    congr 1
    exact Subtype.ext hval
  have hopen : IsOpenEmbedding f := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_sigma (fun _ => continuous_subtype_val)
    · exact hinj
    · apply isOpenMap_sigma.mpr
      intro n
      exact (countableClopenShell_isClopen p (en n).val).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hrange : range f = {p}ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨n, y⟩, rfl⟩ h
      change y.val = p at h
      apply countableClopenShell_not_mem p (en n).val
      simpa only [h] using y.property
    · intro hx
      obtain ⟨n, hn⟩ := countableClopenShell_covers p hx
      let i : S := ⟨n, x, hn⟩
      have he : (en (en.symm i)).val = n := congrArg Subtype.val (en.apply_symm_apply i)
      refine ⟨⟨en.symm i, ⟨x, ?_⟩⟩, rfl⟩
      change x ∈ countableClopenShell p (en (en.symm i)).val
      simpa only [he] using hn
  let eK : OnePoint (Σ n, H n) ≃ₜ K :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p f hopen.isEmbedding hrange
  choose a ha using (fun n => hmodel (en n).val (en n).property)
  let es : (Σ n, H n) ≃ₜ (Σ n, OrdinalInterval (a n)) :=
    { toEquiv := Equiv.sigmaCongrRight (fun n => (Classical.choice (ha n)).toEquiv)
      continuous_toFun := continuous_sigma fun n =>
        (continuous_sigmaMk (i := n)).comp (Classical.choice (ha n)).continuous
      continuous_invFun := continuous_sigma fun n =>
        (continuous_sigmaMk (i := n)).comp (Classical.choice (ha n)).symm.continuous }
  exact ⟨ordinalBlockSup a, ⟨eK.symm.trans (es.onePointCongr.trans (ordinalOnePointSumHomeomorph a))⟩⟩

end ThesisCommon
