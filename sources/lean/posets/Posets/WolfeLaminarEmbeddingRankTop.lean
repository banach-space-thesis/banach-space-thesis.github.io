import Posets.WolfeLaminarEmbeddingRank
import Posets.WolfeLaminarEmbeddingClopenTop

/-! Rank transfer to the quotient of a clopen top cell.

The rows remain in the original ambient dual space.  Only the geometric
cells are restricted, so no transport of measures or row topology is needed.
-/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u

namespace Posets

variable {𝕜 K P Q : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace Q] [T2Space Q]

/-- A target-cell system preserving nesting and separating siblings retains
the offset Cantor–Bendixson lower bound of the original ranked family. -/
theorem rankedWolfeFamily_targetCells_ordinalDerived
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (F : P → Set Q) (H : Set K) (β : Ordinal.{u})
    (hcell : ∀ δ p, p ∈ rankedWolfeFamily v height B Leaves δ →
      β ≤ δ → (v p).2 ⊆ H → (F p).Nonempty ∧ IsCompact (F p))
    (hmono : ∀ p q, (v p).2 ⊆ (v q).2 → F p ⊆ F q)
    (hdisj : ∀ δ p q, p ∈ rankedWolfeFamily v height B Leaves δ →
      q ∈ rankedWolfeFamily v height B Leaves δ → β ≤ δ →
      (v p).2 ⊆ H → (v q).2 ⊆ H → Disjoint (v p).2 (v q).2 → Disjoint (F p) (F q))
    (α : Ordinal.{u}) {p : P}
    (hp : p ∈ rankedWolfeFamily v height B Leaves (β + α)) (hpH : (v p).2 ⊆ H) :
    (F p ∩ ordinalDerived (Set.univ : Set Q) α).Nonempty := by
  classical
  induction α using Ordinal.limitRecOn generalizing p with
  | zero =>
      obtain ⟨x, hx⟩ := (hcell _ p hp (Ordinal.le_add_right _ _) hpH).1
      exact ⟨x, hx, by simp⟩
  | succ α ih =>
      have hcompact := (hcell _ p hp (Ordinal.le_add_right _ _) hpH).2
      rw [Ordinal.add_succ] at hp
      obtain ⟨_, _, c, hc, hch⟩ :=
        (mem_rankedWolfeFamily_succ v height B Leaves (β + α) p).mp hp
      have hex (n : ℕ) := ih (hc n) ((hch.child_subset n).trans hpH)
      choose q hq using hex
      have hqinj : Function.Injective q := by
        intro n m hnm
        by_contra hne
        have hd := hdisj (β + α) (c n) (c m) (hc n) (hc m) (Ordinal.le_add_right _ _)
          ((hch.child_subset n).trans hpH) ((hch.child_subset m).trans hpH) (hch.2.1 hne)
        exact Set.disjoint_left.mp hd (hq n).1 (hnm ▸ (hq m).1)
      have hrange : Set.range q ⊆ F p := by
        rintro _ ⟨n, rfl⟩
        exact hmono (c n) p (hch.child_subset n) (hq n).1
      obtain ⟨z, hz, hacc⟩ := (Set.infinite_range_of_injective hqinj).exists_accPt_of_subset_isCompact
        hcompact hrange
      refine ⟨z, hz, ?_⟩
      rw [ordinalDerived_succ]
      apply derivedSet_mono (Set.range q) _ ?_ hacc
      rintro _ ⟨n, rfl⟩
      exact (hq n).2
  | limit α hα ih =>
      have hcompact := (hcell _ p hp (Ordinal.le_add_right _ _) hpH).2
      let G (γ : Iio α) : Set Q := F p ∩ ordinalDerived Set.univ γ.val
      have hGne (γ : Iio α) : (G γ).Nonempty := by
        obtain ⟨q, hq, hqp⟩ := rankedWolfeFamily_exists_lower v height B Leaves (β + α) hp
          (add_le_add_left γ.property.le β)
        obtain ⟨z, hz, hzd⟩ := ih γ.val γ.property hq (hqp.trans hpH)
        exact ⟨z, hmono q p hqp hz, hzd⟩
      have hGd : Directed (· ⊇ ·) G := by
        intro γ δ
        refine ⟨⟨max γ.val δ.val, show max γ.val δ.val < α from
          max_lt γ.property δ.property⟩, ?_, ?_⟩
        · exact inter_subset_inter_right _ (ordinalDerived_antitone isClosed_univ (le_max_left _ _))
        · exact inter_subset_inter_right _ (ordinalDerived_antitone isClosed_univ (le_max_right _ _))
      letI : Nonempty (Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
      obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        G hGd hGne
        (fun γ => hcompact.inter_right (isClosed_ordinalDerived isClosed_univ γ.val))
        (fun γ => hcompact.isClosed.inter (isClosed_ordinalDerived isClosed_univ γ.val))
      refine ⟨z, (mem_iInter.mp hz ⟨0, hα.bot_lt⟩).1, ?_⟩
      rw [ordinalDerived_limit Set.univ hα]
      exact mem_iInter₂.mpr (fun γ hγ => (mem_iInter.mp hz ⟨γ, hγ⟩).2)

variable {ι : Type*} [T2Space K]

/-- The quotient of the top cell retains the original offset rank, with all
ranked nodes and rows still interpreted in the ambient space. -/
theorem rankedWolfeFamily_clopenTop_ordinalDerived
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (H : Set K) [CompactSpace H] (A : ι → Set K) (hA : ∀ i, IsClopen (A i))
    (β : Ordinal.{u})
    (hcell : ∀ p ∈ B, (v p).2.Nonempty ∧ IsCompact (v p).2)
    (hcoord : ∀ δ p, p ∈ rankedWolfeFamily v height B Leaves δ →
      β ≤ δ → (v p).2 ⊆ H → ∃ i, A i = (v p).2)
    (α : Ordinal.{u}) {p : P}
    (hp : p ∈ rankedWolfeFamily v height B Leaves (β + α)) (hpH : (v p).2 ⊆ H) :
    ((wolfeClopenProjection (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA) ''
      (Subtype.val ⁻¹' (v p).2 : Set H)) ∩
      ordinalDerived (Set.univ : Set (WolfeClopenTopQuotient H A hA)) α).Nonempty := by
  let π := wolfeClopenProjection (wolfeClopenTopCells H A) (wolfeClopenTopCells_isClopen H A hA)
  apply rankedWolfeFamily_targetCells_ordinalDerived v height B Leaves
    (fun q => π '' (Subtype.val ⁻¹' (v q).2 : Set H)) H β ?_ ?_ ?_ α hp hpH
  · intro δ q hq _ hqH
    obtain ⟨hne, hc⟩ := hcell q (rankedWolfeFamily_base_height v height B Leaves δ hq).1
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨π ⟨x, hqH hx⟩, ⟨⟨x, hqH hx⟩, hx, rfl⟩⟩
    · exact ((hc.isClosed.preimage continuous_subtype_val).isCompact).image π.continuous
  · intro q r hqr
    exact image_mono (preimage_mono hqr)
  · intro δ q r hq _ hβ hqH _ hqr
    obtain ⟨i, hi⟩ := hcoord δ q hq hβ hqH
    apply wolfeClopenProjection_disjoint_image _ _ (hqr.preimage Subtype.val)
    exact ⟨i, congrArg (fun S : Set K => (Subtype.val ⁻¹' S : Set H)) hi⟩

end Posets
