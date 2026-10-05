import Posets.WolfeLaminarEmbeddingQuotient
import Posets.WolfeRankedClosure
import ThesisCommon.Analysis.OrdinalDerived

/-! Cantor–Bendixson lower bounds for the actual clopen-code quotient.

The offset allows discarding all coordinates below a prescribed original
rank.  At limit stages compactness combines witnesses from lower ranks;
no injectivity or positivity of the rows is used.
-/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u

namespace Posets

variable {K ι : Type*} [TopologicalSpace K]

/-- Equal quotient codes have the same membership in every recorded cell. -/
theorem wolfeClopenProjection_mem_iff (A : ι → Set K) (hA : ∀ i, IsClopen (A i))
    {x y : K} (hxy : wolfeClopenProjection A hA x = wolfeClopenProjection A hA y)
    (i : ι) : x ∈ A i ↔ y ∈ A i := by
  have h := congrArg (fun q : WolfeClopenQuotient A hA => q.val i) hxy
  change (A i).boolIndicator x = (A i).boolIndicator y at h
  rw [mem_iff_boolIndicator, mem_iff_boolIndicator, h]

/-- A recorded cell stays disjoint from the image of any disjoint set. -/
theorem wolfeClopenProjection_disjoint_image (A : ι → Set K)
    (hA : ∀ i, IsClopen (A i)) {U V : Set K} (hUV : Disjoint U V)
    (hU : ∃ i, A i = U) :
    Disjoint (wolfeClopenProjection A hA '' U) (wolfeClopenProjection A hA '' V) := by
  obtain ⟨i, rfl⟩ := hU
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  exact Set.disjoint_left.mp hUV
    ((wolfeClopenProjection_mem_iff A hA (hxq.trans hyq.symm) i).mp hx) hy

variable {𝕜 P : Type*} [RCLike 𝕜]

/-- Rank `β + α` in a ranked Wolfe family forces Cantor–Bendixson rank at
least `α` in the quotient recording all cells of original rank at least `β`.
The witness belongs to the image of the original root cell. -/
theorem rankedWolfeFamily_quotient_ordinalDerived
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (H : Set K) (β : Ordinal.{u})
    (hcell : ∀ p ∈ B, (v p).2.Nonempty ∧ IsCompact (v p).2)
    (hcoord : ∀ δ p, p ∈ rankedWolfeFamily v height B Leaves δ →
      β ≤ δ → (v p).2 ⊆ H → ∃ i, A i = (v p).2)
    (α : Ordinal.{u}) {p : P}
    (hp : p ∈ rankedWolfeFamily v height B Leaves (β + α))
    (hpH : (v p).2 ⊆ H) :
    ((wolfeClopenProjection A hA '' (v p).2) ∩
      ordinalDerived (Set.univ : Set (WolfeClopenQuotient A hA)) α).Nonempty := by
  classical
  induction α using Ordinal.limitRecOn generalizing p with
  | zero =>
      obtain ⟨x, hx⟩ := (hcell p (rankedWolfeFamily_base_height v height B Leaves _ hp).1).1
      exact ⟨wolfeClopenProjection A hA x, ⟨x, hx, rfl⟩, by simp⟩
  | succ α ih =>
      rw [Ordinal.add_succ] at hp
      obtain ⟨hpb, _, c, hc, hch⟩ :=
        (mem_rankedWolfeFamily_succ v height B Leaves (β + α) p).mp hp
      have hex (n : ℕ) := ih (hc n) ((hch.child_subset n).trans hpH)
      choose q hq using hex
      have hcoord' (n : ℕ) : ∃ i, A i = (v (c n)).2 :=
        hcoord (β + α) (c n) (hc n) (Ordinal.le_add_right _ _) ((hch.child_subset n).trans hpH)
      have hqinj : Function.Injective q := by
        intro n m hnm
        by_contra hne
        have hd := wolfeClopenProjection_disjoint_image A hA (hch.2.1 hne) (hcoord' n)
        exact Set.disjoint_left.mp hd (hq n).1 (hnm ▸ (hq m).1)
      have hcompact : IsCompact (wolfeClopenProjection A hA '' (v p).2) :=
        (hcell p hpb).2.image (wolfeClopenProjection A hA).continuous
      have hrange : Set.range q ⊆ wolfeClopenProjection A hA '' (v p).2 := by
        rintro _ ⟨n, rfl⟩
        exact Set.image_mono (hch.child_subset n) (hq n).1
      obtain ⟨z, hz, hacc⟩ := (Set.infinite_range_of_injective hqinj).exists_accPt_of_subset_isCompact
        hcompact hrange
      refine ⟨z, hz, ?_⟩
      rw [ordinalDerived_succ]
      apply derivedSet_mono (Set.range q) _ ?_ hacc
      rintro _ ⟨n, rfl⟩
      exact (hq n).2
  | limit α hα ih =>
      let S : Set (WolfeClopenQuotient A hA) := wolfeClopenProjection A hA '' (v p).2
      have hS : IsCompact S :=
        (hcell p (rankedWolfeFamily_base_height v height B Leaves _ hp).1).2.image
          (wolfeClopenProjection A hA).continuous
      let F (γ : Iio α) : Set (WolfeClopenQuotient A hA) :=
        S ∩ ordinalDerived Set.univ γ.val
      have hFne (γ : Iio α) : (F γ).Nonempty := by
        obtain ⟨q, hq, hqp⟩ := rankedWolfeFamily_exists_lower v height B Leaves (β + α) hp
          (add_le_add_left γ.property.le β)
        obtain ⟨z, hz, hzd⟩ := ih γ.val γ.property hq (hqp.trans hpH)
        exact ⟨z, Set.image_mono hqp hz, hzd⟩
      have hFd : Directed (· ⊇ ·) F := by
        intro γ δ
        refine ⟨⟨max γ.val δ.val, show max γ.val δ.val < α from
          max_lt γ.property δ.property⟩, ?_, ?_⟩
        · exact inter_subset_inter_right _ (ordinalDerived_antitone isClosed_univ (le_max_left _ _))
        · exact inter_subset_inter_right _ (ordinalDerived_antitone isClosed_univ (le_max_right _ _))
      letI : Nonempty (Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
      obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        F hFd hFne
        (fun γ => hS.inter_right (isClosed_ordinalDerived isClosed_univ γ.val))
        (fun γ => hS.isClosed.inter (isClosed_ordinalDerived isClosed_univ γ.val))
      refine ⟨z, (mem_iInter.mp hz ⟨0, hα.bot_lt⟩).1, ?_⟩
      rw [ordinalDerived_limit Set.univ hα]
      exact mem_iInter₂.mpr (fun γ hγ => (mem_iInter.mp hz ⟨γ, hγ⟩).2)

end Posets
