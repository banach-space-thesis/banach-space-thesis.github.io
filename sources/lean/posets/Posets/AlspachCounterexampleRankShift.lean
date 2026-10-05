import Posets.AlspachCounterexampleRankGraft

/-! Once a graft has reduced to its base, subsequent derivatives are exactly
the derivatives of that base, with ordinal addition in the correct order. -/

noncomputable section
open Set Topology Order ThesisCommon
universe u v w z
namespace Posets

theorem alspach_ordinalDerived_add {K : Type v} [TopologicalSpace K] [T1Space K]
    {A : Set K} (hA : IsClosed A) (α β : Ordinal.{u}) :
    ordinalDerived A (α + β) = ordinalDerived (ordinalDerived A α) β := by
  induction β using Ordinal.limitRecOn with
  | zero => simp
  | succ β ih => rw [Ordinal.add_succ, ordinalDerived_succ, ih, ordinalDerived_succ]
  | limit β hβ ih =>
      rw [ordinalDerived_limit _ (Ordinal.isSuccLimit_add α hβ),
        ordinalDerived_limit _ hβ]
      ext x
      constructor
      · intro hx
        apply mem_iInter₂.mpr
        intro γ hγ
        rw [← ih γ hγ]
        exact mem_iInter₂.mp hx (α + γ) (add_lt_add_left hγ α)
      · intro hx
        apply mem_iInter₂.mpr
        intro ξ hξ
        obtain ⟨γ, hγ, hξγ⟩ := (Ordinal.lt_add_iff hβ.ne_bot).mp hξ
        have h := mem_iInter₂.mp hx γ hγ
        rw [← ih γ hγ] at h
        exact ordinalDerived_antitone hA hξγ h

theorem alspachCompactGraft_ordinalDerived_add
    {K : Type v} {I : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (anchor : I → K) (X : I → Type z) [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] (p : ∀ i, X i)
    (β γ : Ordinal.{u}) (hβ : ∀ i, ordinalDerived (univ : Set (X i)) β = {p i})
    (ha : Function.Surjective anchor) :
    ordinalDerived (univ : Set (AlspachGraft anchor (fun i => {x : X i // x ≠ p i})))
      (β + γ) = alspachGraftBase anchor _ '' ordinalDerived (univ : Set K) γ := by
  rw [alspach_ordinalDerived_add isClosed_univ,
    alspachCompactGraft_ordinalDerived_eq_base anchor X p β hβ ha, ← image_univ]
  exact ordinalDerived_image_closedEmbedding (alspachGraftBase_isClosedEmbedding anchor _) _ γ

end Posets
