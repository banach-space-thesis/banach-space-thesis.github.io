import Posets.WolfeRankShift

/-! Wolfe's rank-shift estimate inside a fixed spatial window. Every
descendant open set stays in that window, so the usual derivative argument
applies without requiring a globally restricted space of measures. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

def alspachWolfeWindowMeasures (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (C : Set K) (α : Ordinal) :
    Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :=
  {μ | ∃ U ⊆ C, (μ, U) ∈ wolfeFamily M ε B α}

theorem alspachWolfeWindow_add_subset_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (C : Set K) (γ η : Ordinal) (hc : (γ + η).card ≤ Cardinal.aleph0) :
    alspachWolfeWindowMeasures M ε B C (γ + η) ⊆
      ordinalDerived (alspachWolfeWindowMeasures M ε B C γ) η := by
  induction η using Ordinal.limitRecOn with
  | zero => simpa only [add_zero, ordinalDerived_zero] using subset_rfl
  | succ η ih =>
      rintro μ ⟨U, hUC, hp⟩
      rw [Ordinal.add_succ] at hp
      obtain ⟨_, c, hchild, hch⟩ :=
        (mem_wolfeFamily_succ M ε B (γ + η) (μ, U)).mp hp
      have hc' : (γ + η).card ≤ Cardinal.aleph0 :=
        (Ordinal.card_le_card (by rw [Ordinal.add_succ]; exact le_succ _)).trans hc
      rw [ordinalDerived_succ]
      exact wolfeSequence_mem_derivedSet M (fun n => (c n).1) (fun n => (c n).2)
        hch.2.1 hε (fun n => (wolfeFamily_subset_base M ε B _ (hchild n)).2.2)
        hch.1 (fun n => ih hc' ⟨(c n).2, (hch.child_subset n).trans hUC, hchild n⟩)
  | limit η hη ih =>
      rintro μ ⟨U, hUC, hp⟩
      rw [ordinalDerived_limit _ hη]
      apply mem_iInter₂.mpr
      intro β hβ
      have hle : γ + β ≤ γ + η := add_le_add_left hβ.le γ
      exact ih β hβ ((Ordinal.card_le_card hle).trans hc) ⟨U, hUC,
        wolfeFamily_antitone_on_countable M ε B hc hle hp⟩

end Posets
