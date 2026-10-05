import Posets.AlspachCounterexampleWolfeWindow

/-! Two elementary ways to end a Wolfe tree: a derivative bound within a
fixed window, and two additional levels to choose a closed window avoiding
one prescribed point. -/

noncomputable section
open Set Topology Order ThesisCommon
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem alspachWolfeWindow_empty_of_projection_bound (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) (B A : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (C : Set K) (β η : Ordinal) (hc : (β + η).card ≤ Cardinal.aleph0)
    (hsub : alspachWolfeWindowMeasures M ε B C β ⊆ A)
    (he : ordinalDerived A η = ∅) :
    ∀ U ⊆ C, ∀ μ, (μ, U) ∉ wolfeFamily M ε B (β + η) := by
  intro U hUC μ hμ
  have hh := alspachWolfeWindow_add_subset_ordinalDerived M hε B C β η hc ⟨U, hUC, hμ⟩
  have hm := ordinalDerived_mono hsub η hh
  rw [he] at hm
  exact hm

theorem alspachWolfe_empty_of_closed_windows (M : JLMS.AtomicDualModel 𝕜 K)
    (ε : ℝ) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (p : K) (κ : Ordinal)
    (hw : ∀ C : Set K, IsClosed C → p ∉ C →
      ∀ U ⊆ C, ∀ μ, (μ, U) ∉ wolfeFamily M ε B κ) :
    wolfeFamily M ε B (succ (succ κ)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨_, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B (succ κ) z).mp hz
  have hex : ∃ n : ℕ, p ∉ (c n).2 := by
    by_contra! h
    exact Set.disjoint_left.mp (hch.2.1 (show (0 : ℕ) ≠ 1 by decide)) (h 0) (h 1)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨_, d, hd, hdh⟩ := (mem_wolfeFamily_succ M ε B κ (c n)).mp (hc n)
  exact hw (closure (⋃ n, (d n).2)) isClosed_closure
    (fun hp => hn (hdh.2.2 hp)) (d 0).2
    ((subset_iUnion (fun n => (d n).2) 0).trans subset_closure) (d 0).1 (hd 0)

end Posets
