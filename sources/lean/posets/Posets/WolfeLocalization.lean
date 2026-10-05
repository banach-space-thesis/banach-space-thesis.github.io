import Posets.WolfeMonotonicity

/-! Wolfe witnesses can be localized to every weak-star neighborhood of
their root measure. This retains the original spatial open set and the full
ordinal level; sequence tails implement the localization at every stage. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeFamily_localize_measures (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    ∀ p ∈ wolfeFamily M ε B α,
      ∀ W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)), IsOpen W → p.1 ∈ W →
        p ∈ wolfeFamily M ε (B ∩ W) α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p hp W _ hpW
      rw [wolfeFamily_zero] at hp ⊢
      exact ⟨⟨hp.1, hpW⟩, hp.2⟩
  | succ α ih =>
      intro p hp W hW hpW
      obtain ⟨hp, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
      have hev : ∀ᶠ n in atTop, (c n).1 ∈ W := hch.1 (hW.mem_nhds hpW)
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      refine (mem_wolfeFamily_succ M ε (B ∩ W) α p).mpr
        ⟨⟨⟨hp.1, hpW⟩, hp.2⟩, (fun n => c (n + N)), ?_, hch.tail N⟩
      intro n
      exact ih (c (n + N)) (hc (n + N)) W hW (hN _ (Nat.le_add_left N n))
  | limit α hα ih =>
      intro p hp W hW hpW
      obtain ⟨hp, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα p).mp hp
      have hev : ∀ᶠ n in atTop, (c n).1 ∈ W := hch.1 (hW.mem_nhds hpW)
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      refine (mem_wolfeFamily_limit M ε (B ∩ W) hα p).mpr
        ⟨⟨⟨hp.1, hpW⟩, hp.2⟩, (fun n => a (n + N)), ?_, ?_,
          (fun n => c (n + N)), ?_, hch.tail N⟩
      · intro i j hij
        exact ha (Nat.add_lt_add_right hij N)
      · intro β hβ
        obtain ⟨n, hn⟩ := hcof β hβ
        exact ⟨n, hn.trans (ha.monotone (Nat.le_add_right n N))⟩
      · intro n
        exact ih (a (n + N)).val (a (n + N)).property (c (n + N)) (hc (n + N))
          W hW (hN _ (Nat.le_add_left N n))

theorem wolfeFamily_inter_open_iff (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u})
    {W : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))} (hW : IsOpen W) (p : WolfeNode 𝕜 K) :
    p ∈ wolfeFamily M ε (B ∩ W) α ↔ p ∈ wolfeFamily M ε B α ∧ p.1 ∈ W := by
  constructor
  · intro hp
    exact ⟨wolfeFamily_mono M le_rfl inter_subset_left α hp,
      (wolfeFamily_subset_base M ε (B ∩ W) α hp).1.2⟩
  · rintro ⟨hp, hpW⟩
    exact wolfeFamily_localize_measures M ε B α p hp W hW hpW

end Posets
