import Posets.WolfeDirac

/-! Wolfe's families decrease through the countable ordinals. This proof
retains the same parent open set and uses tails of the actual child sequence;
the limit clause is not silently replaced by an intersection. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem WolfeChildren.tail {p : WolfeNode 𝕜 K} {c : ℕ → WolfeNode 𝕜 K}
    (hc : WolfeChildren p c) (N : ℕ) : WolfeChildren p (fun n => c (n + N)) := by
  refine ⟨hc.1.comp (tendsto_add_atTop_nat N), ?_, ?_⟩
  · intro i j hij
    exact hc.2.1 (by omega)
  · apply (closure_mono ?_).trans hc.2.2
    exact iUnion_subset fun n => subset_iUnion (fun n => (c n).2) (n + N)

theorem wolfeFamily_of_children_all_lower (M : JLMS.AtomicDualModel 𝕜 K)
    (ε : ℝ) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (α : Ordinal.{u}) (hαc : α.card ≤ Cardinal.aleph0)
    {p : WolfeNode 𝕜 K} (hp : p ∈ wolfeBase M ε B)
    (c : ℕ → WolfeNode 𝕜 K) (hch : WolfeChildren p c)
    (hc : ∀ β < α, ∀ n, c n ∈ wolfeFamily M ε B β) :
    p ∈ wolfeFamily M ε B α := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨β, rfl⟩ | hα
  · simpa using hp
  · exact (mem_wolfeFamily_succ M ε B β p).mpr ⟨hp, c, hc β (lt_succ β), hch⟩
  · obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα hαc
    exact (mem_wolfeFamily_limit M ε B hα p).mpr
      ⟨hp, a, ha, hcof, c, fun n => hc (a n).val (a n).property n, hch⟩

theorem wolfeFamily_subset_lower (M : JLMS.AtomicDualModel 𝕜 K)
    (ε : ℝ) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (β : Ordinal.{u}) (hβc : β.card ≤ Cardinal.aleph0) :
    ∀ α < β, wolfeFamily M ε B β ⊆ wolfeFamily M ε B α := by
  induction β using Ordinal.limitRecOn with
  | zero => intro α hα; exact (Ordinal.not_lt_zero α hα).elim
  | succ β ih =>
      intro α hα p hp
      obtain ⟨hp, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B β p).mp hp
      apply wolfeFamily_of_children_all_lower M ε B α
        ((Ordinal.card_le_card hα.le).trans hβc) hp c hch
      intro γ hγ n
      exact ih ((Ordinal.card_le_card (le_succ β)).trans hβc)
        γ (hγ.trans_le (lt_succ_iff.mp hα)) (hc n)
  | limit β hβ ih =>
      intro α hα p hp
      obtain ⟨hp, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hβ p).mp hp
      obtain ⟨N, hN⟩ := hcof α hα
      apply wolfeFamily_of_children_all_lower M ε B α
        ((Ordinal.card_le_card hα.le).trans hβc) hp (fun n => c (n + N)) (hch.tail N)
      intro γ hγ n
      have hγα : γ < (a (n + N)).val :=
        hγ.trans_le (hN.trans (ha.monotone (Nat.le_add_left N n)))
      exact ih (a (n + N)).val (a (n + N)).property
        ((Ordinal.card_le_card (a (n + N)).property.le).trans hβc) γ hγα (hc (n + N))

theorem wolfeFamily_antitone_on_countable (M : JLMS.AtomicDualModel 𝕜 K)
    (ε : ℝ) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    {α β : Ordinal.{u}} (hβc : β.card ≤ Cardinal.aleph0) (hαβ : α ≤ β) :
    wolfeFamily M ε B β ⊆ wolfeFamily M ε B α := by
  rcases hαβ.eq_or_lt with rfl | hlt
  · exact subset_rfl
  · exact wolfeFamily_subset_lower M ε B β hβc α hlt

end Posets
