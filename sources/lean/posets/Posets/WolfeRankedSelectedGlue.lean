import Posets.WolfeRankedSelectedSets

/-! Gluing selected subtrees with small proper-descendant mass. -/
noncomputable section
open Set Filter Topology Order
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

structure RankedWolfeSelection (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (B : Set P) (η : ℝ) (p : P) (C : Set P) : Prop where
  countable : C.Countable
  subset : C ⊆ B
  root : p ∈ C
  cells : ∀ q ∈ C, (v q).2 ⊆ (v p).2
  small : ∀ q ∈ C, wolfeMass M (v q).1 (rankedWolfeDescendantUnion v C q) < η

theorem RankedWolfeSelection.glue (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (B : Set P) (η : ℝ) (p : P)
    (c : ℕ → P) (C : ℕ → Set P) (hp : p ∈ B)
    (hne : ∀ q ∈ B, (v q).2.Nonempty)
    (hC : ∀ n, RankedWolfeSelection M v B η (c n) (C n))
    (hsub : ∀ n, (v (c n)).2 ⊆ (v p).2)
    (hd : Pairwise fun n m => Disjoint (v (c n)).2 (v (c m)).2)
    (hm : wolfeMass M (v p).1 (⋃ n, (v (c n)).2) < η) :
    RankedWolfeSelection M v B η p (insert p (⋃ n, C n)) := by
  refine ⟨(countable_iUnion (fun n => (hC n).countable)).insert p, ?_, mem_insert p _, ?_, ?_⟩
  · intro q hq
    rcases mem_insert_iff.mp hq with rfl | hq
    · exact hp
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      exact (hC n).subset hn
  · intro q hq
    rcases mem_insert_iff.mp hq with rfl | hq
    · exact subset_rfl
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      exact ((hC n).cells q hn).trans (hsub n)
  · intro q hq
    rcases mem_insert_iff.mp hq with rfl | hq
    · exact (wolfeMass_mono M (v q).1 (rankedWolfeDescendantUnion_root_subset v q C
        (fun n => (v (c n)).2) (fun n => (hC n).cells))).trans_lt hm
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
      exact (wolfeMass_mono M (v q).1 (rankedWolfeDescendantUnion_child_subset v p C
        (fun n => (v (c n)).2) (fun n => (hC n).cells) hsub hd
        (fun m r hr => hne r ((hC m).subset hr)) hn)).trans_lt ((hC n).small q hn)

end Posets

