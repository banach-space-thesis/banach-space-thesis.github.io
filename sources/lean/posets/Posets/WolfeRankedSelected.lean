import Posets.WolfeRankedSelectedGlue

/-! Every ranked family admits a countable full-rank subfamily with uniformly
small mass of all proper descendants at each selected node. -/
noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_exists_countable_selection (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (hne : ∀ q ∈ B, (v q).2.Nonempty) {η : ℝ} (hη : 0 < η)
    (α : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves α) :
    ∃ C : Set P, RankedWolfeSelection M v B η p C ∧
      p ∈ rankedWolfeFamily v height C Leaves α := by
  classical
  induction α using Ordinal.limitRecOn generalizing p with
  | zero =>
    obtain ⟨hb, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B Leaves p).mp hp
    refine ⟨{p}, ?_, (mem_rankedWolfeFamily_zero v height {p} Leaves p).mpr
      ⟨mem_singleton p, hh, hl⟩⟩
    refine ⟨countable_singleton p, singleton_subset_iff.mpr hb, mem_singleton p, ?_, ?_⟩
    · intro q hq
      rcases mem_singleton_iff.mp hq with rfl
      exact subset_rfl
    · intro q hq
      rcases mem_singleton_iff.mp hq with rfl
      rw [rankedWolfeDescendantUnion_singleton, wolfeMass_empty]
      exact hη
  | succ α ih =>
    obtain ⟨hb, hh, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp
    obtain ⟨N, hN⟩ := wolfeMass_disjoint_tail_union_small M (v p).1
      (fun n => (v (c n)).2) hch.2.1 hη
    let d : ℕ → P := fun n => c (n + N)
    have hd : WolfeChildren (v p) (fun n => v (d n)) := hch.tail N
    have hex (n : ℕ) := ih (hc (n + N))
    choose C hC hf using hex
    let D := insert p (⋃ n, C n)
    have hs : RankedWolfeSelection M v B η p D :=
      RankedWolfeSelection.glue M v B η p d C hb hne hC hd.child_subset hd.2.1 hN
    refine ⟨D, hs, (mem_rankedWolfeFamily_succ v height D Leaves α p).mpr
      ⟨hs.root, hh, d, ?_, hd⟩⟩
    intro n
    exact rankedWolfeFamily_mono_base v height
      (fun q hq => mem_insert_of_mem p (mem_iUnion.mpr ⟨n, hq⟩)) Leaves α (hf n)
  | limit α hα ih =>
    obtain ⟨hb, hh, a, ha, hcof, c, hc, hch⟩ :=
      (mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp
    obtain ⟨N, hN⟩ := wolfeMass_disjoint_tail_union_small M (v p).1
      (fun n => (v (c n)).2) hch.2.1 hη
    let d : ℕ → P := fun n => c (n + N)
    let b : ℕ → Iio α := fun n => a (n + N)
    have hd : WolfeChildren (v p) (fun n => v (d n)) := hch.tail N
    have hex (n : ℕ) := ih (a (n + N)).val (a (n + N)).property (hc (n + N))
    choose C hC hf using hex
    let D := insert p (⋃ n, C n)
    have hs : RankedWolfeSelection M v B η p D :=
      RankedWolfeSelection.glue M v B η p d C hb hne hC hd.child_subset hd.2.1 hN
    refine ⟨D, hs, (mem_rankedWolfeFamily_limit v height D Leaves hα p).mpr
      ⟨hs.root, hh, b, ?_, ?_, d, ?_, hd⟩⟩
    · intro n m hnm
      exact ha (Nat.add_lt_add_right hnm N)
    · intro β hβ
      obtain ⟨n, hn⟩ := hcof β hβ
      exact ⟨n, hn.trans (ha.monotone (Nat.le_add_right n N))⟩
    · intro n
      exact rankedWolfeFamily_mono_base v height
        (fun q hq => mem_insert_of_mem p (mem_iUnion.mpr ⟨n, hq⟩)) Leaves (b n).val (hf n)

end Posets
