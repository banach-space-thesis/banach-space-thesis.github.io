import Posets.WolfeSequenceRefinement

/-! A finite weak-star closed cover of the measures respects every Wolfe
level. Subsequence selection preserves the child disjointness and cofinal
ordinal ranks, while closedness retains the root measure in the selected part. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets

theorem wolfe_finiteColor_subsequence {ι : Type*} [Finite ι] (j : ℕ → ι) :
    ∃ i : ι, ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, j (f n) = i := by
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber j
  have hfreq : ∃ᶠ n in atTop, j n = i := by
    rw [← Nat.cofinite_eq_atTop, frequently_cofinite_iff_infinite]
    exact Set.infinite_coe_iff.mp hi
  obtain ⟨f, hf, hfi⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨i, f, hf, hfi⟩

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeFamily_iUnion_closed {ι : Type*} [Finite ι]
    (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : ι → Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (hB : ∀ i, IsClosed (B i))
    (α : Ordinal.{u}) :
    wolfeFamily M ε (⋃ i, B i) α = ⋃ i, wolfeFamily M ε (B i) α := by
  classical
  apply subset_antisymm
  · induction α using Ordinal.limitRecOn with
    | zero =>
        intro p hp
        simp only [wolfeFamily_zero] at hp ⊢
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1
        exact mem_iUnion.mpr ⟨i, hi, hp.2⟩
    | succ α ih =>
        intro p hp
        obtain ⟨hb, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε (⋃ i, B i) α p).mp hp
        have hi (n : ℕ) : ∃ i, c n ∈ wolfeFamily M ε (B i) α := mem_iUnion.mp (ih (hc n))
        choose j hj using hi
        obtain ⟨i, f, hf, hfi⟩ := wolfe_finiteColor_subsequence j
        have hc' (n : ℕ) : c (f n) ∈ wolfeFamily M ε (B i) α := by
          simpa only [hfi n] using hj (f n)
        have hch' := hch.subsequence hf
        have hpi : p.1 ∈ B i := (hB i).mem_of_tendsto hch'.1
          (Eventually.of_forall fun n => (wolfeFamily_subset_base M ε (B i) α (hc' n)).1)
        exact mem_iUnion.mpr ⟨i, (mem_wolfeFamily_succ M ε (B i) α p).mpr
          ⟨⟨hpi, hb.2⟩, (fun n => c (f n)), hc', hch'⟩⟩
    | limit α hα ih =>
        intro p hp
        obtain ⟨hb, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε (⋃ i, B i) hα p).mp hp
        have hi (n : ℕ) : ∃ i, c n ∈ wolfeFamily M ε (B i) (a n).val :=
          mem_iUnion.mp (ih (a n).val (a n).property (hc n))
        choose j hj using hi
        obtain ⟨i, f, hf, hfi⟩ := wolfe_finiteColor_subsequence j
        have hc' (n : ℕ) : c (f n) ∈ wolfeFamily M ε (B i) (a (f n)).val := by
          simpa only [hfi n] using hj (f n)
        have hch' := hch.subsequence hf
        have hpi : p.1 ∈ B i := (hB i).mem_of_tendsto hch'.1
          (Eventually.of_forall fun n => (wolfeFamily_subset_base M ε (B i) _ (hc' n)).1)
        refine mem_iUnion.mpr ⟨i, (mem_wolfeFamily_limit M ε (B i) hα p).mpr
          ⟨⟨hpi, hb.2⟩, (fun n => a (f n)), ha.comp hf, ?_, (fun n => c (f n)), hc', hch'⟩⟩
        intro β hβ
        obtain ⟨n, hn⟩ := hcof β hβ
        exact ⟨n, hn.trans (ha.monotone (hf.id_le n))⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact wolfeFamily_mono M le_rfl (subset_iUnion B i) α hi

end Posets
