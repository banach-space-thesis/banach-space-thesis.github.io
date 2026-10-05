import Posets.WolfeClosedCover

/-! Rank-labelled recursive clopen families. The leaf condition occurs only
at rank zero, so arbitrary finite colourings of leaves allow full-rank
pruning. Original rank labels remain fixed throughout the construction. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

def rankedWolfeFamily (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u})
    (B Leaves : Set P) (α : Ordinal.{u}) : Set P :=
  Ordinal.limitRecOn α {p | p ∈ B ∧ height p = 0 ∧ p ∈ Leaves}
    (fun α C => {p | p ∈ B ∧ height p = succ α ∧
      ∃ c : ℕ → P, (∀ n, c n ∈ C) ∧ WolfeChildren (v p) (fun n => v (c n))})
    (fun α _ C => {p | p ∈ B ∧ height p = α ∧
      ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧
        ∃ c : ℕ → P, (∀ n, c n ∈ C (a n).val (a n).property) ∧
          WolfeChildren (v p) (fun n => v (c n))})

@[simp] theorem mem_rankedWolfeFamily_zero (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B Leaves : Set P) (p : P) :
    p ∈ rankedWolfeFamily v height B Leaves 0 ↔ p ∈ B ∧ height p = 0 ∧ p ∈ Leaves := by
  unfold rankedWolfeFamily
  rw [Ordinal.limitRecOn_zero]
  rfl

theorem mem_rankedWolfeFamily_succ (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B Leaves : Set P) (α : Ordinal.{u}) (p : P) :
    p ∈ rankedWolfeFamily v height B Leaves (succ α) ↔
      p ∈ B ∧ height p = succ α ∧ ∃ c : ℕ → P,
        (∀ n, c n ∈ rankedWolfeFamily v height B Leaves α) ∧
          WolfeChildren (v p) (fun n => v (c n)) := by
  unfold rankedWolfeFamily
  rw [Ordinal.limitRecOn_succ]
  rfl

theorem mem_rankedWolfeFamily_limit (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B Leaves : Set P) {α : Ordinal.{u}}
    (hα : IsSuccLimit α) (p : P) :
    p ∈ rankedWolfeFamily v height B Leaves α ↔
      p ∈ B ∧ height p = α ∧
      ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧
        ∃ c : ℕ → P, (∀ n, c n ∈ rankedWolfeFamily v height B Leaves (a n).val) ∧
          WolfeChildren (v p) (fun n => v (c n)) := by
  unfold rankedWolfeFamily
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]
  rfl

theorem rankedWolfeFamily_base_height (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B Leaves : Set P) (α : Ordinal.{u})
    {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves α) :
    p ∈ B ∧ height p = α := by
  induction α using Ordinal.limitRecOn with
  | zero => exact ⟨(mem_rankedWolfeFamily_zero v height B Leaves p).mp hp |>.1,
      (mem_rankedWolfeFamily_zero v height B Leaves p).mp hp |>.2.1⟩
  | succ α _ => exact ⟨(mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp |>.1,
      (mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp |>.2.1⟩
  | limit α hα _ => exact ⟨(mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp |>.1,
      (mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp |>.2.1⟩

theorem rankedWolfeFamily_mono_leaves (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B : Set P) {L L' : Set P} (hL : L ⊆ L')
    (α : Ordinal.{u}) : rankedWolfeFamily v height B L α ⊆ rankedWolfeFamily v height B L' α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p hp
      obtain ⟨hp, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B L p).mp hp
      exact (mem_rankedWolfeFamily_zero v height B L' p).mpr ⟨hp, hh, hL hl⟩
  | succ α ih =>
      intro p hp
      obtain ⟨hb, hh, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B L α p).mp hp
      exact (mem_rankedWolfeFamily_succ v height B L' α p).mpr
        ⟨hb, hh, c, fun n => ih (hc n), hch⟩
  | limit α hα ih =>
      intro p hp
      obtain ⟨hb, hh, a, ha, hcof, c, hc, hch⟩ :=
        (mem_rankedWolfeFamily_limit v height B L hα p).mp hp
      exact (mem_rankedWolfeFamily_limit v height B L' hα p).mpr
        ⟨hb, hh, a, ha, hcof, c, fun n => ih _ (a n).property (hc n), hch⟩

/-- Finite-colour pruning retains the original root and every ordinal level.
The colour sets need not be closed: only rank-zero nodes must have the colour. -/
theorem rankedWolfeFamily_iUnion {ι : Type*} [Finite ι]
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B : Set P)
    (L : ι → Set P) (α : Ordinal.{u}) :
    rankedWolfeFamily v height B (⋃ i, L i) α =
      ⋃ i, rankedWolfeFamily v height B (L i) α := by
  apply subset_antisymm
  · induction α using Ordinal.limitRecOn with
    | zero =>
        intro p hp
        obtain ⟨hb, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B (⋃ i, L i) p).mp hp
        obtain ⟨i, hi⟩ := mem_iUnion.mp hl
        exact mem_iUnion.mpr ⟨i, (mem_rankedWolfeFamily_zero v height B (L i) p).mpr ⟨hb, hh, hi⟩⟩
    | succ α ih =>
        intro p hp
        obtain ⟨hb, hh, c, hc, hch⟩ :=
          (mem_rankedWolfeFamily_succ v height B (⋃ i, L i) α p).mp hp
        have hi (n : ℕ) : ∃ i, c n ∈ rankedWolfeFamily v height B (L i) α :=
          mem_iUnion.mp (ih (hc n))
        choose j hj using hi
        obtain ⟨i, f, hf, hfi⟩ := wolfe_finiteColor_subsequence j
        exact mem_iUnion.mpr ⟨i, (mem_rankedWolfeFamily_succ v height B (L i) α p).mpr
          ⟨hb, hh, (fun n => c (f n)),
            (fun n => by simpa only [hfi n] using hj (f n)), hch.subsequence hf⟩⟩
    | limit α hα ih =>
        intro p hp
        obtain ⟨hb, hh, a, ha, hcof, c, hc, hch⟩ :=
          (mem_rankedWolfeFamily_limit v height B (⋃ i, L i) hα p).mp hp
        have hi (n : ℕ) : ∃ i, c n ∈ rankedWolfeFamily v height B (L i) (a n).val :=
          mem_iUnion.mp (ih _ (a n).property (hc n))
        choose j hj using hi
        obtain ⟨i, f, hf, hfi⟩ := wolfe_finiteColor_subsequence j
        refine mem_iUnion.mpr ⟨i, (mem_rankedWolfeFamily_limit v height B (L i) hα p).mpr
          ⟨hb, hh, (fun n => a (f n)), ha.comp hf, ?_, (fun n => c (f n)),
            (fun n => by simpa only [hfi n] using hj (f n)), hch.subsequence hf⟩⟩
        intro β hβ
        obtain ⟨n, hn⟩ := hcof β hβ
        exact ⟨n, hn.trans (ha.monotone (hf.id_le n))⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact rankedWolfeFamily_mono_leaves v height B (subset_iUnion L i) α hi

end Posets

