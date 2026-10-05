import Posets.WolfePruning

/-! Every Wolfe witness admits recursive pruning so that each node assigns
small total mass to all of its children. Descendants lie inside these children,
so the estimate controls their entire union as well. No ordinal level or mass
threshold is lost by this pruning. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

def wolfePrunedFamily (M : JLMS.AtomicDualModel 𝕜 K) (ε η : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) : Set (WolfeNode 𝕜 K) :=
  Ordinal.limitRecOn α (wolfeBase M ε B)
    (fun _ P => {p | p ∈ wolfeBase M ε B ∧ ∃ c : ℕ → WolfeNode 𝕜 K,
      (∀ n, c n ∈ P) ∧ WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η})
    (fun α _ P => {p | p ∈ wolfeBase M ε B ∧
      ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧ ∃ c : ℕ → WolfeNode 𝕜 K,
          (∀ n, c n ∈ P (a n).val (a n).property) ∧
            WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η})

@[simp] theorem wolfePrunedFamily_zero (M : JLMS.AtomicDualModel 𝕜 K) (ε η : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) :
    wolfePrunedFamily M ε η B (0 : Ordinal.{u}) = wolfeBase M ε B := by
  simp [wolfePrunedFamily]

theorem mem_wolfePrunedFamily_succ (M : JLMS.AtomicDualModel 𝕜 K) (ε η : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) (p : WolfeNode 𝕜 K) :
    p ∈ wolfePrunedFamily M ε η B (succ α) ↔
      p ∈ wolfeBase M ε B ∧ ∃ c : ℕ → WolfeNode 𝕜 K,
        (∀ n, c n ∈ wolfePrunedFamily M ε η B α) ∧
          WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η := by
  simp [wolfePrunedFamily]

theorem mem_wolfePrunedFamily_limit (M : JLMS.AtomicDualModel 𝕜 K) (ε η : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) {α : Ordinal.{u}} (hα : IsSuccLimit α)
    (p : WolfeNode 𝕜 K) : p ∈ wolfePrunedFamily M ε η B α ↔
      p ∈ wolfeBase M ε B ∧ ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧ ∃ c : ℕ → WolfeNode 𝕜 K,
          (∀ n, c n ∈ wolfePrunedFamily M ε η B (a n).val) ∧
            WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η := by
  unfold wolfePrunedFamily
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]
  rfl

/-- Recursive small-descendant-mass pruning is available at every ordinal. -/
theorem wolfePrunedFamily_eq (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    {η : ℝ} (hη : 0 < η) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (α : Ordinal.{u}) : wolfePrunedFamily M ε η B α = wolfeFamily M ε B α := by
  induction α using Ordinal.limitRecOn with
  | zero => simp only [wolfePrunedFamily_zero, wolfeFamily_zero]
  | succ α ih =>
      ext p
      constructor
      · intro hp
        obtain ⟨hb, c, hc, hch, _⟩ := (mem_wolfePrunedFamily_succ M ε η B α p).mp hp
        exact (mem_wolfeFamily_succ M ε B α p).mpr
          ⟨hb, c, (fun n => by simpa only [ih] using hc n), hch⟩
      · intro hp
        obtain ⟨c, hc, hch, hsmall⟩ := wolfeFamily_successor_small_children M hη B α hp
        exact (mem_wolfePrunedFamily_succ M ε η B α p).mpr
          ⟨wolfeFamily_subset_base M ε B (succ α) hp, c,
            (fun n => by simpa only [ih] using hc n), hch, hsmall⟩
  | limit α hα ih =>
      ext p
      constructor
      · intro hp
        obtain ⟨hb, a, ha, hcof, c, hc, hch, _⟩ :=
          (mem_wolfePrunedFamily_limit M ε η B hα p).mp hp
        exact (mem_wolfeFamily_limit M ε B hα p).mpr
          ⟨hb, a, ha, hcof, c,
            (fun n => by simpa only [ih (a n).val (a n).property] using hc n), hch⟩
      · intro hp
        obtain ⟨a, ha, hcof, c, hc, hch, hsmall⟩ := wolfeFamily_limit_small_children M hη B hα hp
        exact (mem_wolfePrunedFamily_limit M ε η B hα p).mpr
          ⟨wolfeFamily_subset_base M ε B α hp, a, ha, hcof, c,
            (fun n => by simpa only [ih (a n).val (a n).property] using hc n), hch, hsmall⟩

end Posets
