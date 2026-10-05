import Posets.WolfeRankedClosure
import Posets.WolfePruning

/-! Set-theoretic gluing for countable, recursively pruned ranked families.
Strict descendant unions never cross disjoint immediate-child cells. -/
noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_mono_base (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) {B C : Set P} (hBC : B ⊆ C) (Leaves : Set P)
    (α : Ordinal.{u}) : rankedWolfeFamily v height B Leaves α ⊆ rankedWolfeFamily v height C Leaves α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro p hp
    obtain ⟨hb, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B Leaves p).mp hp
    exact (mem_rankedWolfeFamily_zero v height C Leaves p).mpr ⟨hBC hb, hh, hl⟩
  | succ α ih =>
    intro p hp
    obtain ⟨hb, hh, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp
    exact (mem_rankedWolfeFamily_succ v height C Leaves α p).mpr
      ⟨hBC hb, hh, c, fun n => ih (hc n), hch⟩
  | limit α hα ih =>
    intro p hp
    obtain ⟨hb, hh, a, ha, hcof, c, hc, hch⟩ :=
      (mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp
    exact (mem_rankedWolfeFamily_limit v height C Leaves hα p).mpr
      ⟨hBC hb, hh, a, ha, hcof, c, fun n => ih _ (a n).property (hc n), hch⟩

def rankedWolfeDescendantUnion (v : P → WolfeNode 𝕜 K) (C : Set P) (p : P) : Set K :=
  {x | ∃ q ∈ C, (v q).2 ⊂ (v p).2 ∧ x ∈ (v q).2}

theorem rankedWolfeDescendantUnion_singleton (v : P → WolfeNode 𝕜 K) (p : P) :
    rankedWolfeDescendantUnion v {p} p = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨q, hq, hh, _⟩
  rcases mem_singleton_iff.mp hq with rfl
  exact (lt_irrefl _ hh)

theorem rankedWolfeDescendantUnion_root_subset (v : P → WolfeNode 𝕜 K) (p : P)
    (C : ℕ → Set P) (U : ℕ → Set K)
    (hC : ∀ n q, q ∈ C n → (v q).2 ⊆ U n) :
    rankedWolfeDescendantUnion v (insert p (⋃ n, C n)) p ⊆ ⋃ n, U n := by
  rintro x ⟨q, hq, hh, hx⟩
  rcases mem_insert_iff.mp hq with rfl | hq
  · exact False.elim (lt_irrefl _ hh)
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨n, hC n q hn hx⟩

theorem rankedWolfeDescendantUnion_child_subset (v : P → WolfeNode 𝕜 K) (p : P)
    (C : ℕ → Set P) (U : ℕ → Set K)
    (hC : ∀ n q, q ∈ C n → (v q).2 ⊆ U n)
    (hU : ∀ n, U n ⊆ (v p).2) (hd : Pairwise fun n m => Disjoint (U n) (U m))
    (hne : ∀ n q, q ∈ C n → (v q).2.Nonempty)
    {n : ℕ} {q : P} (hq : q ∈ C n) :
    rankedWolfeDescendantUnion v (insert p (⋃ m, C m)) q ⊆ rankedWolfeDescendantUnion v (C n) q := by
  rintro x ⟨r, hr, hrq, hx⟩
  rcases mem_insert_iff.mp hr with rfl | hr
  · exact False.elim (hrq.2 ((hC n q hq).trans (hU n)))
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hr
    by_cases hmn : m = n
    · subst m
      exact ⟨r, hm, hrq, hx⟩
    · obtain ⟨y, hy⟩ := hne m r hm
      exact False.elim (Set.disjoint_left.mp (hd hmn)
        (hC m r hm hy) (hC n q hq (hrq.1 hy)))

end Posets
