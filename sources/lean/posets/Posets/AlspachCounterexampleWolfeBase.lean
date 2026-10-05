import Posets.AlspachCounterexampleWeakRows
import Posets.AlspachCounterexampleSuccessorMass
import Posets.WolfeMonotonicity

/-! The initial high-threshold Wolfe bound: above one half every admissible
open set must contain the shared distinguished atom, so two disjoint
children are impossible. -/

noncomputable section
open Set Order
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [Countable K] (p : K)

theorem alspachBase_wolfeBase_contains_root {ε : ℝ} (hε : 1 / 2 < ε)
    {q : WolfeNode 𝕜 K}
    (hq : q ∈ wolfeBase (AlspachCompactRows.base (𝕜 := 𝕜) K p).pointAtomicModel ε
      (Set.range (AlspachCompactRows.base (𝕜 := 𝕜) K p).weakRows)) : p ∈ q.2 := by
  obtain ⟨i, hi⟩ := hq.1
  have hm := hq.2.2
  rw [← hi, AlspachCompactRows.weakRows_mass] at hm
  change ε ≤ (alspachBaseRow p i).mass q.2 at hm
  by_contra hp
  exact (not_le_of_gt hε) (hm.trans (alspachBaseRow_mass_le_half hp))

theorem alspachBase_wolfeFamily_one_empty {ε : ℝ} (hε : 1 / 2 < ε) :
    wolfeFamily (AlspachCompactRows.base (𝕜 := 𝕜) K p).pointAtomicModel ε
      (Set.range (AlspachCompactRows.base (𝕜 := 𝕜) K p).weakRows) (1 : Ordinal) = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  have hq' : q ∈ wolfeFamily (AlspachCompactRows.base (𝕜 := 𝕜) K p).pointAtomicModel ε
      (Set.range (AlspachCompactRows.base (𝕜 := 𝕜) K p).weakRows) (Order.succ 0) := by
    simpa using hq
  obtain ⟨_, c, hc, hch⟩ := (mem_wolfeFamily_succ _ _ _ 0 q).mp hq'
  have hp (n : ℕ) : p ∈ (c n).2 := alspachBase_wolfeBase_contains_root p hε (by
    simpa only [wolfeFamily_zero] using hc n)
  exact Set.disjoint_left.mp (hch.2.1 (show (0 : ℕ) ≠ 1 by decide)) (hp 0) (hp 1)

theorem alspachBase_wolfeFamily_empty {ε : ℝ} (hε : 1 / 2 < ε)
    (α : Ordinal) (hα : 1 ≤ α) (hc : α.card ≤ Cardinal.aleph0) :
    wolfeFamily (AlspachCompactRows.base (𝕜 := 𝕜) K p).pointAtomicModel ε
      (Set.range (AlspachCompactRows.base (𝕜 := 𝕜) K p).weakRows) α = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  have hh := wolfeFamily_antitone_on_countable _ _ _ hc hα hq
  rw [alspachBase_wolfeFamily_one_empty p hε] at hh
  exact hh

end Posets
