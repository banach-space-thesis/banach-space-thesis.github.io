import Posets.WolfeRankedSelectedSets
import Posets.WolfeOperatorRows

/-! Changing rows by a continuous weak-star map preserves every ranked
family. Restricting the base to nodes which already have their assigned rank
preserves the full family and records the hereditary leaf condition. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_transport
    (v w : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (hchildren : ∀ (p : P) (c : ℕ → P), WolfeChildren (v p) (fun n => v (c n)) →
      WolfeChildren (w p) (fun n => w (c n))) (α : Ordinal.{u}) :
    rankedWolfeFamily v height B Leaves α ⊆ rankedWolfeFamily w height B Leaves α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro p hp
    exact (mem_rankedWolfeFamily_zero w height B Leaves p).mpr
      ((mem_rankedWolfeFamily_zero v height B Leaves p).mp hp)
  | succ α ih =>
    intro p hp
    obtain ⟨hb, hh, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp
    exact (mem_rankedWolfeFamily_succ w height B Leaves α p).mpr
      ⟨hb, hh, c, fun n => ih (hc n), hchildren p c hch⟩
  | limit α hα ih =>
    intro p hp
    obtain ⟨hb, hh, a, ha, hcof, c, hc, hch⟩ :=
      (mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp
    exact (mem_rankedWolfeFamily_limit w height B Leaves hα p).mpr
      ⟨hb, hh, a, ha, hcof, c, fun n => ih _ (a n).property (hc n), hchildren p c hch⟩

theorem rankedWolfeFamily_map_rows
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (f : WeakDual 𝕜 (JLMS.CZero 𝕜 K) → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hf : Continuous f) (α : Ordinal.{u}) :
    rankedWolfeFamily v height B Leaves α ⊆
      rankedWolfeFamily (fun p => (f (v p).1, (v p).2)) height B Leaves α := by
  apply rankedWolfeFamily_transport
  intro p c hc
  exact ⟨hf.continuousAt.tendsto.comp hc.1, hc.2⟩

theorem rankedWolfeFamily_operator_rows
    (point : P → K) (cell : P → Set K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K) (α : Ordinal.{u}) :
    rankedWolfeFamily (fun p => (wolfeDirac (𝕜 := 𝕜) (point p), cell p)) height B Leaves α ⊆
      rankedWolfeFamily (fun p => (wolfeOperatorRow T (point p), cell p)) height B Leaves α :=
  rankedWolfeFamily_map_rows _ height B Leaves (weakStarAdjoint T)
    (weakStarAdjoint_continuous T) α

theorem rankedWolfeFamily_mono_zero_leaves
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B : Set P)
    {L L' : Set P} (hL : ∀ p ∈ B, height p = 0 → p ∈ L → p ∈ L')
    (α : Ordinal.{u}) : rankedWolfeFamily v height B L α ⊆ rankedWolfeFamily v height B L' α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro p hp
    obtain ⟨hb, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B L p).mp hp
    exact (mem_rankedWolfeFamily_zero v height B L' p).mpr ⟨hb, hh, hL p hb hh hl⟩
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

def rankedWolfeHereditaryBase
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P) : Set P :=
  {p | p ∈ rankedWolfeFamily v height B Leaves (height p)}

theorem rankedWolfeHereditaryBase_subset
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P) :
    rankedWolfeHereditaryBase v height B Leaves ⊆ B := by
  intro p hp
  exact (rankedWolfeFamily_base_height v height B Leaves (height p) hp).1

theorem rankedWolfeFamily_restrict_hereditary
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (α : Ordinal.{u}) :
    rankedWolfeFamily v height (rankedWolfeHereditaryBase v height B Leaves) Leaves α =
      rankedWolfeFamily v height B Leaves α := by
  apply subset_antisymm
  · exact rankedWolfeFamily_mono_base v height
      (rankedWolfeHereditaryBase_subset v height B Leaves) Leaves α
  · induction α using Ordinal.limitRecOn with
    | zero =>
      intro p hp
      obtain ⟨_, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B Leaves p).mp hp
      refine (mem_rankedWolfeFamily_zero v height _ Leaves p).mpr ⟨?_, hh, hl⟩
      change p ∈ rankedWolfeFamily v height B Leaves (height p)
      simpa only [hh] using hp
    | succ α ih =>
      intro p hp
      obtain ⟨_, hh, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B Leaves α p).mp hp
      refine (mem_rankedWolfeFamily_succ v height _ Leaves α p).mpr
        ⟨?_, hh, c, fun n => ih (hc n), hch⟩
      change p ∈ rankedWolfeFamily v height B Leaves (height p)
      simpa only [hh] using hp
    | limit α hα ih =>
      intro p hp
      obtain ⟨_, hh, a, ha, hcof, c, hc, hch⟩ :=
        (mem_rankedWolfeFamily_limit v height B Leaves hα p).mp hp
      refine (mem_rankedWolfeFamily_limit v height _ Leaves hα p).mpr
        ⟨?_, hh, a, ha, hcof, c, fun n => ih _ (a n).property (hc n), hch⟩
      change p ∈ rankedWolfeFamily v height B Leaves (height p)
      simpa only [hh] using hp

end Posets
