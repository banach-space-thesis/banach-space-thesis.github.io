import Posets.WolfePositiveMixture
import Mathlib.Topology.Sequences

/-! Compact positive row families lift a base mass selection to every Wolfe
level. The selected limit row need not equal the original root measure.
Closure containment and positivity retain its mass in the parent open set. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [TopologicalSpace P] [SeqCompactSpace P]

theorem wolfe_positive_compact_selection
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (q : P → AlspachProbability K)
    (hq : Continuous (fun p => wolfeProbabilityRow M (q p)))
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) {ε δ : ℝ}
    (hselect : ∀ μ ∈ B, ∀ U : Set K, IsOpen U → ε ≤ wolfeMass M μ U →
      ∃ p : P, δ ≤ (q p).mass U)
    (α : Ordinal.{u}) : ∀ z ∈ wolfeFamily M ε B α,
      ∃ p : P, (wolfeProbabilityRow M (q p), z.2) ∈
        wolfeFamily M δ (range (fun p => wolfeProbabilityRow M (q p))) α := by
  classical
  let Q := fun p => wolfeProbabilityRow M (q p)
  have hm (p : P) (U : Set K) : wolfeMass M (Q p) U = (q p).mass U :=
    (q p).wolfeMass_probability M U
  have hparent (z : WolfeNode 𝕜 K) (hz : IsOpen z.2)
      (c : ℕ → WolfeNode 𝕜 K) (hch : WolfeChildren z c)
      (s : ℕ → P) (p : P) (g : ℕ → ℕ) (hg : StrictMono g)
      (hlim : Tendsto (s ∘ g) atTop (𝓝 p))
      (hδ : ∀ n, δ ≤ wolfeMass M (Q (s (g n))) (c (g n)).2) :
      (Q p, z.2) ∈ wolfeBase M δ (range Q) ∧
        WolfeChildren (Q p, z.2) (fun n => (Q (s (g n)), (c (g n)).2)) := by
    have ht : Tendsto (fun n => Q (s (g n))) atTop (𝓝 (Q p)) :=
      hq.continuousAt.tendsto.comp hlim
    have hc := hch.subsequence hg
    refine ⟨⟨mem_range_self p, hz, ?_⟩, ht, hc.2⟩
    rw [hm]
    exact wolfe_probability_mass_le_of_children M hK (fun n => q (s (g n))) (q p)
      ht (fun n => (c (g n)).2) hz hc.2.2 (fun n => by rw [← hm]; exact hδ n)
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro z hz
      have hb := wolfeFamily_subset_base M ε B 0 hz
      obtain ⟨p, hp⟩ := hselect z.1 hb.1 z.2 hb.2.1 hb.2.2
      refine ⟨p, ?_⟩
      rw [wolfeFamily_zero]
      exact ⟨mem_range_self p, hb.2.1, (hm p z.2).symm ▸ hp⟩
  | succ α ih =>
      intro z hz
      obtain ⟨hb, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B α z).mp hz
      choose s hs using fun n => ih (c n) (hc n)
      obtain ⟨p, g, hg, hlim⟩ := SeqCompactSpace.tendsto_subseq s
      have hd (n : ℕ) := (wolfeFamily_subset_base M δ (range Q) α (hs (g n))).2.2
      obtain ⟨hbase, hchildren⟩ := hparent z hb.2.1 c hch s p g hg hlim hd
      exact ⟨p, (mem_wolfeFamily_succ M δ (range Q) α _).mpr
        ⟨hbase, _, (fun n => hs (g n)), hchildren⟩⟩
  | limit α hα ih =>
      intro z hz
      obtain ⟨hb, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα z).mp hz
      choose s hs using fun n => ih (a n).val (a n).property (c n) (hc n)
      obtain ⟨p, g, hg, hlim⟩ := SeqCompactSpace.tendsto_subseq s
      have hd (n : ℕ) := (wolfeFamily_subset_base M δ (range Q) _ (hs (g n))).2.2
      obtain ⟨hbase, hchildren⟩ := hparent z hb.2.1 c hch s p g hg hlim hd
      refine ⟨p, (mem_wolfeFamily_limit M δ (range Q) hα _).mpr
        ⟨hbase, (fun n => a (g n)), ha.comp hg, ?_, _, (fun n => hs (g n)), hchildren⟩⟩
      intro β hβ
      obtain ⟨n, hn⟩ := hcof β hβ
      exact ⟨n, hn.trans (ha.monotone (hg.id_le n))⟩

end Posets
