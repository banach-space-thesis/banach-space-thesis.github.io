import Posets.WolfeSequenceRefinement
import Posets.WolfeMassBounds
import Mathlib.Topology.Sequences

/-! Wolfe witnesses lift through a sequentially compact parameter space
when the two continuous row families satisfy a uniform setwise mass bound.
The lifted root keeps its image row, rather than an arbitrarily chosen
preimage. A convergent subsequence is selected at every nonzero node. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace P] [SeqCompactSpace P]

theorem wolfe_compact_mass_transport
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ σ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hμ : Continuous μ) (hσ : Continuous σ) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ p U, wolfeMass M (σ p) U ≤ C * wolfeMass M (μ p) U)
    (ε : ℝ) (α : Ordinal.{u}) :
    ∀ z ∈ wolfeFamily M ε (range σ) α,
      ∃ p : P, σ p = z.1 ∧ (μ p, z.2) ∈ wolfeFamily M (ε / C) (range μ) α := by
  classical
  have hbase (z : WolfeNode 𝕜 K) (hz : z ∈ wolfeBase M ε (range σ))
      (p : P) (hp : σ p = z.1) :
      (μ p, z.2) ∈ wolfeBase M (ε / C) (range μ) := by
    refine ⟨mem_range_self p, hz.2.1, (div_le_iff₀ hC).mpr ?_⟩
    calc
      ε ≤ wolfeMass M (σ p) z.2 := by rw [hp]; exact hz.2.2
      _ ≤ C * wolfeMass M (μ p) z.2 := hbound p z.2
      _ = wolfeMass M (μ p) z.2 * C := mul_comm _ _
  have hparent (z : WolfeNode 𝕜 K) (c : ℕ → WolfeNode 𝕜 K)
      (hch : WolfeChildren z c) (s : ℕ → P) (hs : ∀ n, σ (s n) = (c n).1)
      (p : P) (g : ℕ → ℕ) (hg : StrictMono g)
      (hlim : Tendsto (s ∘ g) atTop (𝓝 p)) :
      σ p = z.1 ∧
        WolfeChildren (μ p, z.2) (fun n => (μ (s (g n)), (c (g n)).2)) := by
    have hσlim : Tendsto (fun n => σ (s (g n))) atTop (𝓝 (σ p)) :=
      hσ.continuousAt.tendsto.comp hlim
    have hzlim : Tendsto (fun n => σ (s (g n))) atTop (𝓝 z.1) := by
      simpa only [hs] using hch.1.comp hg.tendsto_atTop
    refine ⟨tendsto_nhds_unique hσlim hzlim, ?_⟩
    exact ⟨hμ.continuousAt.tendsto.comp hlim, (hch.subsequence hg).2⟩
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro z hz
      have hb := wolfeFamily_subset_base M ε (range σ) 0 hz
      obtain ⟨p, hp⟩ := hb.1
      exact ⟨p, hp, by simpa only [wolfeFamily_zero] using hbase z hb p hp⟩
  | succ α ih =>
      intro z hz
      obtain ⟨hb, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε (range σ) α z).mp hz
      choose s hs hw using fun n => ih (c n) (hc n)
      obtain ⟨p, g, hg, hlim⟩ := SeqCompactSpace.tendsto_subseq s
      obtain ⟨hp, hchildren⟩ := hparent z c hch s hs p g hg hlim
      exact ⟨p, hp, (mem_wolfeFamily_succ M (ε / C) (range μ) α _).mpr
        ⟨hbase z hb p hp, _, (fun n => hw (g n)), hchildren⟩⟩
  | limit α hα ih =>
      intro z hz
      obtain ⟨hb, a, ha, hcof, c, hc, hch⟩ :=
        (mem_wolfeFamily_limit M ε (range σ) hα z).mp hz
      choose s hs hw using fun n => ih (a n).val (a n).property (c n) (hc n)
      obtain ⟨p, g, hg, hlim⟩ := SeqCompactSpace.tendsto_subseq s
      obtain ⟨hp, hchildren⟩ := hparent z c hch s hs p g hg hlim
      refine ⟨p, hp, (mem_wolfeFamily_limit M (ε / C) (range μ) hα _).mpr
        ⟨hbase z hb p hp, (fun n => a (g n)), ha.comp hg, ?_, _,
          (fun n => hw (g n)), hchildren⟩⟩
      intro β hβ
      obtain ⟨n, hn⟩ := hcof β hβ
      exact ⟨n, hn.trans (ha.monotone (hg.id_le n))⟩

theorem wolfe_compact_mass_transport_nonempty
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ σ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hμ : Continuous μ) (hσ : Continuous σ) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ p U, wolfeMass M (σ p) U ≤ C * wolfeMass M (μ p) U)
    (ε : ℝ) (α : Ordinal.{u})
    (hne : (wolfeFamily M ε (range σ) α).Nonempty) :
    (wolfeFamily M (ε / C) (range μ) α).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨p, _, hp⟩ := wolfe_compact_mass_transport M μ σ hμ hσ hC hbound ε α z hz
  exact ⟨(μ p, z.2), hp⟩

end Posets
