import Posets.WolfePositiveLimits
import Posets.WolfeClosedCover

/-! Pullback of every Wolfe level through a fixed finite positive mixture.
The source and target mass thresholds may differ, and the mass selection may
hold only inside a prescribed window. Closure containment retains the chosen
positive component's mass at successor and limit roots. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

def wolfeProbabilityRow {K : Type*} [TopologicalSpace K]
    (M : JLMS.AtomicDualModel 𝕜 K) (p : AlspachProbability K) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) :=
  StrongDual.toWeakDual (M.representation.symm p.vector)

section Pullback
variable {X Y P I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] [Finite I]
    [CompactSpace X] [T2Space X]
    (M : JLMS.AtomicDualModel 𝕜 X) (N : JLMS.AtomicDualModel 𝕜 Y)
    (hX : JLMS.IsScattered X)
    (q : P → AlspachProbability X) (r : P → AlspachProbability Y)
    (f : I → X → Y) (hf : ∀ i, Continuous (f i))
    (hq : Continuous (fun p => wolfeProbabilityRow M (q p)))
    (hr : IsEmbedding (fun p => wolfeProbabilityRow N (r p)))

include hX hf hq hr in
theorem wolfe_positive_mixture_pullback {ε δ : ℝ} (C : Set Y)
    (hselect : ∀ p : P, ∀ U : Set Y, IsOpen U → U ⊆ C →
      ε ≤ (r p).mass U → ∃ i : I, δ ≤ (q p).mass (f i ⁻¹' U))
    (α : Ordinal.{u}) : ∀ p : P, ∀ G : Set Y, G ⊆ C →
      (wolfeProbabilityRow N (r p), G) ∈
        wolfeFamily N ε (range (fun p => wolfeProbabilityRow N (r p))) α →
      ∃ i : I, (wolfeProbabilityRow M (q p), f i ⁻¹' G) ∈
        wolfeFamily M δ (range (fun p => wolfeProbabilityRow M (q p))) α := by
  classical
  let R := fun p => wolfeProbabilityRow N (r p)
  let Q := fun p => wolfeProbabilityRow M (q p)
  have hmassN (p : P) (G : Set Y) : wolfeMass N (R p) G = (r p).mass G :=
    (r p).wolfeMass_probability N G
  have hmassM (p : P) (G : Set X) : wolfeMass M (Q p) G = (q p).mass G :=
    (q p).wolfeMass_probability M G
  have hchildren (p : P) (G : Set Y) (c : ℕ → WolfeNode 𝕜 Y)
      (hch : WolfeChildren (R p, G) c) (s : ℕ → P) (hs : ∀ n, R (s n) = (c n).1)
      (i : I) (g : ℕ → ℕ) (hg : StrictMono g) :
      WolfeChildren (Q p, f i ⁻¹' G)
        (fun n => (Q (s (g n)), f i ⁻¹' (c (g n)).2)) := by
    have ht : Tendsto s atTop (𝓝 p) := hr.tendsto_nhds_iff.mpr (by
      change Tendsto (fun n => R (s n)) atTop (𝓝 (R p))
      simpa only [hs] using hch.1)
    refine ⟨hq.continuousAt.tendsto.comp (ht.comp hg.tendsto_atTop), ?_, ?_⟩
    · intro j k hjk
      exact (hch.2.1 (hg.injective.ne hjk)).preimage (f i)
    · change closure (⋃ n, f i ⁻¹' (c (g n)).2) ⊆ f i ⁻¹' G
      rw [← preimage_iUnion]
      exact ((hf i).closure_preimage_subset _).trans
        (preimage_mono (hch.subsequence hg).2.2)
  have hparent (p : P) (G : Set Y) (hG : IsOpen G) (s : ℕ → P)
      (i : I) (U : ℕ → Set X)
      (hch : WolfeChildren (Q p, f i ⁻¹' G) (fun n => (Q (s n), U n)))
      (hm : ∀ n, δ ≤ wolfeMass M (Q (s n)) (U n)) :
      (Q p, f i ⁻¹' G) ∈ wolfeBase M δ (range Q) := by
    refine ⟨mem_range_self p, hG.preimage (hf i), ?_⟩
    rw [hmassM]
    exact wolfe_probability_mass_le_of_children M hX (fun n => q (s n)) (q p)
      hch.1 U (hG.preimage (hf i)) hch.2.2
        (fun n => by simpa only [hmassM] using hm n)
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p G hGC hp
      have hb := wolfeFamily_subset_base N ε (range R) 0 hp
      obtain ⟨i, hi⟩ := hselect p G hb.2.1 hGC (by rw [← hmassN]; exact hb.2.2)
      refine ⟨i, ?_⟩
      rw [wolfeFamily_zero]
      exact ⟨mem_range_self p, hb.2.1.preimage (hf i), (hmassM p _).symm ▸ hi⟩
  | succ α ih =>
      intro p G hGC hp
      obtain ⟨hb, c, hc, hch⟩ := (mem_wolfeFamily_succ N ε (range R) α (R p, G)).mp hp
      have hex (n : ℕ) : ∃ z : P, R z = (c n).1 :=
        (wolfeFamily_subset_base N ε (range R) α (hc n)).1
      choose s hs using hex
      have hi (n : ℕ) : ∃ i : I, (Q (s n), f i ⁻¹' (c n).2) ∈
          wolfeFamily M δ (range Q) α := by
        apply ih (s n) (c n).2 ((hch.child_subset n).trans hGC)
        have he : (R (s n), (c n).2) = c n := Prod.ext (hs n) rfl
        rw [he]
        exact hc n
      choose j hj using hi
      obtain ⟨i, g, hg, hgi⟩ := wolfe_finiteColor_subsequence j
      have hc' (n : ℕ) : (Q (s (g n)), f i ⁻¹' (c (g n)).2) ∈
          wolfeFamily M δ (range Q) α := by simpa only [hgi n] using hj (g n)
      have hch' := hchildren p G c hch s hs i g hg
      refine ⟨i, (mem_wolfeFamily_succ M δ (range Q) α _).mpr
        ⟨?_, _, hc', hch'⟩⟩
      exact hparent p G hb.2.1 (fun n => s (g n)) i (fun n => f i ⁻¹' (c (g n)).2) hch'
        (fun n => (wolfeFamily_subset_base M δ (range Q) α (hc' n)).2.2)
  | limit α hα ih =>
      intro p G hGC hp
      obtain ⟨hb, a, ha, hcof, c, hc, hch⟩ :=
        (mem_wolfeFamily_limit N ε (range R) hα (R p, G)).mp hp
      have hex (n : ℕ) : ∃ z : P, R z = (c n).1 :=
        (wolfeFamily_subset_base N ε (range R) (a n).val (hc n)).1
      choose s hs using hex
      have hi (n : ℕ) : ∃ i : I, (Q (s n), f i ⁻¹' (c n).2) ∈
          wolfeFamily M δ (range Q) (a n).val := by
        apply ih (a n).val (a n).property (s n) (c n).2 ((hch.child_subset n).trans hGC)
        have he : (R (s n), (c n).2) = c n := Prod.ext (hs n) rfl
        rw [he]
        exact hc n
      choose j hj using hi
      obtain ⟨i, g, hg, hgi⟩ := wolfe_finiteColor_subsequence j
      have hc' (n : ℕ) : (Q (s (g n)), f i ⁻¹' (c (g n)).2) ∈
          wolfeFamily M δ (range Q) (a (g n)).val := by simpa only [hgi n] using hj (g n)
      have hch' := hchildren p G c hch s hs i g hg
      refine ⟨i, (mem_wolfeFamily_limit M δ (range Q) hα _).mpr
        ⟨?_, (fun n => a (g n)), ha.comp hg, ?_, _, hc', hch'⟩⟩
      · exact hparent p G hb.2.1 (fun n => s (g n)) i (fun n => f i ⁻¹' (c (g n)).2) hch'
          (fun n => (wolfeFamily_subset_base M δ (range Q) _ (hc' n)).2.2)
      · intro β hβ
        obtain ⟨n, hn⟩ := hcof β hβ
        exact ⟨n, hn.trans (ha.monotone (hg.id_le n))⟩

end Pullback
end Posets
