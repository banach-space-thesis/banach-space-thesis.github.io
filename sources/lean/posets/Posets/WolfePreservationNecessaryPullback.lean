import Posets.WolfeDirac
import Posets.WolfeNorming

/-! A continuous support map gives genuine Wolfe witnesses by pulling back
the source neighborhoods. The hypothesis concerns the complete fibre of one
continuous map; arbitrary disjoint atomic owner sets do not suffice. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u
namespace Posets

variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [MetricSpace L] [Countable L]

theorem wolfePullback_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    (π : K → L) (hπ : Continuous π)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set L} (hA : IsClosed A) {ε : ℝ}
    (hmass : ∀ x ∈ A, ε ≤ wolfeMass M (μ x) (π ⁻¹' {x}))
    (α : Ordinal.{u}) (hc : α.card ≤ Cardinal.aleph0) :
    ∀ x ∈ ordinalDerived A α, ∀ U : Set L, IsOpen U → x ∈ U →
      (μ x, π ⁻¹' U) ∈ wolfeFamily M ε (μ '' A) α := by
  have hbase (x : L) (hx : x ∈ A) (U : Set L) (hU : IsOpen U) (hxU : x ∈ U) :
      (μ x, π ⁻¹' U) ∈ wolfeBase M ε (μ '' A) := by
    refine ⟨⟨x, hx, rfl⟩, hU.preimage hπ, (hmass x hx).trans ?_⟩
    exact wolfeMass_mono M (μ x) (preimage_mono (singleton_subset_iff.mpr hxU))
  have hchildren (x : L) (y : ℕ → L) (V : ℕ → Set L) (U : Set L)
      (hconv : Tendsto y atTop (𝓝 x))
      (hdisj : Pairwise (fun i j => Disjoint (V i) (V j)))
      (hclosure : closure (⋃ n, V n) ⊆ U) :
      WolfeChildren (μ x, π ⁻¹' U) (fun n => (μ (y n), π ⁻¹' V n)) := by
    refine ⟨hμ.continuousAt.tendsto.comp hconv,
      fun i j hij => (hdisj hij).preimage π, ?_⟩
    change closure (⋃ n, π ⁻¹' V n) ⊆ π ⁻¹' U
    rw [← preimage_iUnion]
    exact (hπ.closure_preimage_subset _).trans (preimage_mono hclosure)
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro x hx U hU hxU
      rw [wolfeFamily_zero]
      exact hbase x (by simpa using hx) U hU hxU
  | succ α ih =>
      intro x hx U hU hxU
      have hαc : α.card ≤ Cardinal.aleph0 := (Ordinal.card_le_card (le_succ α)).trans hc
      have hxA : x ∈ A := by
        simpa using ordinalDerived_antitone hA (show 0 ≤ succ α from bot_le) hx
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun _ => ordinalDerived A α) (fun _ => by simpa only [ordinalDerived_succ] using hx)
        hU hxU
      refine (mem_wolfeFamily_succ M ε (μ '' A) α _).mpr
        ⟨hbase x hxA U hU hxU, (fun n => (μ (y n), π ⁻¹' V n)), ?_,
          hchildren x y V U hconv hdisj hclosure⟩
      intro n
      exact ih hαc (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1
  | limit α hα ih =>
      intro x hx U hU hxU
      have hxA : x ∈ A := by
        simpa using ordinalDerived_antitone hA (show 0 ≤ α from bot_le) hx
      obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα hc
      have hacc (n : ℕ) : x ∈ derivedSet (ordinalDerived A (a n).val) := by
        rw [← ordinalDerived_succ]
        exact ordinalDerived_antitone hA (hα.succ_lt (a n).property).le hx
      obtain ⟨y, V, hy, hdisj, hconv, hclosure⟩ := exists_disjoint_open_point_sequence_closure
        (fun n => ordinalDerived A (a n).val) hacc hU hxU
      refine (mem_wolfeFamily_limit M ε (μ '' A) hα _).mpr
        ⟨hbase x hxA U hU hxU, a, ha, hcof,
          (fun n => (μ (y n), π ⁻¹' V n)), ?_, hchildren x y V U hconv hdisj hclosure⟩
      intro n
      exact ih (a n).val (a n).property ((Ordinal.card_le_card (a n).property.le).trans hc)
        (y n) (hy n).1 (V n) (hy n).2.2.1 (hy n).2.1

theorem wolfePullback_nonempty_of_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    (π : K → L) (hπ : Continuous π)
    (μ : L → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set L} (hA : IsClosed A) {ε : ℝ}
    (hmass : ∀ x ∈ A, ε ≤ wolfeMass M (μ x) (π ⁻¹' {x}))
    {α : Ordinal.{u}} (hc : α.card ≤ Cardinal.aleph0)
    (hne : (ordinalDerived A α).Nonempty) :
    (wolfeFamily M ε (μ '' A) α).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, wolfePullback_ordinalDerived M π hπ μ hμ hA hmass α hc
    x hx univ isOpen_univ (mem_univ _)⟩

end Posets
