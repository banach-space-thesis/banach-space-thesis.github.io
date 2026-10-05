import ThesisCommon.Analysis.PositiveMatrix
import Mathlib.Tactic

/-! Infinite subsets with infinite remainders and uniform scalar approximation. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon

theorem infinite_coinfinite_subset {α : Type*} (C : Set α) (hC : C.Infinite) :
    ∃ J : Set α, J ⊆ C ∧ J.Infinite ∧ (C \ J).Infinite := by
  let q : ℕ → α := fun n => (hC.natEmbedding C n).val
  have hq : Function.Injective q := Subtype.val_injective.comp (hC.natEmbedding C).injective
  let even : ℕ → α := fun n => q (2 * n)
  let odd : ℕ → α := fun n => q (2 * n + 1)
  have heven : Function.Injective even := fun i j h => by
    have := hq h
    omega
  have hodd : Function.Injective odd := fun i j h => by
    have := hq h
    omega
  refine ⟨Set.range even, ?_, Set.infinite_range_of_injective heven, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hC.natEmbedding C (2*n)).property
  · apply (Set.infinite_range_of_injective hodd).mono
    rintro _ ⟨n, rfl⟩
    refine ⟨(hC.natEmbedding C (2*n+1)).property, ?_⟩
    rintro ⟨m, hm⟩
    have := hq hm
    omega

theorem bounded_sequence_uniform_infinite_subset (u : ℕ → ℝ) (b : ℝ)
    (hb : ∀ n, b ≤ u n ∧ u n ≤ 1) (C : Set ℕ) (hC : C.Infinite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : Set ℕ) (a : ℝ), J ⊆ C ∧ J.Infinite ∧ (C \ J).Infinite ∧
      b ≤ a ∧ ∀ n ∈ J, |u n - a| < δ := by
  obtain ⟨D, hDC, hD, hCD⟩ := infinite_coinfinite_subset C hC
  let q : ℕ → ℕ := fun n => (hD.natEmbedding D n).val
  have hq : Function.Injective q := Subtype.val_injective.comp (hD.natEmbedding D).injective
  let v : ℕ → Set.Icc b 1 := fun n => ⟨u (q n), hb _⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq v
  have hlim' : Tendsto (fun n => u (q (φ n))) atTop (𝓝 a.val) :=
    (continuous_subtype_val.tendsto a).comp hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim' δ hδ
  let r : ℕ → ℕ := fun n => q (φ (n + N))
  have hr : Function.Injective r := hq.comp (hφ.injective.comp (fun i j h => Nat.add_right_cancel h))
  have hrD : Set.range r ⊆ D := by
    rintro _ ⟨n, rfl⟩
    exact (hD.natEmbedding D _).property
  refine ⟨Set.range r, a.val, hrD.trans hDC, Set.infinite_range_of_injective hr,
    hCD.mono ?_, a.property.1, ?_⟩
  · intro n hn
    exact ⟨hn.1, fun h => hn.2 (hrD h)⟩
  · rintro _ ⟨n, rfl⟩
    simpa only [Real.dist_eq] using hN (n+N) (Nat.le_add_left N n)

end ThesisCommon
