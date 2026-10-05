import Posets.WolfeLaminarDisjointSum
import Posets.WolfeRankedCrossMassSets

/-! The finite-span estimate after cross-block pruning. The local outside
mass and cross-block mass add, while disjoint roots preserve laminarity. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfe_disjointBlocks_outside_bound
    (M : JLMS.AtomicDualModel 𝕜 K) (H : ℕ → Set K)
    (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (i : ℕ) (A : Set K) {ε : ℝ}
    (hloc : wolfeMass M μ (H i \ A) ≤ ε)
    (hcross : wolfeMass M μ (wolfeCrossUnion H i) ≤ ε) :
    wolfeMass M μ ((⋃ j, H j) \ A) ≤ 2 * ε := by
  have hsub : (⋃ j, H j) \ A ⊆ (H i \ A) ∪ wolfeCrossUnion H i := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx.1
    by_cases hji : j = i
    · exact Or.inl ⟨hji ▸ hj, hx.2⟩
    · exact Or.inr ((mem_wolfeCrossUnion H i x).mpr ⟨j, hji, hj⟩)
  have hd : Disjoint (H i \ A) (wolfeCrossUnion H i) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, hji, hj⟩ := (mem_wolfeCrossUnion H i x).mp hy
    exact Set.disjoint_left.mp (hH hji) hj hx.1
  have h := wolfeMass_mono M μ hsub
  rw [wolfeMass_union M μ hd] at h
  linarith

theorem wolfe_disjointBlocks_laminar {I : Type*} {ι : I → Type*}
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (A : ∀ i, ι i → Set K) (hAH : ∀ i j, A i j ⊆ H i)
    (hlam : ∀ i j k, A i j ⊆ A i k ∨ A i k ⊆ A i j ∨ Disjoint (A i j) (A i k)) :
    ∀ q r : Sigma ι, A q.1 q.2 ⊆ A r.1 r.2 ∨ A r.1 r.2 ⊆ A q.1 q.2 ∨
      Disjoint (A q.1 q.2) (A r.1 r.2) := by
  rintro ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k
  · subst k
    exact hlam i j l
  · right; right
    exact Set.disjoint_left.mpr (fun x hx hy =>
      Set.disjoint_left.mp (hH hik) (hAH i j hx) (hAH k l hy))

theorem wolfe_disjointBlocks_descendants {I : Type*} {ι : I → Type*}
    (H : I → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (A E : ∀ i, ι i → Set K) (hAH : ∀ i j, A i j ⊆ H i)
    (hne : ∀ i j, (A i j).Nonempty)
    (hdesc : ∀ i j k, A i k ⊂ A i j → A i k ⊆ E i j) :
    ∀ q r : Sigma ι, A r.1 r.2 ⊂ A q.1 q.2 → A r.1 r.2 ⊆ E q.1 q.2 := by
  rintro ⟨i, j⟩ ⟨k, l⟩ hsub
  by_cases hik : i = k
  · subst k
    exact hdesc i j l hsub
  · obtain ⟨x, hx⟩ := hne k l
    exact (Set.disjoint_left.mp (hH hik) (hAH i j (hsub.1 hx)) (hAH k l hx)).elim

theorem wolfe_disjointBlocks_sum_lower_bound [CompactSpace K] [Nonempty K]
    {ι : ℕ → Type*} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : JLMS.AtomicDualModel 𝕜 K) (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (H : ℕ → Set K) (hH : Pairwise (fun i j => Disjoint (H i) (H j)))
    (A E : ∀ i, ι i → Set K) (μ : ∀ i, ι i → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hA : ∀ i j, IsClopen (A i j)) (hcA : ∀ i j, IsCompact (A i j))
    (hAH : ∀ i j, A i j ⊆ H i) (hne : ∀ i j, (A i j).Nonempty)
    (hlam : ∀ i j k, A i j ⊆ A i k ∨ A i k ⊆ A i j ∨ Disjoint (A i j) (A i k))
    (hdesc : ∀ i j k, A i k ⊂ A i j → A i k ⊆ E i j)
    (hμ : ∀ i j, μ i j ∈ adjointUnitBall T) {ell ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i j, ell ≤ ‖μ i j (JLMS.clopenIndicator (𝕜 := 𝕜) (A i j) (hA i j) (hcA i j))‖)
    (houtside : ∀ i j, wolfeMass M (μ i j) (H i \ A i j) ≤ ε)
    (hcross : ∀ i j, wolfeMass M (μ i j) (wolfeCrossUnion H i) ≤ ε)
    (hchildren : ∀ i j, wolfeMass M (μ i j) (E i j) ≤ ε)
    (s : Finset (Sigma ι)) (a : Sigma ι → 𝕜) :
    (ell - 6 * ε) * ‖∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2)‖ ≤
      ‖T (∑ q ∈ s, a q • JLMS.clopenIndicator (𝕜 := 𝕜) (A q.1 q.2) (hA q.1 q.2) (hcA q.1 q.2))‖ := by
  have h := wolfe_laminar_sum_lower_bound M T
    (fun q : Sigma ι => A q.1 q.2) (fun q : Sigma ι => E q.1 q.2)
    (fun q : Sigma ι => μ q.1 q.2) (fun q => hA q.1 q.2) (fun q => hcA q.1 q.2)
    (⋃ i, H i) (fun q x hx => mem_iUnion.mpr ⟨q.1, hAH q.1 q.2 hx⟩)
    (wolfe_disjointBlocks_laminar H hH A hAH hlam)
    (wolfe_disjointBlocks_descendants H hH A E hAH hne hdesc)
    (fun q => hμ q.1 q.2) (fun q => hdiag q.1 q.2)
    (fun q => wolfe_disjointBlocks_outside_bound M H hH (μ q.1 q.2) q.1 (A q.1 q.2)
      (houtside q.1 q.2) (hcross q.1 q.2))
    (fun q => (hchildren q.1 q.2).trans (by linarith : ε ≤ 2 * ε)) s a
  convert h using 1 <;> ring

end Posets
