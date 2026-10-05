import Posets.WolfeNorming

/-! The analytic estimates in Wolfe's outside-mass pruning. Disjoint bands
in a nested family cannot all carry large mass. Upper bounds on the mass of
an open set pass to weak-star limits, including complex atomic functionals. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeOutsideMassDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeOutsideMassDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

omit [TopologicalSpace K] in
theorem wolfe_nested_bands_disjoint (G : ℕ → Set K) (hG : Monotone G) :
    Pairwise (fun i j => Disjoint (G (i+1) \ G i) (G (j+1) \ G j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Set.disjoint_left.mpr fun x hx hy => hy.2 (hG (by omega) hx.1)
  · exact Set.disjoint_left.mpr fun x hx hy => hx.2 (hG (by omega) hy.1)

theorem wolfe_exists_small_disjoint_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : ℕ → Set K) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    {N : ℕ} {ε : ℝ} (hN : ‖WeakDual.toStrongDual μ‖ < N * ε) :
    ∃ n < N, wolfeMass M μ (U n) < ε := by
  classical
  by_contra hn
  push_neg at hn
  have hl : (N : ℝ) * ε ≤ ∑ n ∈ Finset.range N, wolfeMass M μ (U n) := by
    calc
      (N : ℝ) * ε = ∑ _n ∈ Finset.range N, ε := by simp
      _ ≤ _ := Finset.sum_le_sum fun n hn' => hn n (Finset.mem_range.mp hn')
  exact hN.not_ge (hl.trans (wolfeMass_finset_sum_le M μ U hU _))

theorem wolfe_exists_small_nested_band
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (G : ℕ → Set K) (hG : Monotone G)
    {N : ℕ} {ε : ℝ} (hN : ‖WeakDual.toStrongDual μ‖ < N * ε) :
    ∃ n < N, wolfeMass M μ (G (n+1) \ G n) < ε :=
  wolfe_exists_small_disjoint_mass M μ _ (wolfe_nested_bands_disjoint G hG) hN

theorem wolfe_exists_small_disjoint_mass_pair
    (M : JLMS.AtomicDualModel 𝕜 K) (μ ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : ℕ → Set K) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    {N : ℕ} {ε : ℝ}
    (hN : ‖WeakDual.toStrongDual μ‖ + ‖WeakDual.toStrongDual ν‖ < N * ε) :
    ∃ n < N, wolfeMass M μ (U n) + wolfeMass M ν (U n) < ε := by
  classical
  by_contra hn
  push_neg at hn
  have hl : (N : ℝ) * ε ≤
      ∑ n ∈ Finset.range N, (wolfeMass M μ (U n) + wolfeMass M ν (U n)) := by
    calc
      (N : ℝ) * ε = ∑ _n ∈ Finset.range N, ε := by simp
      _ ≤ _ := Finset.sum_le_sum fun n hn' => hn n (Finset.mem_range.mp hn')
  rw [Finset.sum_add_distrib] at hl
  exact hN.not_ge (hl.trans (add_le_add
    (wolfeMass_finset_sum_le M μ U hU _) (wolfeMass_finset_sum_le M ν U hU _)))

variable [LocallyCompactSpace K] [T2Space K]

theorem wolfeMass_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    {μ : ι → WeakDual 𝕜 (JLMS.CZero 𝕜 K)}
    {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hμ : Tendsto μ l (𝓝 ν))
    {U : Set K} (hU : IsOpen U) {ε : ℝ}
    (hε : ∀ᶠ i in l, wolfeMass M (μ i) U ≤ ε) : wolfeMass M ν U ≤ ε := by
  have hclosed : IsClosed {ρ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) | wolfeMass M ρ U ≤ ε} := by
    simpa only [Set.compl_setOf, not_lt] using (isOpen_wolfeMass_gt M hK hU ε).isClosed_compl
  exact hclosed.mem_of_tendsto hμ hε

theorem wolfeMass_outside_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    {μ : ι → WeakDual 𝕜 (JLMS.CZero 𝕜 K)}
    {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hμ : Tendsto μ l (𝓝 ν))
    {H G : Set K} (hH : IsOpen H) (hG : IsClosed G) (U : ι → Set K)
    (hUG : ∀ i, U i ⊆ G) {ε : ℝ}
    (hε : ∀ᶠ i in l, wolfeMass M (μ i) (H \ U i) ≤ ε) :
    wolfeMass M ν (H \ G) ≤ ε := by
  apply wolfeMass_le_of_tendsto M hK hμ (hH.sdiff hG)
  filter_upwards [hε] with i hi
  exact (wolfeMass_mono M (μ i) (diff_subset_diff_right (hUG i))).trans hi

end Posets
