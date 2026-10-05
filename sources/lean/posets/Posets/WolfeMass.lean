import JLMS.AtomicDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.DerivedSet
import Mathlib.Order.Filter.Cofinite

/-! The variation mass used in Wolfe's families, expressed through the actual
atomic representation of the dual of a scattered space. In particular, a fixed
functional cannot occur infinitely often among disjoint positive-mass children.
No operator preservation assertion is assumed here. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (M : JLMS.AtomicDualModel 𝕜 K)

local instance wolfeMassDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeMassDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def wolfeMass (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) : ℝ :=
  ‖JLMS.atomicRestriction M U (WeakDual.toStrongDual μ)‖

theorem wolfeMass_nonneg (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    0 ≤ wolfeMass M μ U := by
  exact norm_nonneg (JLMS.atomicRestriction M U (WeakDual.toStrongDual μ))

theorem wolfeMass_le_norm (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M μ U ≤ ‖WeakDual.toStrongDual μ‖ := by
  calc
    wolfeMass M μ U ≤ ‖JLMS.atomicRestriction M U‖ * ‖WeakDual.toStrongDual μ‖ :=
      (JLMS.atomicRestriction M U).le_opNorm _
    _ ≤ 1 * ‖WeakDual.toStrongDual μ‖ :=
      mul_le_mul_of_nonneg_right (JLMS.atomicRestriction_norm_le M U) (norm_nonneg _)
    _ = _ := one_mul _

theorem wolfeMass_union (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {U V : Set K} (hUV : Disjoint U V) :
    wolfeMass M μ (U ∪ V) = wolfeMass M μ U + wolfeMass M μ V :=
  JLMS.atomicRestriction_norm_union M U V hUV _

@[simp] theorem wolfeMass_empty (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    wolfeMass M μ ∅ = 0 := by
  rw [wolfeMass, JLMS.atomicRestriction_norm]
  have h : JLMS.restrictionL1 (∅ : Set K) (M.representation (WeakDual.toStrongDual μ)) = 0 := by
    ext x
    simp [JLMS.restrictionL1, JLMS.restrictL1]
  rw [h, norm_zero]

theorem wolfeMass_finset_sum_le {ι : Type*} (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (U : ι → Set K) (hU : Pairwise (fun i j => Disjoint (U i) (U j))) (s : Finset ι) :
    ∑ i ∈ s, wolfeMass M μ (U i) ≤ ‖WeakDual.toStrongDual μ‖ := by
  classical
  have hsum : ∀ s : Finset ι, ∑ i ∈ s, wolfeMass M μ (U i) =
      wolfeMass M μ (⋃ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, ih]
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
        symm
        apply wolfeMass_union
        simp only [disjoint_iUnion_right]
        intro j hj
        exact hU (fun hij => hi (hij ▸ hj))
  rw [hsum]
  exact wolfeMass_le_norm M μ _

theorem wolfeMass_positive_indices_finite {ι : Type*}
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ι → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ wolfeMass M μ (U i)}.Finite := by
  classical
  by_contra hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (‖WeakDual.toStrongDual μ‖ / ε)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hlower : (N : ℝ) * ε ≤ ∑ i ∈ s, wolfeMass M μ (U i) := by
    calc
      (N : ℝ) * ε = ∑ _i ∈ s, ε := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum fun i hi => hs hi
  have hupper := wolfeMass_finset_sum_le M μ U hU s
  have := (div_lt_iff₀ hε).mp hN
  linarith

theorem wolfeSequence_finite_fibers
    (μ : ℕ → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ℕ → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) {ε : ℝ} (hε : 0 < ε)
    (hmass : ∀ n, ε ≤ wolfeMass M (μ n) (U n))
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) : {n | μ n = ν}.Finite := by
  apply (wolfeMass_positive_indices_finite M ν U hU hε).subset
  intro n hn
  change μ n = ν at hn
  change ε ≤ wolfeMass M ν (U n)
  rw [← hn]
  exact hmass n

theorem wolfeSequence_mem_derivedSet
    (μ : ℕ → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ℕ → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) {ε : ℝ} (hε : 0 < ε)
    (hmass : ∀ n, ε ≤ wolfeMass M (μ n) (U n))
    {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hconv : Tendsto μ atTop (𝓝 ν))
    {B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))} (hB : ∀ n, μ n ∈ B) :
    ν ∈ derivedSet B := by
  rw [mem_derivedSet, accPt_iff_nhds]
  intro V hV
  have hne : ∀ᶠ n in atTop, μ n ≠ ν := by
    simpa only [Nat.cofinite_eq_atTop, mem_setOf_eq] using
      (wolfeSequence_finite_fibers M μ U hU hε hmass ν).eventually_cofinite_notMem
  have hev : ∀ᶠ n in atTop, μ n ∈ V := hconv hV
  obtain ⟨n, hnV, hne⟩ := (hev.and hne).exists
  exact ⟨μ n, ⟨hnV, hB n⟩, hne⟩

end Posets
