import JLMS.PrintedAtomicNotation
import JLMS.ScatteredCZeroFactorization

noncomputable section
open Set
open scoped BigOperators

namespace JLMS

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]

local instance : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

omit [LocallyCompactSpace K] [T2Space K] in
private theorem atomicRestriction_union_eq (M : AtomicDualModel 𝕜 K)
    (C D : Set K) (h : Disjoint C D) :
    atomicRestriction M (C ∪ D) = atomicRestriction M C + atomicRestriction M D := by
  apply ContinuousLinearMap.ext
  intro f
  apply M.representation.injective
  simp only [ContinuousLinearMap.add_apply, map_add, atomicRestriction_coordinates]
  rw [restrictionL1_union C D h, ContinuousLinearMap.add_apply]

private theorem finite_atomicRestriction (M : AtomicDualModel 𝕜 K) {I : Type*}
    (s : Finset I) (C : I → Set K)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j)) :
    atomicRestriction M (⋃ i ∈ s, C i) = ∑ i ∈ s, atomicRestriction M (C i) ∧
      ∀ f, ‖atomicRestriction M (⋃ i ∈ s, C i) f‖ =
        ∑ i ∈ s, ‖atomicRestriction M (C i) f‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hzero : atomicRestriction M (∅ : Set K) = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      apply M.representation.injective
      simp only [atomicRestriction_coordinates, ContinuousLinearMap.zero_apply,
        LinearIsometryEquiv.map_zero]
      apply lp.ext
      funext k
      simp [restrictionL1_apply, restrictL1_apply]
    simp [hzero, norm_zero]
  | @insert i s hi ih =>
    have hds : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (C j) (C k) :=
      fun j hj k hk h => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) h
    obtain ⟨heq, hn⟩ := ih hds
    have hdisj : Disjoint (C i) (⋃ j ∈ s, C j) := by
      rw [Set.disjoint_left]
      intro x hxi hx
      simp only [mem_iUnion] at hx
      obtain ⟨j, hj, hxj⟩ := hx
      exact Set.disjoint_left.mp
        (hd i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))) hxi hxj
    rw [Finset.set_biUnion_insert]
    simp only [Finset.sum_insert hi]
    exact ⟨(atomicRestriction_union_eq M _ _ hdisj).trans
        (congrArg (fun L => atomicRestriction M (C i) + L) heq),
      fun f => (atomicRestriction_norm_union M _ _ hdisj f).trans
        (congrArg (_ + ·) (hn f))⟩

/-- Both identities of Lemma 4.11, including the norm-one clause for a nonempty union. -/
theorem lemma_4_11_finite_family (hK : IsScattered K) {I : Type*}
    (s : Finset I) (C : I → Set K)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j))
    (hne : (⋃ i ∈ s, C i).Nonempty) :
    let R := printedAtomicRestriction (𝕜 := 𝕜) hK
    R (⋃ i ∈ s, C i) = ∑ i ∈ s, R (C i) ∧
      ‖∑ i ∈ s, R (C i)‖ = 1 ∧ ‖R (⋃ i ∈ s, C i)‖ = 1 ∧
      ∀ f, ‖(∑ i ∈ s, R (C i)) f‖ = ∑ i ∈ s, ‖R (C i) f‖ := by
  classical
  let M := printedAtomicDualModel (𝕜 := 𝕜) hK
  let D := ⋃ i ∈ s, C i
  obtain ⟨heq, hsum⟩ := finite_atomicRestriction M s C hd
  obtain ⟨k, hk⟩ := hne
  let e : ellOneOn 𝕜 K := lp.single 1 k (1 : 𝕜)
  have he : ‖e‖ = 1 := by simp [e, lp.norm_single]
  have hcut : restrictionL1 D e = e := by
    apply lp.ext
    funext x
    by_cases hx : x = k
    · subst x
      simp [restrictionL1_apply, restrictL1_apply, show k ∈ D from hk, e]
    · simp [restrictionL1_apply, restrictL1_apply, e, lp.single_apply, hx]
  have hnorm : ‖atomicRestriction M D‖ = 1 := by
    apply le_antisymm (atomicRestriction_norm_le M D)
    have h := (atomicRestriction M D).le_opNorm (M.representation.symm e)
    rwa [atomicRestriction_norm, LinearIsometryEquiv.apply_symm_apply, hcut,
      M.representation.symm.norm_map, he, mul_one] at h
  refine ⟨heq, ?_, hnorm, fun f => ?_⟩
  · rw [← heq]
    exact hnorm
  · rw [← heq]
    exact hsum f

/-- Lemma 8.2 with infinite K. Index zero in Lean is the first block. -/
theorem lemma_8_2_infinite [Infinite K] (hK : IsScattered K) :
    ∃ P : ℕ → CZero 𝕜 K →L[𝕜] CZero 𝕜 K, (∀ n, ¬ IsCompactOperator (P n)) ∧
      SimultaneousFactorizations P (fun n => (2 : ℝ) ^ (2 * (n + 1) + 1)) := by
  obtain ⟨A, B, hBA, _, _⟩ := exists_cZero_retract (𝕜 := 𝕜) hK
  let R := orthogonalRetracts_of_cZero_retract A B hBA
  have hZ : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 (cZero 𝕜)) := by
    intro h
    exact cZero_not_finiteDimensional 𝕜 (finiteDimensional_of_compact_identity h)
  let ρ : ℕ → ℝ := fun n => (1 / 2) ^ (n + 1)
  have hρ (n : ℕ) : 0 < ρ n := pow_pos (by norm_num) _
  have hs : Summable ρ :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have he (n : ℕ) : 2 / (ρ n) ^ 2 = (2 : ℝ) ^ (2 * (n + 1) + 1) := by
    change 2 / ((1 / 2 : ℝ) ^ (n + 1)) ^ 2 = _
    rw [one_div, ← pow_mul, inv_pow, div_inv_eq_mul, Nat.mul_comm (n + 1) 2, pow_succ']
  refine ⟨R.block, R.block_noncompact hZ, ?_⟩
  simpa only [he] using simultaneousFactorizations_of_factor_two R
    (theorem_1_6_of_scatteredCZero hK hK (cZero_admissible hK)) ρ hρ hs

end JLMS
