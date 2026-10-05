import JLMS.DisjointSynthesis
import JLMS.PointNeighborhoodSelection

/-!
# Pairing disjoint compact clopen indicators

On each consecutive pair of neighborhoods, use values +1 and -1. Pairing
keeps the norm at most one and preserves disjointness. Half-difference
evaluations then recover the c₀ coefficient exactly.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable (η : ℕ → CZero 𝕜 K) (hunit : ∀ n, ‖η n‖ ≤ 1)
    (hdisjoint : Pairwise fun i j => Disjoint (Function.support (η i)) (Function.support (η j)))

def pairedDisjointFunction (n : ℕ) : CZero 𝕜 K := η (2 * n) - η (2 * n + 1)

include hunit hdisjoint in
theorem pairedDisjointFunction_norm_le (n : ℕ) : ‖pairedDisjointFunction η n‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro x
  change ‖η (2 * n) x - η (2 * n + 1) x‖ ≤ 1
  by_cases he : η (2 * n) x = 0
  · simpa [he] using (norm_CZero_apply_le (η (2 * n + 1)) x).trans (hunit _)
  · have ho : η (2 * n + 1) x = 0 := by
      by_contra ho
      exact Set.disjoint_left.mp (hdisjoint (by omega : 2 * n ≠ 2 * n + 1)) he ho
    simpa [ho] using (norm_CZero_apply_le (η (2 * n)) x).trans (hunit _)

include hdisjoint in
theorem pairedDisjointFunction_disjoint : Pairwise fun i j =>
    Disjoint (Function.support (pairedDisjointFunction η i))
      (Function.support (pairedDisjointFunction η j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : η (2 * i) x ≠ 0 ∨ η (2 * i + 1) x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxi (by change η (2 * i) x - η (2 * i + 1) x = 0; rw [h.1, h.2, sub_self])
  have hj : η (2 * j) x ≠ 0 ∨ η (2 * j + 1) x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxj (by change η (2 * j) x - η (2 * j + 1) x = 0; rw [h.1, h.2, sub_self])
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact Set.disjoint_left.mp (hdisjoint (by omega : 2 * i ≠ 2 * j)) hi hj
  · exact Set.disjoint_left.mp (hdisjoint (by omega : 2 * i ≠ 2 * j + 1)) hi hj
  · exact Set.disjoint_left.mp (hdisjoint (by omega : 2 * i + 1 ≠ 2 * j)) hi hj
  · exact Set.disjoint_left.mp (hdisjoint (by omega : 2 * i + 1 ≠ 2 * j + 1)) hi hj

variable (p : ℕ → K) (U : ℕ → Set K) (hU : ∀ n, IsClopen (U n))
    (hcU : ∀ n, IsCompact (U n)) (hpU : ∀ n, p n ∈ U n)
    (hUd : Pairwise fun i j => Disjoint (U i) (U j))

include hpU hUd in
/-- Indicators interpolate the coordinate delta on the selected points. -/
theorem pointNeighborhood_indicator_apply (i j : ℕ) :
    clopenIndicator (𝕜 := 𝕜) (U i) (hU i) (hcU i) (p j) = if j = i then 1 else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp [hpU]
  · have hout : p j ∉ U i := fun h => Set.disjoint_left.mp (hUd hji) (hpU j) h
    simp [hji, hout]

end JLMS
