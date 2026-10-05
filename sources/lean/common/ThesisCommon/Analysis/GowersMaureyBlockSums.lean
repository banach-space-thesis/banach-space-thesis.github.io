import ThesisCommon.Analysis.GowersMaureyIntervalNorms
import ThesisCommon.Analysis.GowersMaureyNormingForms
import Mathlib.Logic.Equiv.Fin.Basic

/-! Successive finite blocks, their actual support projections, and the
lower logarithmic estimate for sums in the constructed norm. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem before_finset_sums {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (x : ι → C00 𝕜) (y : κ → C00 𝕜)
    (h : ∀ i ∈ s, ∀ j ∈ t, Before (x i) (y j)) :
    Before (∑ i ∈ s, x i) (∑ j ∈ t, y j) := by
  intro a ha b hb
  obtain ⟨i, hi, hai⟩ := Finsupp.mem_support_finset_sum a ha
  obtain ⟨j, hj, hbj⟩ := Finsupp.mem_support_finset_sum b hb
  exact h i hi j hj a hai b hbj

theorem successive_grouped_sums {m n : ℕ} {x : Fin m → Fin n → C00 𝕜}
    (h : ∀ i j, i < j → ∀ a b, Before (x i a) (x j b)) :
    Successive (fun i => ∑ a, x i a) := by
  intro i j hij
  exact before_finset_sums Finset.univ Finset.univ (x i) (x j)
    (fun a _ b _ => h i j hij a b)

theorem finProdFinEquiv_lt_of_first_lt {m n : ℕ} {i j : Fin m}
    (hij : i < j) (a b : Fin n) :
    finProdFinEquiv (i, a) < finProdFinEquiv (j, b) := by
  change a.val + n * i.val < b.val + n * j.val
  have hmul := Nat.mul_le_mul_left n (show i.val + 1 ≤ j.val from hij)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have ha := a.isLt
  omega

theorem successive_support_intervals_disjoint {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (supportInterval (x i)).set (supportInterval (x j)).set := by
  apply Finset.disjoint_left.mpr
  intro s hsi hsj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (lt_irrefl s) (supportInterval_successive (hx i j hlt) s hsi s hsj)
  · exact (lt_irrefl s) (supportInterval_successive (hx j i hgt) s hsj s hsi)

theorem restrict_eq_zero_of_disjoint_supportInterval {a b : C00 𝕜}
    (h : Disjoint (supportInterval a).set (supportInterval b).set) :
    restrict (supportInterval a) b = 0 := by
  ext n
  rw [restrict_apply]
  by_cases hn : n ∈ (supportInterval a).set
  · rw [if_pos hn]
    apply Finsupp.notMem_support_iff.mp
    intro hb
    exact Finset.disjoint_left.mp h hn (support_subset_supportInterval b hb)
  · simp [hn]

theorem successive_restrict_sum {N : ℕ} {x : Fin N → C00 𝕜}
    (hx : Successive x) (i : Fin N) :
    restrict (supportInterval (x i)) (∑ j, x j) = x i := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · exact restrict_supportInterval (x i)
  · intro j _ hji
    exact restrict_eq_zero_of_disjoint_supportInterval
      (successive_support_intervals_disjoint hx (Ne.symm hji))
  · simp

theorem successive_sum_lower_logarithmic (D : ConstructionData 𝕜) {N : ℕ}
    (hN : 2 ≤ N) {x : Fin N → C00 𝕜} (hx : Successive x) :
    (∑ i, implicitNorm D (x i)) ≤ logarithmicWeight N * implicitNorm D (∑ i, x i) := by
  let I := supportIntervalFamily x hx
  have hh := implicitNorm_intervalAverage_le D ⟨N, hN, I.interval, I.successive⟩ (∑ i, x i)
  have hpos : 0 < logarithmicWeight N :=
    lt_of_lt_of_le zero_lt_one (one_le_logarithmicWeight (by omega))
  change (logarithmicWeight N)⁻¹ *
    (∑ i, implicitNorm D (restrict (supportInterval (x i)) (∑ j, x j))) ≤ _ at hh
  simp_rw [successive_restrict_sum hx] at hh
  have hm := mul_le_mul_of_nonneg_left hh hpos.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] using hm

end ThesisCommon.GowersMaurey
