import ThesisCommon.Analysis.LpHaarDenseSpan
import ThesisCommon.Analysis.LpHaarMeanDifference

/-! Nested dyadic averages and the full cross-level Haar identities. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem lpHaarDyadicMean_fix_parent_cell (n k : ℕ) (hk : k < 2 ^ n) :
    lpHaarDyadicMean 𝕜 p hp (n + 1) (lpHaarCellVector 𝕜 p n k) = lpHaarCellVector 𝕜 p n k := by
  have hk₁ : 2 * k < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hk₂ : 2 * k + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  rw [lpHaarCellVector_split 𝕜 p n k, map_add]
  have hl := lpHaarDyadicMean_fix_cell 𝕜 p hp (n + 1) (2 * k) hk₁ (1 : 𝕜)
  have hr := lpHaarDyadicMean_fix_cell 𝕜 p hp (n + 1) (2 * k + 1) hk₂ (1 : 𝕜)
  exact congrArg₂ (· + ·) hl hr

theorem lpHaarDyadicMean_adjacent_forward (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp (n + 1) (lpHaarDyadicMean 𝕜 p hp n f) =
      lpHaarDyadicMean 𝕜 p hp n f := by
  have hfix : ∀ g ∈ Submodule.span 𝕜 (Set.range (fun k : Fin (2 ^ n) => lpHaarCellVector 𝕜 p n k)),
      lpHaarDyadicMean 𝕜 p hp (n + 1) g = g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨k, rfl⟩ := hg
        exact lpHaarDyadicMean_fix_parent_cell 𝕜 p hp n k k.isLt
    | zero => exact map_zero _
    | add g h _ _ hg hh => rw [map_add, hg, hh]
    | smul c g _ hg => rw [map_smul, hg]
  exact hfix _ (lpHaarDyadicMean_mem_stepSpan 𝕜 p hp n f)

theorem lpHaarDyadicMean_kill_level (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarLevelProjection 𝕜 p n f) = 0 := by
  rw [lpHaarLevelProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_smul, lpHaarDyadicMean_kill_haar 𝕜 p hp n k k.isLt, smul_zero]

theorem lpHaarDyadicMean_idempotent_apply (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp n f) = lpHaarDyadicMean 𝕜 p hp n f :=
  congrArg (fun T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p => T f)
    (lpHaarDyadicMean_idempotent 𝕜 p hp n)

theorem lpHaarDyadicMean_adjacent_reverse (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp (n + 1) f) =
      lpHaarDyadicMean 𝕜 p hp n f := by
  have heq : lpHaarDyadicMean 𝕜 p hp (n + 1) f =
      lpHaarDyadicMean 𝕜 p hp n f + lpHaarLevelProjection 𝕜 p n f := by
    rw [← lpHaarDyadicMean_difference 𝕜 p hp n f]
    abel
  rw [heq, map_add, lpHaarDyadicMean_idempotent_apply 𝕜 p hp,
    lpHaarDyadicMean_kill_level 𝕜 p hp, add_zero]

theorem lpHaarDyadicMean_nested_forward (m n : ℕ) (hmn : m ≤ n) :
    ∀ f : IntervalLp 𝕜 p, lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp m f) =
      lpHaarDyadicMean 𝕜 p hp m f := by
  induction n, hmn using Nat.le_induction with
  | base => exact lpHaarDyadicMean_idempotent_apply 𝕜 p hp m
  | succ n hmn ih =>
      intro f
      calc
        _ = lpHaarDyadicMean 𝕜 p hp (n + 1)
            (lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp m f)) := congrArg _ (ih f).symm
        _ = _ := (lpHaarDyadicMean_adjacent_forward 𝕜 p hp n _).trans (ih f)

theorem lpHaarDyadicMean_nested_reverse (m n : ℕ) (hmn : m ≤ n) :
    ∀ f : IntervalLp 𝕜 p, lpHaarDyadicMean 𝕜 p hp m (lpHaarDyadicMean 𝕜 p hp n f) =
      lpHaarDyadicMean 𝕜 p hp m f := by
  induction n, hmn using Nat.le_induction with
  | base => exact lpHaarDyadicMean_idempotent_apply 𝕜 p hp m
  | succ n hmn ih =>
      intro f
      calc
        _ = lpHaarDyadicMean 𝕜 p hp m
            (lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadicMean 𝕜 p hp (n + 1) f)) :=
          (ih (lpHaarDyadicMean 𝕜 p hp (n + 1) f)).symm
        _ = _ := by rw [lpHaarDyadicMean_adjacent_reverse 𝕜 p hp n f, ih f]

theorem lpHaarDyadicMean_fix_earlier_haar (m n k : ℕ) (hk : k < 2 ^ m) (hmn : m < n) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadic 𝕜 p m k) = lpHaarDyadic 𝕜 p m k := by
  calc
    _ = lpHaarDyadicMean 𝕜 p hp n
        (lpHaarDyadicMean 𝕜 p hp (m + 1) (lpHaarDyadic 𝕜 p m k)) :=
      congrArg _ (lpHaarDyadicMean_fix_haar 𝕜 p hp m k hk).symm
    _ = _ := (lpHaarDyadicMean_nested_forward 𝕜 p hp (m + 1) n (by omega) _).trans
      (lpHaarDyadicMean_fix_haar 𝕜 p hp m k hk)

theorem lpHaarDyadicMean_kill_later_haar (m n k : ℕ) (hk : k < 2 ^ m) (hnm : n ≤ m) :
    lpHaarDyadicMean 𝕜 p hp n (lpHaarDyadic 𝕜 p m k) = 0 := by
  rw [← lpHaarDyadicMean_nested_reverse 𝕜 p hp n m hnm (lpHaarDyadic 𝕜 p m k),
    lpHaarDyadicMean_kill_haar 𝕜 p hp m k hk, map_zero]

include hp in
theorem lpHaarLevelProjection_haar_other (m n k : ℕ) (hk : k < 2 ^ m) (hnm : n ≠ m) :
    lpHaarLevelProjection 𝕜 p n (lpHaarDyadic 𝕜 p m k) = 0 := by
  rw [← lpHaarDyadicMean_difference 𝕜 p hp n]
  rcases lt_or_gt_of_ne hnm with h | h
  · rw [lpHaarDyadicMean_kill_later_haar 𝕜 p hp m (n + 1) k hk (by omega),
      lpHaarDyadicMean_kill_later_haar 𝕜 p hp m n k hk (by omega), sub_self]
  · rw [lpHaarDyadicMean_fix_earlier_haar 𝕜 p hp m (n + 1) k hk (by omega),
      lpHaarDyadicMean_fix_earlier_haar 𝕜 p hp m n k hk (by omega), sub_self]

include hp in
theorem lpHaarDyadicCoefficient_other_level (m n : ℕ) (k : Fin (2 ^ m)) (j : Fin (2 ^ n))
    (hnm : n ≠ m) : lpHaarDyadicCoefficient 𝕜 p n j (lpHaarDyadic 𝕜 p m k) = 0 := by
  rw [← lpHaarLevelProjection_coefficient 𝕜 p n j,
    lpHaarLevelProjection_haar_other 𝕜 p hp m n k k.isLt hnm, map_zero]

end ThesisCommon
