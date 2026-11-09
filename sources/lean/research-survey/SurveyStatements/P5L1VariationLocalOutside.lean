import SurveyStatements.P5L1VariationLocalTree

/-! The genuine local symmetry group fixes every dyadic cell and Haar
vector outside its chosen root, including finer dyadic levels. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem localNodeAction_outside_fixed (M n r : ℕ) (hn : n ≤ M) (hr : r ≤ n)
    (root : Fin (2 ^ r)) (σ : LocalDyadicTreePerm M r (hr.trans hn) root)
    (k : Fin (2 ^ n)) (hk : prefixIndex n r hr k ≠ root) :
    nodeAction σ.val n hn k = k := by
  have hz : prefixIndex M r (hr.trans hn) (prefixLift M n hn k) ≠ root := by
    rwa [prefixLift_prefix]
  change prefixIndex M n hn (σ.val.val (prefixLift M n hn k)) = k
  rw [σ.property _ hz]
  exact prefixIndex_lift M n hn k

theorem prefixIndex_child (n r : ℕ) (hr : r ≤ n) (a : Fin (2 ^ (n + 1))) :
    prefixIndex (n + 1) r (by omega) a =
      prefixIndex n r hr (lpHaarParentIndex n a) := by
  apply Fin.ext
  change a.val / 2 ^ ((n + 1) - r) = (a.val / 2) / 2 ^ (n - r)
  rw [Nat.div_div_eq_div_mul]
  have he : (n + 1) - r = (n - r) + 1 := by omega
  congr 1
  calc
    2 ^ ((n + 1) - r) = 2 ^ ((n - r) + 1) := congrArg (fun l : ℕ => 2 ^ l) he
    _ = 2 ^ (n - r) * 2 := pow_succ 2 (n - r)
    _ = 2 * 2 ^ (n - r) := Nat.mul_comm _ _

theorem terminalPermutation_haar_of_fixed_children (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (σ : DyadicTreePerm M) (k : Fin (2 ^ n))
    (hL : nodeAction σ (n + 1) hn (lpHaarLeftIndex n k) = lpHaarLeftIndex n k)
    (hR : nodeAction σ (n + 1) hn (lpHaarRightIndex n k) = lpHaarRightIndex n k) :
    terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  change terminalPermutation 𝕜 M σ.val
    (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarLeftIndex n k) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarRightIndex n k)) = _
  rw [map_sub, terminalPermutation_cell 𝕜 M (n + 1) hn,
    terminalPermutation_cell 𝕜 M (n + 1) hn, hL, hR]
  rfl

theorem localTerminalPermutation_haar_outside (𝕜 : Type*) [RCLike 𝕜]
    (M n r : ℕ) (hn : n + 1 ≤ M) (hr : r ≤ n) (root : Fin (2 ^ r))
    (σ : LocalDyadicTreePerm M r (by omega) root)
    (k : Fin (2 ^ n)) (hk : prefixIndex n r hr k ≠ root) :
    terminalPermutation 𝕜 M σ.val.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  apply terminalPermutation_haar_of_fixed_children 𝕜 M n hn σ.val k
  · apply localNodeAction_outside_fixed M (n + 1) r hn (by omega) root σ
    rw [prefixIndex_child]
    have hp : lpHaarParentIndex n (lpHaarLeftIndex n k) = k := by
      apply Fin.ext
      simp [lpHaarParentIndex, lpHaarLeftIndex, lpHaarSignedChildIndex]
    rwa [hp]
  · apply localNodeAction_outside_fixed M (n + 1) r hn (by omega) root σ
    rw [prefixIndex_child]
    have hp : lpHaarParentIndex n (lpHaarRightIndex n k) = k := by
      apply Fin.ext
      change (2 * k.val + 1) / 2 = k.val
      omega
    rwa [hp]

end SurveyStatements.P5L1Variation
