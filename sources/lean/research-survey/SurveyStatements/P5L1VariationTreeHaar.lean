import SurveyStatements.P5L1VariationTerminalVectors
import SurveyStatements.P5Support.LpHaarBinarySums

/-! The finite tree permutations act on each actual Haar vector by a sign
and a permutation of its own level. This follows from the concrete cells. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem prefixIndex_parent (M n : ℕ) (hn : n + 1 ≤ M) (a : Fin (2 ^ M)) :
    lpHaarParentIndex n (prefixIndex M (n + 1) hn a) =
      prefixIndex M n (by omega) a := by
  apply Fin.ext
  change (a.val / 2 ^ (M - (n + 1))) / 2 = a.val / 2 ^ (M - n)
  rw [Nat.div_div_eq_div_mul]
  have he : M - n = (M - (n + 1)) + 1 := by omega
  rw [he, pow_succ]

theorem prefixLift_parent (M n : ℕ) (hn : n + 1 ≤ M)
    (a : Fin (2 ^ (n + 1))) :
    prefixIndex M n (by omega) (prefixLift M (n + 1) hn a) =
      lpHaarParentIndex n a := by
  have h := prefixIndex_parent M n hn (prefixLift M (n + 1) hn a)
  rw [prefixIndex_lift] at h
  exact h.symm

theorem nodeAction_parent {M : ℕ} (σ : DyadicTreePerm M)
    (n : ℕ) (hn : n + 1 ≤ M) (a : Fin (2 ^ (n + 1))) :
    lpHaarParentIndex n (nodeAction σ (n + 1) hn a) =
      nodeAction σ n (by omega) (lpHaarParentIndex n a) := by
  calc
    _ = prefixIndex M n (by omega) (σ.val (prefixLift M (n + 1) hn a)) :=
      prefixIndex_parent M n hn _
    _ = nodeAction σ n (by omega) (prefixIndex M n (by omega)
        (prefixLift M (n + 1) hn a)) := nodeAction_prefix σ n (by omega) _
    _ = _ := by rw [prefixLift_parent]

theorem nodeAction_children {M : ℕ} (σ : DyadicTreePerm M)
    (n : ℕ) (hn : n + 1 ≤ M) (k : Fin (2 ^ n)) :
    ((nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val =
        2 * (nodeAction σ n (by omega) k).val ∧
      (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val =
        2 * (nodeAction σ n (by omega) k).val + 1) ∨
    ((nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val =
        2 * (nodeAction σ n (by omega) k).val + 1 ∧
      (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val =
        2 * (nodeAction σ n (by omega) k).val) := by
  have hpL := nodeAction_parent σ n hn (lpHaarLeftIndex n k)
  have hpR := nodeAction_parent σ n hn (lpHaarRightIndex n k)
  have hparentL : lpHaarParentIndex n (lpHaarLeftIndex n k) = k := by
    apply Fin.ext
    simp [lpHaarParentIndex, lpHaarLeftIndex, lpHaarSignedChildIndex]
  have hparentR : lpHaarParentIndex n (lpHaarRightIndex n k) = k := by
    apply Fin.ext
    change (2 * k.val + 1) / 2 = k.val
    omega
  rw [hparentL] at hpL
  rw [hparentR] at hpR
  have hL := congrArg Fin.val hpL
  have hR := congrArg Fin.val hpR
  change (nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val / 2 =
    (nodeAction σ n (by omega) k).val at hL
  change (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val / 2 =
    (nodeAction σ n (by omega) k).val at hR
  have hne : (nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val ≠
      (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val := by
    intro h
    exact lpHaar_child_indices_ne n k ((nodeAction_injective σ (n + 1) hn) (Fin.ext h))
  omega

theorem terminalPermutation_haar_signed (𝕜 : Type*) [RCLike 𝕜]
    (M n : ℕ) (hn : n + 1 ≤ M) (σ : DyadicTreePerm M) (k : Fin (2 ^ n)) :
    terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
        lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k) ∨
      terminalPermutation 𝕜 M σ.val (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
        -lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n (nodeAction σ n (by omega) k) := by
  have hsplit : lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k =
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarLeftIndex n k) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1) (lpHaarRightIndex n k) := rfl
  rw [hsplit, map_sub, terminalPermutation_cell 𝕜 M (n + 1) hn σ,
    terminalPermutation_cell 𝕜 M (n + 1) hn σ]
  rcases nodeAction_children σ n hn k with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · left
    change lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
        (nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
        (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val = _
    rw [hL, hR]
    rfl
  · right
    change lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
        (nodeAction σ (n + 1) hn (lpHaarLeftIndex n k)).val -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
        (nodeAction σ (n + 1) hn (lpHaarRightIndex n k)).val = _
    rw [hL, hR]
    change _ = -(lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
      (2 * (nodeAction σ n (by omega) k).val) -
      lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ (n + 1)
      (2 * (nodeAction σ n (by omega) k).val + 1))
    abel

end SurveyStatements.P5L1Variation

