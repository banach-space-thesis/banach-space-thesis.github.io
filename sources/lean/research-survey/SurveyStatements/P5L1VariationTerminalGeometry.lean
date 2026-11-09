import SurveyStatements.P5L1VariationTreeFlips

/-! Connecting ancestor prefixes of terminal indices with the actual dyadic
interval cells. These are concrete set identities, independent of operators. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem terminalCell_subset_parent (n : ℕ) (a : Fin (2 ^ (n + 1))) :
    lpHaarCell (n + 1) a ⊆ lpHaarCell n (lpHaarParentIndex n a) := by
  intro x hx
  rw [← lpHaarCell_children]
  have ha : a.val = 2 * (a.val / 2) ∨ a.val = 2 * (a.val / 2) + 1 := by omega
  rcases ha with h | h
  · apply Or.inl
    simpa only [lpHaarParentIndex, ← h] using hx
  · apply Or.inr
    simpa only [lpHaarParentIndex, ← h] using hx

theorem terminalCell_subset_prefix_add (n d : ℕ) (a : Fin (2 ^ (n + d))) :
    lpHaarCell (n + d) a ⊆
      lpHaarCell n (prefixIndex (n + d) n (by omega) a) := by
  induction d with
  | zero =>
      change lpHaarCell n a ⊆ lpHaarCell n (prefixIndex n n (by omega) a)
      have heq : prefixIndex n n (by omega) a = a := by
        apply Fin.ext
        simp [prefixIndex]
      rw [heq]
  | succ d ih =>
      let p : Fin (2 ^ (n + d)) := lpHaarParentIndex (n + d) a
      have hp : prefixIndex (n + d) n (by omega) p =
          prefixIndex (n + (d + 1)) n (by omega) a := by
        apply Fin.ext
        change (a.val / 2) / 2 ^ ((n + d) - n) =
          a.val / 2 ^ ((n + (d + 1)) - n)
        simp only [Nat.add_sub_cancel_left]
        rw [Nat.div_div_eq_div_mul, pow_succ]
        rw [Nat.mul_comm]
      have hs := (terminalCell_subset_parent (n + d) a).trans (ih p)
      simpa only [hp] using hs

theorem terminalCell_subset_prefix (M n : ℕ) (hn : n ≤ M) (a : Fin (2 ^ M)) :
    lpHaarCell M a ⊆ lpHaarCell n (prefixIndex M n hn a) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact terminalCell_subset_prefix_add n d a

def terminalFiber (M n : ℕ) (hn : n ≤ M) (k : Fin (2 ^ n)) : Finset (Fin (2 ^ M)) :=
  Finset.univ.filter (fun a => prefixIndex M n hn a = k)

theorem terminalFiber_cells (M n : ℕ) (hn : n ≤ M) (k : Fin (2 ^ n)) :
    (⋃ a ∈ terminalFiber M n hn k, lpHaarCell M a) = lpHaarCell n k := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp hx
    have heq : prefixIndex M n hn a = k := by simpa [terminalFiber] using ha
    simpa only [heq] using terminalCell_subset_prefix M n hn a hx
  · intro x hx
    have hxinterval : x ∈ Ioc (0 : ℝ) 1 := by
      have hnonneg : 0 ≤ (k.val : ℝ) * intervalLpDyadicRadius n :=
        mul_nonneg (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le
      exact ⟨hnonneg.trans_lt hx.1, (lpHaarCell_subset n k k.isLt hx).2⟩
    have hcover : x ∈ ⋃ a : Fin (2 ^ M), lpHaarCell M a := by
      rw [lpHaarLevelCells_union]
      exact hxinterval
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hcover
    have heq : prefixIndex M n hn a = k := by
      by_contra hne
      exact Set.disjoint_left.mp (lpHaarLevelCells_disjoint n hne)
        (terminalCell_subset_prefix M n hn a ha) hx
    exact Set.mem_iUnion₂.mpr ⟨a, by simp [terminalFiber, heq], ha⟩

end SurveyStatements.P5L1Variation

