import ThesisCommon.Analysis.InfiniteFusion
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Stabilization of real set functions modulo finite sets. This is the
countable pseudointersection argument behind Drewnowski--Roberts Lemma 2.2.
The bounded-below version suffices for the nonnegative local suprema used
in their operator compression theorem. -/
noncomputable section
namespace ThesisCommon
open Set

/-- A decreasing sequence of infinite sets has an infinite pseudointersection,
chosen inside the first set. -/
theorem infinite_nested_pseudointersection (A : ℕ → Set ℕ)
    (hA : ∀ n, (A n).Infinite) (hanti : Antitone A) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A 0 ∧ ∀ n, (B \ A n).Finite := by
  classical
  choose next hmem hgt using (fun n k => (hA n).exists_gt k)
  let b : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n k => next (n + 1) k) n
  have hb : ∀ n, b n ∈ A n := by
    intro n
    cases n with
    | zero => exact hmem 0 0
    | succ n => exact hmem (n + 1) (b n)
  have hstrict : StrictMono b := strictMono_nat_of_lt_succ (fun n => hgt (n + 1) (b n))
  refine ⟨range b, infinite_range_of_injective hstrict.injective, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hanti (Nat.zero_le n) (hb n)
  · intro n
    apply ((finite_Iio n).image b).subset
    rintro x ⟨⟨m, rfl⟩, hm⟩
    refine ⟨m, ?_, rfl⟩
    by_contra h
    exact hm (hanti (Nat.le_of_not_gt h) (hb m))

/-- Select a set on which the value differs from that of any infinite
subset by less than the prescribed positive error. -/
theorem exists_infinite_subset_near_infimum (w : Set ℕ → ℝ)
    {A : Set ℕ} (hA : A.Infinite)
    (hbound : BddBelow {r | ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ w B = r})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      ∀ C : Set ℕ, C.Infinite → C ⊆ B → w B < w C + ε := by
  let V : Set ℝ := {r | ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ w B = r}
  have hV : V.Nonempty := ⟨w A, A, hA, Subset.rfl, rfl⟩
  obtain ⟨r, ⟨B, hB, hBA, hr⟩, hsmall⟩ :=
    exists_lt_of_csInf_lt hV (lt_add_of_pos_right (sInf V) hε)
  refine ⟨B, hB, hBA, fun C hC hCB => ?_⟩
  have hlow : sInf V ≤ w C := csInf_le hbound ⟨C, hC, hCB.trans hBA, rfl⟩
  rw [← hr] at hsmall
  exact hsmall.trans_le (add_le_add_right hlow ε)

/-- A set function that is monotone modulo finite sets and bounded below
on the infinite subsets of A is constant on all infinite subsets of some B.
No continuum hypothesis or operator-theoretic assumption is used. -/
theorem infinite_subset_stabilization (w : Set ℕ → ℝ)
    {A : Set ℕ} (hA : A.Infinite)
    (hmono : ∀ E F : Set ℕ, E.Infinite → F.Infinite →
      E ⊆ A → F ⊆ A → (E \ F).Finite → w E ≤ w F)
    (hbound : BddBelow {r | ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ w B = r}) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      ∀ C : Set ℕ, C.Infinite → C ⊆ B → w C = w B := by
  classical
  let S := {E : Set ℕ // E.Infinite ∧ E ⊆ A}
  have hstep (n : ℕ) (E : S) : ∃ F : Set ℕ, F.Infinite ∧ F ⊆ E.val ∧
      ∀ C : Set ℕ, C.Infinite → C ⊆ F → w F < w C + 1 / (n + 1 : ℝ) := by
    apply exists_infinite_subset_near_infimum w E.property.1
    · apply hbound.mono
      rintro r ⟨B, hB, hBE, rfl⟩
      exact ⟨B, hB, hBE.trans E.property.2, rfl⟩
    · positivity
  choose F hF hFE hsmall using hstep
  let states : ℕ → S := fun n => Nat.rec (⟨A, hA, Subset.rfl⟩ : S)
    (fun n E => ⟨F n E, hF n E, (hFE n E).trans E.property.2⟩) n
  let D : ℕ → Set ℕ := fun n => (states n).val
  have hD : ∀ n, (D n).Infinite := fun n => (states n).property.1
  have hDA : ∀ n, D n ⊆ A := fun n => (states n).property.2
  have hnest : ∀ n, D (n + 1) ⊆ D n := fun n => hFE n (states n)
  obtain ⟨B, hB, hBA, hfin⟩ :=
    infinite_nested_pseudointersection D hD (antitone_nat_of_succ_le hnest)
  change B ⊆ A at hBA
  refine ⟨B, hB, hBA, fun C hC hCB => le_antisymm ?_ ?_⟩
  · exact hmono C B hC hB (hCB.trans hBA) hBA
      (by simpa only [diff_eq_empty.mpr hCB] using (finite_empty : (∅ : Set ℕ).Finite))
  · by_contra h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (lt_of_not_ge h))
    let E := C ∩ D (n + 1)
    have hCEfin : (C \ D (n + 1)).Finite := (hfin (n + 1)).subset (by
      intro i hi
      exact ⟨hCB hi.1, hi.2⟩)
    have hE : E.Infinite := by
      have heq : C \ (C \ D (n + 1)) = E := by ext i; simp [E]
      rw [← heq]
      exact hC.diff hCEfin
    have hEB : E ⊆ B := inter_subset_left.trans hCB
    have hEq : w E = w C := le_antisymm
      (hmono E C hE hC (hEB.trans hBA) (hCB.trans hBA)
        (by rw [diff_eq_empty.mpr inter_subset_left]; exact finite_empty))
      (hmono C E hC hE (hCB.trans hBA) (hEB.trans hBA) (by
        convert hCEfin using 1
        ext i
        simp [E]))
    have hBD : w B ≤ w (D (n + 1)) :=
      hmono B (D (n + 1)) hB (hD (n + 1)) hBA (hDA (n + 1)) (hfin (n + 1))
    have hs := hsmall n (states n) E hE (show E ⊆ F n (states n) from inter_subset_right)
    change w (D (n + 1)) < w E + 1 / (n + 1 : ℝ) at hs
    rw [hEq] at hs
    linarith

/-- The ordinary inclusion/finite-removal formulation of stabilization. -/
theorem infinite_subset_stabilization_of_finite_removal (w : Set ℕ → ℝ)
    {A : Set ℕ} (hA : A.Infinite)
    (hmono : ∀ E F : Set ℕ, E.Infinite → F.Infinite →
      E ⊆ A → F ⊆ A → E ⊆ F → w E ≤ w F)
    (hremove : ∀ E : Set ℕ, E.Infinite → E ⊆ A →
      ∀ K : Set ℕ, K.Finite → w (E \ K) = w E)
    (hbound : BddBelow {r | ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ w B = r}) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
      ∀ C : Set ℕ, C.Infinite → C ⊆ B → w C = w B := by
  apply infinite_subset_stabilization w hA (hbound := hbound)
  intro E F hE hF hEA hFA hfin
  rw [← hremove E hE hEA (E \ F) hfin]
  apply hmono (E \ (E \ F)) F (hE.diff hfin) hF
    (diff_subset.trans hEA) hFA
  intro i hi
  by_contra h
  exact hi.2 ⟨hi.1, h⟩

end ThesisCommon
