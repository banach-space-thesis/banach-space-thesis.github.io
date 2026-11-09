import SurveyStatements.P1TwoFrontInfinite
import Aesop

/-! The intersection of the two limit sets consists precisely of matched
points in both finite witnesses. A point appearing in only one front can
never be added to the other front at a later stage. -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem matchingFrontStep_common (a b : MatchingColor) (A B : Finset ℕ)
    (x y z : ℕ) (hxA : x ∉ A) (hxB : x ∉ B) (hyA : y ∉ A)
    (hyB : y ∉ B) (hxy : x ≠ y)
    (hzA : z ∈ (matchingFrontStep a b A B x y).1)
    (hzB : z ∈ (matchingFrontStep a b A B x y).2) :
    (z ∈ A ∧ z ∈ B) ∨ (a = .inside ∧ b = .inside ∧ z = x) := by
  cases a <;> cases b <;>
    simp only [matchingFrontStep, Finset.mem_insert] at hzA hzB <;> aesop

section Run

variable (F : Set ℕ → Finset ℕ) (hF : IsLocallyConstantFiniteAssignment F)
  (N : Set ℕ) (hN : N.Infinite)

local notation "q" => twoFrontMatchRun F hF N hN
local notation "L" => finiteFrontLimit (fun n => (q n).frontA)
local notation "M" => finiteFrontLimit (fun n => (q n).frontB)

theorem twoFrontMatchRun_Y_not_frontA (n : ℕ) : twoFrontMatchY (q n) ∉ (q n).frontA := by
  intro hy
  exact (lt_irrefl _) ((q n).separated _ (Finset.mem_union_left _ hy)
    _ (twoFrontMatchY_spec (q n)).1)

theorem twoFrontMatchRun_front_common (n z : ℕ)
    (hzA : z ∈ (q n).frontA) (hzB : z ∈ (q n).frontB) :
    z ∈ F L ∧ z ∈ F M := by
  induction n with
  | zero =>
    change z ∈ (∅ : Finset ℕ) at hzA
    exact False.elim (Finset.notMem_empty _ hzA)
  | succ n ih =>
    have heq := twoFrontMatchNext_fronts F hF (q n)
    have hA := congrArg Prod.fst heq
    dsimp only at hA
    have hB := congrArg Prod.snd heq
    dsimp only at hB
    change z ∈ (twoFrontMatchNext F hF (q n)).frontA at hzA
    change z ∈ (twoFrontMatchNext F hF (q n)).frontB at hzB
    rw [hA] at hzA
    rw [hB] at hzB
    have hm := matchingFrontStep_common (q n).colorA (q n).colorB
      (q n).frontA (q n).frontB (twoFrontMatchX (q n)) (twoFrontMatchY (q n)) z
      (twoFrontMatchRun_X_not_frontA F hF N hN n)
      (twoFrontMatchRun_X_not_frontB F hF N hN n)
      (twoFrontMatchRun_Y_not_frontA F hF N hN n)
      (twoFrontMatchRun_Y_not_frontB F hF N hN n)
      (ne_of_lt (twoFrontMatchY_spec (q n)).2) hzA hzB
    rcases hm with hold | ⟨hca, hcb, rfl⟩
    · exact ih hold.1 hold.2
    · have hxA : twoFrontMatchX (q n) ∈ (q (n + 1)).frontA := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontA
        rw [hA]
        simp [hca, hcb, matchingFrontStep]
      have hxB : twoFrontMatchX (q n) ∈ (q (n + 1)).frontB := by
        change _ ∈ (twoFrontMatchNext F hF (q n)).frontB
        rw [hB]
        simp [hca, hcb, matchingFrontStep]
      have hpA := twoFrontMatchRun_predictA_at_X F hF N hN
        (twoFrontMatchRun_limitA_infinite F hF N hN) n hxA
      have hpB := twoFrontMatchRun_predictB_at_X F hF N hN
        (twoFrontMatchRun_limitB_infinite F hF N hN) n hxB
      rw [hca] at hpA
      rw [hcb] at hpB
      exact ⟨(finiteSetMatchingColor_inside F L _).mp hpA,
        (finiteSetMatchingColor_inside F M _).mp hpB⟩

theorem twoFrontMatchRun_intersection_subset_witnesses :
    L ∩ M ⊆ (F L : Set ℕ) ∩ (F M : Set ℕ) := by
  rintro z ⟨hzL, hzM⟩
  obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzL
  have hzB : z ∈ (q n).frontB := by
    by_contra hzB
    have hztail := twoFrontMatchRun_limitB_tail F hF N hN n ⟨hzM, hzB⟩
    exact (lt_irrefl z) ((q n).separated z (Finset.mem_union_left _ hzn) z hztail)
  exact twoFrontMatchRun_front_common F hF N hN n z hzn hzB

theorem twoFrontMatchRun_intersection_witnesses
    (hsupp : ∀ A : Set ℕ, A.Infinite → (F A : Set ℕ) ⊆ A) :
    L ∩ M = (F L : Set ℕ) ∩ (F M : Set ℕ) := by
  apply Set.Subset.antisymm (twoFrontMatchRun_intersection_subset_witnesses F hF N hN)
  exact Set.inter_subset_inter
    (hsupp L (twoFrontMatchRun_limitA_infinite F hF N hN))
    (hsupp M (twoFrontMatchRun_limitB_infinite F hF N hN))

end Run

end SurveyStatements.P1
