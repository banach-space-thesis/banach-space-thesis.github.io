import SurveyStatements.P1MatchingIntersection

/-! Evaluating a predicted color when the second front advances by the
second available point. The color 'after' confines its finite witness to
the old front. -/

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem finiteWitness_subset_front_of_after (A W : Finset ℕ) (M : Set ℕ) (z : ℕ)
    (hWM : (W : Set ℕ) ⊆ M) (hmin : ∀ i ∈ M \ A, z ≤ i)
    (hz : z ∉ W) (hmax : ∀ i ∈ W, i ≤ z) : W ⊆ A := by
  intro i hi
  by_contra hiA
  have hzi := hmin i ⟨hWM hi, hiA⟩
  have heq : i = z := le_antisymm (hmax i hi) hzi
  exact hz (heq ▸ hi)

section Run

variable (F : Set ℕ → Finset ℕ) (hF : IsLocallyConstantFiniteAssignment F)
  (N : Set ℕ) (hN : N.Infinite)

local notation "q" => twoFrontMatchRun F hF N hN
local notation "L" => finiteFrontLimit (fun n => (q n).frontA)
local notation "M" => finiteFrontLimit (fun n => (q n).frontB)

theorem twoFrontMatchRun_residualB_ge_Y (n : ℕ)
    (hshape : (q (n + 1)).frontB = insert (twoFrontMatchY (q n)) (q n).frontB) :
    ∀ i ∈ M \ (q n).frontB, twoFrontMatchY (q n) ≤ i := by
  intro i hi
  by_cases hinext : i ∈ (q (n + 1)).frontB
  · rw [hshape] at hinext
    rcases Finset.mem_insert.mp hinext with rfl | hiold
    · exact le_rfl
    · exact False.elim (hi.2 hiold)
  · have hitail := twoFrontMatchRun_limitB_tail F hF N hN (n + 1) ⟨hi.1, hinext⟩
    exact (twoFrontMatchNext_tail F hF (q n) hitail).2.le

theorem twoFrontMatchRun_predictB_at_Y (n : ℕ)
    (hshape : (q (n + 1)).frontB = insert (twoFrontMatchY (q n)) (q n).frontB) :
    finiteSetMatchingColor F M (twoFrontMatchY (q n)) = (q n).colorB := by
  let Q := M \ (q n).frontB
  have hQ : Q.Infinite := (twoFrontMatchRun_limitB_infinite F hF N hN).diff
    (q n).frontB.finite_toSet
  have hQtail : Q ⊆ (q n).tail := twoFrontMatchRun_limitB_tail F hF N hN n
  have hyQ : twoFrontMatchY (q n) ∈ Q := by
    refine ⟨finiteFront_subset_limit _ (n + 1) ?_,
      twoFrontMatchRun_Y_not_frontB F hF N hN n⟩
    rw [hshape]
    exact Finset.mem_insert_self _ _
  have hmin : sInf Q = twoFrontMatchY (q n) := by
    apply le_antisymm (Nat.sInf_le hyQ)
    exact twoFrontMatchRun_residualB_ge_Y F hF N hN n hshape _ (Nat.sInf_mem hQ.nonempty)
  have hfront : ((q n).frontB : Set ℕ) ∪ Q = M := by
    ext i
    constructor
    · rintro (hi | hi)
      · exact finiteFront_subset_limit _ n hi
      · exact hi.1
    · intro hi
      by_cases hif : i ∈ (q n).frontB
      · exact Or.inl hif
      · exact Or.inr ⟨hi, hif⟩
  have hp := (q n).predictsB Q hQtail hQ
  rwa [hfront, hmin] at hp

theorem twoFrontMatchRun_witnessA_subset_front_after
    (hsupp : ∀ A : Set ℕ, A.Infinite → (F A : Set ℕ) ⊆ A) (n : ℕ)
    (hc : finiteSetMatchingColor F L (twoFrontMatchX (q n)) = .after) :
    F L ⊆ (q n).frontA := by
  obtain ⟨hz, hmax⟩ := (finiteSetMatchingColor_after F L _).mp hc
  apply finiteWitness_subset_front_of_after _ _ _ _
    (hsupp L (twoFrontMatchRun_limitA_infinite F hF N hN)) _ hz hmax
  intro i hi
  exact Nat.sInf_le (twoFrontMatchRun_limitA_tail F hF N hN n hi)

theorem twoFrontMatchRun_witnessB_subset_front_after
    (hsupp : ∀ A : Set ℕ, A.Infinite → (F A : Set ℕ) ⊆ A) (n : ℕ)
    (hshape : (q (n + 1)).frontB = insert (twoFrontMatchY (q n)) (q n).frontB)
    (hc : finiteSetMatchingColor F M (twoFrontMatchY (q n)) = .after) :
    F M ⊆ (q n).frontB := by
  obtain ⟨hz, hmax⟩ := (finiteSetMatchingColor_after F M _).mp hc
  exact finiteWitness_subset_front_of_after _ _ _ _
    (hsupp M (twoFrontMatchRun_limitB_infinite F hF N hN))
    (twoFrontMatchRun_residualB_ge_Y F hF N hN n hshape) hz hmax

end Run

end SurveyStatements.P1
