import SurveyStatements.P1RamseyNextColor
import Mathlib.Tactic.DeriveFintype

/-! The three colors in the one-set matching argument. They record whether
the next point belongs to the chosen finite set, precedes a later member,
or lies after its last member. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

inductive MatchingColor
  | inside
  | before
  | after
  deriving DecidableEq, Fintype

def finiteSetMatchingColor (F : Set ℕ → Finset ℕ) (M : Set ℕ) (n : ℕ) :
    MatchingColor := by
  classical
  exact if n ∈ F M then .inside else
    if ∃ i ∈ F M, n < i then .before else .after

theorem finiteSetMatchingColor_inside (F : Set ℕ → Finset ℕ)
    (M : Set ℕ) (n : ℕ) :
    finiteSetMatchingColor F M n = .inside ↔ n ∈ F M := by
  classical
  simp only [finiteSetMatchingColor]
  split_ifs <;> simp_all

theorem finiteSetMatchingColor_before (F : Set ℕ → Finset ℕ)
    (M : Set ℕ) (n : ℕ) :
    finiteSetMatchingColor F M n = .before ↔
      n ∉ F M ∧ ∃ i ∈ F M, n < i := by
  classical
  simp only [finiteSetMatchingColor]
  split_ifs <;> simp_all

theorem finiteSetMatchingColor_after (F : Set ℕ → Finset ℕ)
    (M : Set ℕ) (n : ℕ) :
    finiteSetMatchingColor F M n = .after ↔
      n ∉ F M ∧ ∀ i ∈ F M, i ≤ n := by
  classical
  simp only [finiteSetMatchingColor]
  split_ifs <;> simp_all

theorem finiteSetMatchingColor_locally_constant
    (F : Set ℕ → Finset ℕ)
    (hF : ∀ A : Set ℕ, A.Infinite → ∃ r : ℕ,
      ∀ B : Set ℕ, B.Infinite →
        (∀ i : ℕ, i < r → (i ∈ A ↔ i ∈ B)) → F B = F A) :
    ∀ A : Set ℕ, A.Infinite → ∀ n : ℕ, ∃ r : ℕ,
      ∀ B : Set ℕ, B.Infinite →
        (∀ i : ℕ, i < r → (i ∈ A ↔ i ∈ B)) →
          finiteSetMatchingColor F B n = finiteSetMatchingColor F A n := by
  intro A hA n
  obtain ⟨r, hr⟩ := hF A hA
  refine ⟨r, ?_⟩
  intro B hB heq
  unfold finiteSetMatchingColor
  rw [hr B hB heq]

theorem exists_twoFront_matching_prediction
    (F : Set ℕ → Finset ℕ)
    (hF : ∀ A : Set ℕ, A.Infinite → ∃ r : ℕ,
      ∀ B : Set ℕ, B.Infinite →
        (∀ i : ℕ, i < r → (i ∈ A ↔ i ∈ B)) → F B = F A)
    (frontA frontB : Finset ℕ) (M : Set ℕ) (hM : M.Infinite) :
    ∃ Y : Set ℕ, Y ⊆ M ∧ Y.Infinite ∧
      (∀ a ∈ frontA ∪ frontB, ∀ b ∈ Y, a < b) ∧
      ∃ colorA colorB : MatchingColor,
        (∀ Q : Set ℕ, Q ⊆ Y → Q.Infinite →
          finiteSetMatchingColor F ((frontA : Set ℕ) ∪ Q) (sInf Q) = colorA) ∧
        (∀ Q : Set ℕ, Q ⊆ Y → Q.Infinite →
          finiteSetMatchingColor F ((frontB : Set ℕ) ∪ Q) (sInf Q) = colorB) := by
  classical
  have hc := finiteSetMatchingColor_locally_constant F hF
  obtain ⟨T, hTM, hT, hsepA, a, hA⟩ :=
    ramsey_exists_nextColor_prediction (finiteSetMatchingColor F) hc frontA M hM
  obtain ⟨Y, hYT, hY, hsepB, b, hB⟩ :=
    ramsey_exists_nextColor_prediction (finiteSetMatchingColor F) hc frontB T hT
  refine ⟨Y, hYT.trans hTM, hY, ?_, a, b, ?_, hB⟩
  · intro n hn i hi
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hsepA n hn i (hYT hi)
    · exact hsepB n hn i hi
  · intro Q hQ hQinf
    exact hA Q (hQ.trans hYT) hQinf

end SurveyStatements.P1
