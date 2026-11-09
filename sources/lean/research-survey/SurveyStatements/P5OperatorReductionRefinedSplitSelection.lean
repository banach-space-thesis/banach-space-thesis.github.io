import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5Support.LpHaarFiniteSplits

/-! Finite sign selection returns an actual faithful split in the chosen
absolute-level reservoir, preserving the original parent set exactly. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem refineAt_nonempty_of_parent (P : LpHaarFiniteParent) (n : ℕ)
    (hn : P.level ≤ n) : (lpHaarRefineAt P.level P.atoms n).Nonempty := by
  by_contra h
  have hz : (lpHaarRefineAt P.level P.atoms n).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
  have hm := lpHaarRefineAt_mass P.level P.atoms n hn
  simp only [hz, Nat.cast_zero, zero_mul] at hm
  have hc : 0 < (P.atoms.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr P.nonempty
  exact (ne_of_gt (mul_pos hc (intervalLpDyadicRadius_pos P.level))) hm.symm

def refinedFiniteSplit (P : LpHaarFiniteParent) (n : ℕ) (hn : P.level ≤ n)
    (θ : Fin (2 ^ n) → Bool) : LpHaarFiniteSplit :=
  ⟨n, lpHaarRefineAt P.level P.atoms n, θ, refineAt_nonempty_of_parent P n hn⟩

theorem refinedFiniteSplit_parent (P : LpHaarFiniteParent) (n : ℕ) (hn : P.level ≤ n)
    (θ : Fin (2 ^ n) → Bool) : (refinedFiniteSplit P n hn θ).parent.set = P.set :=
  lpHaarRefineAt_parent P.level P.atoms n hn

theorem exists_refined_split_in_reservoir_with_finite_errors {m : ℕ}
    (P : LpHaarFiniteParent) (r : ℕ → ℕ) (hr : StrictMono r)
    (f : (n : ℕ) → Fin m → (Fin (2 ^ n) → Bool) → 𝕜)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ᶠ k in atTop,
      (∑ i, mean (fun θ => ‖f (r k) i θ‖ ^ 2)) < ε ^ 2) :
    ∃ S : LpHaarFiniteSplit, ∃ k : ℕ, S.level = r k ∧ N ≤ S.level ∧
      S.parent.set = P.set ∧ ∀ i, ‖f S.level i S.signs‖ < ε := by
  have hlate : ∀ᶠ k in atTop, max N P.level ≤ r k :=
    hr.tendsto_atTop.eventually (eventually_ge_atTop (max N P.level))
  obtain ⟨k, hk, herror⟩ := (hlate.and hsmall).exists
  obtain ⟨θ, hθ⟩ := finite_sign_simultaneous_small (f (r k)) hε herror
  have hP : P.level ≤ r k := (le_max_right N P.level).trans hk
  refine ⟨refinedFiniteSplit P (r k) hP θ, k, rfl,
    (le_max_left N P.level).trans hk, refinedFiniteSplit_parent P (r k) hP θ, ?_⟩
  exact hθ

end SurveyStatements.P5OperatorReduction
