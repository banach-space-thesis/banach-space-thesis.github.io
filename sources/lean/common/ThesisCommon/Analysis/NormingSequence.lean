import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-! Norming sequences. The lower estimate is essential; compare Sigma Definition 3.2
with Definition 3.1 of de Hevia et al., arXiv:2310.02196v2.
-/
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A c-norming sequence in the dual unit ball, in the conventional sense. -/
def IsCNorming (e : ℕ → E →L[ℝ] ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1 ∧ (∀ n, ‖e n‖ ≤ 1) ∧ ∀ x, c * ‖x‖ ≤ ⨆ n, |e n x|

def IsNorming (e : ℕ → E →L[ℝ] ℝ) : Prop := ∃ c, IsCNorming e c

/-- The desired property, Sigma Definition 3.3, with conventional norming. -/
def DesiredProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ e : ℕ → E →L[ℝ] ℝ, IsNorming e →
    ∃ f : E, ¬ ∃ g : E, ∀ n, e n g = |e n f|

/-- A bounded sequence of evaluations has a genuine real supremum. -/
theorem evaluations_bddAbove (e : ℕ → E →L[ℝ] ℝ) (he : ∀ n, ‖e n‖ ≤ 1) (x : E) :
    BddAbove (Set.range fun n => |e n x|) := by
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    |e n x| = ‖e n x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖e n‖ * ‖x‖ := (e n).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (he n) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- The coordinate map associated with a norming sequence is injective. -/
theorem norming_separates_points {e : ℕ → E →L[ℝ] ℝ} (he : IsNorming e)
    {x y : E} (h : ∀ n, e n x = e n y) : x = y := by
  rcases he with ⟨c, hc, _, _, hnorm⟩
  have hz : ∀ n, e n (x - y) = 0 := fun n => by simp [map_sub, h n]
  have hbound := hnorm (x - y)
  simp only [hz, abs_zero, ciSup_const] at hbound
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Select a functional with a uniform lower bound for each unit vector.
This is a choice of indices, with no unjustified assertion that they increase. -/
theorem select_large_evaluations {e : ℕ → E →L[ℝ] ℝ} {c : ℝ} (he : IsCNorming e c)
    (f : ℕ → E) (hf : ∀ n, ‖f n‖ = 1) :
    ∃ k : ℕ → ℕ, ∀ n, c/2 < |e (k n) (f n)| := by
  classical
  have hex (n : ℕ) : ∃ k : ℕ, c/2 < |e k (f n)| := by
    have h := he.2.2.2 (f n)
    rw [hf n, mul_one] at h
    apply exists_lt_of_lt_ciSup
    exact lt_of_lt_of_le (by linarith [he.1]) h
  exact ⟨fun n => Classical.choose (hex n), fun n => Classical.choose_spec (hex n)⟩

/-- Negating DP produces an actual norming sequence whose coordinate image is
closed under modulus. This is only the logical part of Proposition 3.4. -/
theorem not_desiredProperty_iff :
    ¬ DesiredProperty E ↔ ∃ e : ℕ → E →L[ℝ] ℝ,
      IsNorming e ∧ ∀ f : E, ∃ g : E, ∀ n, e n g = |e n f| := by
  classical
  simp only [DesiredProperty, not_forall, not_exists, not_not, exists_prop]

end ThesisCommon
