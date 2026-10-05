import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Normed.Operator.Basic

/-! Actual integrals of finite pointwise maxima in scalar L1. These are
the analytic quantities used by the Enflo--Starbird dyadic-bush criterion;
no embedding or factorization property is assumed in their definition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThesisCommon

def finiteMaxNorm {E : Type*} [Norm E] : ℕ → (ℕ → E) → ℝ
  | 0, _ => 0
  | n + 1, a => max (finiteMaxNorm n a) ‖a n‖

section FiniteMaximum
variable {E : Type*} [SeminormedAddCommGroup E]

theorem finiteMaxNorm_nonneg (n : ℕ) (a : ℕ → E) : 0 ≤ finiteMaxNorm n a := by
  cases n with
  | zero => rfl
  | succ n => exact (norm_nonneg _).trans (le_max_right _ _)

theorem norm_le_finiteMaxNorm {n j : ℕ} (a : ℕ → E) (hj : j < n) :
    ‖a j‖ ≤ finiteMaxNorm n a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j < n
    · exact (ih h).trans (le_max_left _ _)
    · have he : j = n := by omega
      subst j
      exact le_max_right _ _

theorem finiteMaxNorm_le {n : ℕ} {a : ℕ → E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j < n, ‖a j‖ ≤ C) : finiteMaxNorm n a ≤ C := by
  induction n with
  | zero => exact hC
  | succ n ih =>
    exact max_le (ih (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h n (Nat.lt_succ_self n))

theorem finiteMaxNorm_le_sum (n : ℕ) (a : ℕ → E) :
    finiteMaxNorm n a ≤ ∑ j ∈ Finset.range n, ‖a j‖ :=
  finiteMaxNorm_le (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun _ hj => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hj))

theorem finiteMaxNorm_add_le (n : ℕ) (a b : ℕ → E) :
    finiteMaxNorm n (fun j => a j + b j) ≤ finiteMaxNorm n a + finiteMaxNorm n b := by
  apply finiteMaxNorm_le (add_nonneg (finiteMaxNorm_nonneg n a) (finiteMaxNorm_nonneg n b))
  intro j hj
  exact (norm_add_le _ _).trans (add_le_add (norm_le_finiteMaxNorm a hj) (norm_le_finiteMaxNorm b hj))

end FiniteMaximum

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem integrable_finiteMaxNorm (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) :
    Integrable (fun x => finiteMaxNorm n (fun j => f j x)) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact ih.sup (L1.integrable_coeFn (f n)).norm

def l1FiniteMaximumMass (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) : ℝ :=
  ∫ x, finiteMaxNorm n (fun j => f j x) ∂μ

theorem l1FiniteMaximumMass_nonneg (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) :
    0 ≤ l1FiniteMaximumMass n f := integral_nonneg (fun _ => finiteMaxNorm_nonneg n _)

theorem l1FiniteMaximumMass_le_sum_norm (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) :
    l1FiniteMaximumMass n f ≤ ∑ j ∈ Finset.range n, ‖f j‖ := by
  have h := integral_mono (integrable_finiteMaxNorm n f)
    (integrable_finset_sum _ (fun j _ => (L1.integrable_coeFn (f j)).norm))
    (fun x => finiteMaxNorm_le_sum n (fun j => f j x))
  rw [integral_finset_sum _ (fun j _ => (L1.integrable_coeFn (f j)).norm)] at h
  simpa only [l1FiniteMaximumMass, ← L1.norm_eq_integral_norm] using h

theorem l1FiniteMaximumMass_add_le (n : ℕ) (f g : ℕ → Lp 𝕜 1 μ) :
    l1FiniteMaximumMass n (fun j => f j + g j) ≤
      l1FiniteMaximumMass n f + l1FiniteMaximumMass n g := by
  rw [l1FiniteMaximumMass, l1FiniteMaximumMass, l1FiniteMaximumMass,
    ← integral_add (integrable_finiteMaxNorm n f) (integrable_finiteMaxNorm n g)]
  apply integral_mono_ae (integrable_finiteMaxNorm n _)
    ((integrable_finiteMaxNorm n f).add (integrable_finiteMaxNorm n g))
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_add (f j) (g j))] with x hx
  simpa only [hx, Pi.add_apply] using finiteMaxNorm_add_le n (fun j => f j x) (fun j => g j x)

theorem l1FiniteMaximumMass_le_add_sum_norm_sub (n : ℕ) (f g : ℕ → Lp 𝕜 1 μ) :
    l1FiniteMaximumMass n f ≤ l1FiniteMaximumMass n g +
      ∑ j ∈ Finset.range n, ‖f j - g j‖ := by
  have h := l1FiniteMaximumMass_add_le n g (fun j => f j - g j)
  simp only [add_sub_cancel] at h
  exact h.trans (add_le_add le_rfl (l1FiniteMaximumMass_le_sum_norm n (fun j => f j - g j)))

end ThesisCommon
