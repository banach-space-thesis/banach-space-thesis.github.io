import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-! Finite-sign orthogonality and Jensen estimates used by the self-similar
reductions in UPFP Sections 3 and 4. The expectation is the explicit uniform
average over all sign choices. Orthogonality is proved by flipping one sign.
The vector-valued average identity followed by the triangle inequality is
the norm version of the scalar-functional estimate in the manuscript.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

section AddGroup
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup X]

def signedValue (b : Bool) (x : X) : X := if b then x else -x

@[simp] theorem signedValue_self (b : Bool) (x : X) :
    signedValue b (signedValue b x) = x := by cases b <;> simp [signedValue]

theorem signedValue_sum {κ : Type*} (s : Finset κ) (f : κ → X) (b : Bool) :
    signedValue b (∑ i ∈ s, f i) = ∑ i ∈ s, signedValue b (f i) := by
  cases b <;> simp [signedValue]

def flipSign (i : ι) (θ : ι → Bool) : ι → Bool := Function.update θ i (!(θ i))

omit [Fintype ι] in
@[simp] theorem flipSign_self (i : ι) (θ : ι → Bool) : flipSign i θ i = !(θ i) := by
  simp [flipSign]

omit [Fintype ι] in
@[simp] theorem flipSign_other {i j : ι} (h : j ≠ i) (θ : ι → Bool) :
    flipSign i θ j = θ j := by simp [flipSign, h]

omit [Fintype ι] in
@[simp] theorem flipSign_flipSign (i : ι) (θ : ι → Bool) :
    flipSign i (flipSign i θ) = θ := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem signed_correlation_sum_zero {i j : ι} (hij : i ≠ j) (x : X) :
    (∑ θ : ι → Bool, signedValue (θ i) (signedValue (θ j) x)) = 0 := by
  apply Finset.sum_ninvolution (flipSign i)
  · intro θ
    simp only [flipSign_self, flipSign_other hij.symm]
    cases θ i <;> simp [signedValue]
  · intro θ _ heq
    have h := congrFun heq i
    simp only [flipSign_self] at h
    cases θ i <;> simp at h
  · intro θ; exact Finset.mem_univ _
  · exact flipSign_flipSign i

/-- Multiplying by one sign and summing all choices extracts that coefficient. -/
theorem signed_sum_orthogonality (x : ι → X) (i : ι) :
    (∑ θ : ι → Bool, signedValue (θ i) (∑ j, signedValue (θ j) (x j))) =
      Fintype.card (ι → Bool) • x i := by
  simp_rw [signedValue_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact signed_correlation_sum_zero hji.symm (x j)
  · simp

end AddGroup

section Normed
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem norm_signedValue (b : Bool) (x : X) : ‖signedValue b x‖ = ‖x‖ := by
  cases b <;> simp [signedValue]

include 𝕜

/-- A coefficient is bounded by the average norm of the signed sums. -/
theorem norm_le_sign_average (x : ι → X) (i : ι) :
    ‖x i‖ ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ *
      ∑ θ : ι → Bool, ‖∑ j, signedValue (θ j) (x j)‖ := by
  have hcard : 0 < (Fintype.card (ι → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Bool))
    (fun θ => signedValue (θ i) (∑ j, signedValue (θ j) (x j)))
  rw [signed_sum_orthogonality] at hsum
  simp only [norm_signedValue] at hsum
  have hnorm : ‖Fintype.card (ι → Bool) • x i‖ =
      (Fintype.card (ι → Bool) : ℝ) * ‖x i‖ := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, norm_smul]
    simp
  rw [hnorm] at hsum
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hcard).mpr (by simpa only [mul_comm] using hsum)

/-- Jensen's p-moment estimate for each coefficient, valid for every p≥1. -/
theorem norm_rpow_le_sign_average (x : ι → X) (i : ι) {p : ℝ} (hp : 1 ≤ p) :
    ‖x i‖ ^ p ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹ *
      ∑ θ : ι → Bool, ‖∑ j, signedValue (θ j) (x j)‖ ^ p := by
  have havg := Real.rpow_le_rpow (norm_nonneg _) (norm_le_sign_average (𝕜 := 𝕜) x i)
    (zero_le_one.trans hp)
  have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow
    (Finset.univ : Finset (ι → Bool))
    (fun _ => (Fintype.card (ι → Bool) : ℝ)⁻¹)
    (fun θ => ‖∑ j, signedValue (θ j) (x j)‖)
    (by intros; positivity) (by simp) (by intros; positivity) hp
  simp only [← Finset.mul_sum] at hjensen
  exact havg.trans hjensen

end Normed
end ThesisCommon
