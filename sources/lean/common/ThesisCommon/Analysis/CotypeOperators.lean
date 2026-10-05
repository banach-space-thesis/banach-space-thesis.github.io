import ThesisCommon.Analysis.CotypeEstimates
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Data.Fintype.Pigeonhole

/-! The operator form of the finite-sign cotype estimate.
An explicit signed-sum norm hypothesis is supplied by disjoint coordinate
embeddings in c₀ and ℓ∞. It is not a cotype or factorisation assumption.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Choose unit test vectors, apply cotype to their images, and contradict
the common signed-sum bound. This is the numerical heart of UPFP §§3–4. -/
theorem HasRademacherCotype.exists_small_block_power {q C : ℝ}
    (h : HasRademacherCotype X q C) {n : ℕ} (J : Fin n → Y →L[𝕜] Z)
    (hJ : ∀ x : Fin n → Y, (∀ i, ‖x i‖ ≤ 1) →
      ∀ ε : Fin n → Bool, ‖∑ i, if ε i then J i (x i) else -(J i (x i))‖ ≤ 1)
    (T : Z →L[𝕜] X) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : C ^ q * M ^ q < (n : ℝ) * (ε / 2) ^ q) :
    ∃ i, ‖T.comp (J i)‖ < ε := by
  classical
  by_contra! hn
  have hx : ∀ i, ∃ x : Y, ‖x‖ < 1 ∧ ε / 2 < ‖T (J i x)‖ := by
    intro i
    exact (T.comp (J i)).exists_lt_apply_of_lt_opNorm (by linarith [hn i])
  choose x hxnorm hxlarge using hx
  have hsign : ∀ θ : Fin n → Bool,
      ‖∑ i, if θ i then T (J i (x i)) else -T (J i (x i))‖ ≤ M := by
    intro θ
    have heq : (∑ i, if θ i then T (J i (x i)) else -T (J i (x i))) =
        T (∑ i, if θ i then J i (x i) else -(J i (x i))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [heq]
    calc
      _ ≤ ‖T‖ * ‖∑ i, if θ i then J i (x i) else -(J i (x i))‖ := T.le_opNorm _
      _ ≤ M * 1 := mul_le_mul hT (hJ x (fun i => (hxnorm i).le) θ) (norm_nonneg _) hM
      _ = M := mul_one M
  obtain ⟨i, hi⟩ := h.exists_norm_lt_of_sign_bound (fun i => T (J i (x i)))
    hM (by positivity) hsign hlarge
  exact (not_lt_of_ge hi.le) (hxlarge i)

/-- Equivalent form using the threshold printed in the manuscript. -/
theorem HasRademacherCotype.exists_small_block {q C : ℝ}
    (h : HasRademacherCotype X q C) {n : ℕ} (J : Fin n → Y →L[𝕜] Z)
    (hJ : ∀ x : Fin n → Y, (∀ i, ‖x i‖ ≤ 1) →
      ∀ ε : Fin n → Bool, ‖∑ i, if ε i then J i (x i) else -(J i (x i))‖ ≤ 1)
    (T : Z →L[𝕜] X) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : 2 * C * M < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i, ‖T.comp (J i)‖ < ε :=
  h.exists_small_block_power J hJ T hε hM hT
    (cotype_power_threshold (by linarith [h.1]) (zero_le_one.trans h.2.1) hM hlarge)

/-- The forward-selection pigeonhole step: some input block is small on
infinitely many output coordinates. Output rows have a common norm bound. -/
theorem HasRademacherCotype.infinite_small_block {q C : ℝ}
    (h : HasRademacherCotype X q C) {n : ℕ} (J : Fin n → Y →L[𝕜] Z)
    (hJ : ∀ x : Fin n → Y, (∀ i, ‖x i‖ ≤ 1) →
      ∀ ε : Fin n → Bool, ‖∑ i, if ε i then J i (x i) else -(J i (x i))‖ ≤ 1)
    (T : ℕ → Z →L[𝕜] X) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hT : ∀ m, ‖T m‖ ≤ M) (hlarge : 2 * C * M < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i, {m : ℕ | ‖(T m).comp (J i)‖ < ε}.Infinite := by
  classical
  choose i hi using fun m => h.exists_small_block J hJ (T m) hε hM (hT m) hlarge
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
  have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  refine ⟨j, hj'.mono ?_⟩
  intro m hm
  have heq : i m = j := hm
  simpa only [Set.mem_setOf_eq, heq] using hi m

end ThesisCommon
