import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-!
# Square-summable coordinates of a functional on a square-summable sum

The estimate below uses genuine vectors on which each coordinate functional
attains at least half its norm. No dual representation is assumed.
-/

noncomputable section

set_option autoImplicit false

open scoped ENNReal
open Finset
open scoped ComplexConjugate

namespace SurveyStatements.P4

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {ι : Type v} [DecidableEq ι] {E : ι → Type w}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def lp2DualCoordinate (φ : StrongDual 𝕜 (lp E 2)) (i : ι) : StrongDual 𝕜 (E i) :=
  φ.comp (lp.singleContinuousLinearMap 𝕜 E 2 i)

lemma lp2DualCoordinate_apply (φ : StrongDual 𝕜 (lp E 2)) (i : ι) (x : E i) :
    lp2DualCoordinate φ i x = φ (lp.single 2 i x) := rfl

lemma sum_sq_lp2DualCoordinate_values_le (φ : StrongDual 𝕜 (lp E 2))
    (x : ∀ i, E i) (hx : ∀ i, ‖x i‖ ≤ 1) (s : Finset ι) :
    ∑ i ∈ s, ‖lp2DualCoordinate φ i (x i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  classical
  let a : ι → 𝕜 := fun i => lp2DualCoordinate φ i (x i)
  let y : ∀ i, E i := fun i => conj (a i) • x i
  let z : lp E 2 := ∑ i ∈ s, lp.single 2 i (y i)
  let A : ℝ := ∑ i ∈ s, ‖a i‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hvalue : φ z = (A : 𝕜) := by
    simp only [z, map_sum]
    simp only [← lp2DualCoordinate_apply, y, map_smul, smul_eq_mul]
    simp only [A, a, RCLike.ofReal_sum, RCLike.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    exact RCLike.conj_mul _
  have hnorm : ‖z‖ ^ 2 ≤ A := by
    have hn := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    rw [show ‖z‖ ^ 2 = ∑ i ∈ s, ‖y i‖ ^ 2 from hn]
    apply Finset.sum_le_sum
    intro i hi
    have hy : ‖y i‖ ≤ ‖a i‖ := by
      dsimp [y]
      rw [norm_smul, RCLike.norm_conj]
      exact (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)).trans_eq (mul_one _)
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hbound : A ≤ ‖φ‖ * ‖z‖ := by
    have h := φ.le_opNorm z
    rw [hvalue, RCLike.norm_ofReal, abs_of_nonneg hA] at h
    exact h
  have hsquare := pow_le_pow_left₀ hA hbound 2
  have hmul := mul_le_mul_of_nonneg_left hnorm (sq_nonneg ‖φ‖)
  change A ≤ ‖φ‖ ^ 2
  nlinarith [norm_nonneg z, norm_nonneg φ]

lemma sum_sq_lp2DualCoordinate_norm_le (φ : StrongDual 𝕜 (lp E 2)) (s : Finset ι) :
    ∑ i ∈ s, ‖lp2DualCoordinate φ i‖ ^ 2 ≤ 4 * ‖φ‖ ^ 2 := by
  classical
  have hex (i : ι) : ∃ x : E i, ‖x‖ ≤ 1 ∧
      ‖lp2DualCoordinate φ i‖ / 2 ≤ ‖lp2DualCoordinate φ i x‖ := by
    by_cases hzero : ‖lp2DualCoordinate φ i‖ = 0
    · exact ⟨0, by simp, by simp [hzero]⟩
    · have hp : 0 < ‖lp2DualCoordinate φ i‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      obtain ⟨x, hx, hφx⟩ := (lp2DualCoordinate φ i).exists_lt_apply_of_lt_opNorm
        (by linarith : ‖lp2DualCoordinate φ i‖ / 2 < ‖lp2DualCoordinate φ i‖)
      exact ⟨x, hx.le, hφx.le⟩
  choose x hx hφx using hex
  calc
    ∑ i ∈ s, ‖lp2DualCoordinate φ i‖ ^ 2 ≤
        ∑ i ∈ s, 4 * ‖lp2DualCoordinate φ i (x i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ ‖lp2DualCoordinate φ i‖ / 2)
        (hφx i) 2
      nlinarith
    _ = 4 * ∑ i ∈ s, ‖lp2DualCoordinate φ i (x i)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * ‖φ‖ ^ 2 := mul_le_mul_of_nonneg_left
      (sum_sq_lp2DualCoordinate_values_le φ x hx s) (by norm_num)

lemma summable_sq_lp2DualCoordinate_norm (φ : StrongDual 𝕜 (lp E 2)) :
    Summable (fun i => ‖lp2DualCoordinate φ i‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (sum_sq_lp2DualCoordinate_norm_le φ)

end SurveyStatements.P4
