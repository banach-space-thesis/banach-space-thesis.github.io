import JLMS.DiscontinuousLinearWitness
import JLMS.OrthogonalCopies
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Johnson's diagonal argument for countably many full orthogonal copies

Suppose vₙuₘ = δₙₘ 1. A discontinuous homomorphism would admit very small tₙ
with arbitrarily large images. The series of uₙtₙvₙ converges in the source
algebra, while vₙ(∑ uₘtₘvₘ)uₙ = tₙ. Applying the homomorphism to this
identity bounds all the supposedly large images by one fixed element.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem continuous_hom_of_orthogonalCopies (φ : B →ₙₐ[𝕜] A)
    (u v : ℕ → B) (hvu : ∀ n m, v n * u m = if n = m then 1 else 0) :
    Continuous φ := by
  by_contra hφ
  let f : B →ₗ[𝕜] A := {
    toFun := φ
    map_add' := φ.map_add
    map_smul' := φ.map_smul
  }
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hrone : r < 1 := by norm_num [r]
  let ε : ℕ → ℝ := fun n => r ^ n / ((‖u n‖ + 1) * (‖v n‖ + 1))
  let M : ℕ → ℝ := fun n => (n : ℝ) * (‖φ (v n)‖ * ‖φ (u n)‖ + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hwitness (n) : ∃ t : B, ‖t‖ ≤ ε n ∧ M n < ‖φ t‖ :=
    exists_small_large_of_not_continuous f hφ (hε n) (M n)
  choose t ht hlarge using hwitness
  let b : ℕ → B := fun n => u n * t n * v n
  have hbound (n) : ‖b n‖ ≤ r ^ n := by
    have h₁ := norm_mul_le (u n * t n) (v n)
    have h₂ := norm_mul_le (u n) (t n)
    have h₃ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg (v n))
    have h₄ := mul_le_mul_of_nonneg_left (ht n) (norm_nonneg (u n))
    have h₅ := mul_le_mul_of_nonneg_right h₄ (norm_nonneg (v n))
    have h₆ : ‖u n‖ * ε n * ‖v n‖ ≤
        (‖u n‖ + 1) * ε n * (‖v n‖ + 1) := by
      gcongr <;> linarith
    have hcancel : (‖u n‖ + 1) * ε n * (‖v n‖ + 1) = r ^ n := by
      dsimp [ε]
      field_simp
    exact h₁.trans (h₃.trans (h₅.trans (h₆.trans hcancel.le)))
  have hb : Summable b :=
    ((summable_geometric_of_lt_one hr.le hrone).of_nonneg_of_le
      (fun n => norm_nonneg (b n)) hbound).of_norm
  let T : B := ∑' n, b n
  have hcoordinate (n m) : v n * b m * u n = if m = n then t n else 0 := by
    change v n * (u m * t m * v m) * u n = _
    calc
      v n * (u m * t m * v m) * u n = (v n * u m) * t m * (v m * u n) := by
        simp only [mul_assoc]
      _ = if m = n then t n else 0 := by
        by_cases h : m = n
        · subst m; simp [hvu]
        · simp [hvu, h, Ne.symm h]
  have hextract (n) : v n * T * u n = t n := by
    dsimp [T]
    rw [← hb.tsum_mul_left, ← (hb.mul_left (v n)).tsum_mul_right]
    simp only [hcoordinate]
    simp
  obtain ⟨n, hn⟩ := exists_nat_gt ‖φ T‖
  have hnorm : ‖φ (t n)‖ ≤ ‖φ (v n)‖ * ‖φ T‖ * ‖φ (u n)‖ := by
    rw [← hextract n, map_mul, map_mul]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hp : 0 ≤ ‖φ (v n)‖ * ‖φ (u n)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsmall : ‖φ (v n)‖ * ‖φ T‖ * ‖φ (u n)‖ < M n := by
    dsimp [M]
    have h := mul_lt_mul_of_pos_right hn (by positivity : 0 < ‖φ (v n)‖ * ‖φ (u n)‖ + 1)
    nlinarith [norm_nonneg (φ T)]
  exact (not_lt_of_ge hnorm) ((hlarge n).trans' hsmall)

theorem continuous_hom_of_twoCopies (φ : B →ₙₐ[𝕜] A)
    (u₀ u₁ v₀ v₁ : B)
    (h₀₀ : v₀ * u₀ = 1) (h₁₁ : v₁ * u₁ = 1)
    (h₀₁ : v₀ * u₁ = 0) (h₁₀ : v₁ * u₀ = 0) : Continuous φ := by
  obtain ⟨u, v, hvu⟩ := exists_orthogonalCopies u₀ u₁ v₀ v₁ h₀₀ h₁₁ h₀₁ h₁₀
  exact continuous_hom_of_orthogonalCopies φ u v hvu

end JLMS
