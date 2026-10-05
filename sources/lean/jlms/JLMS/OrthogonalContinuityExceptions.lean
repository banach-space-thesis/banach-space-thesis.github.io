import JLMS.DiscontinuousLinearWitness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Only finitely many orthogonal extraction maps can detect discontinuity

This diagonal-series argument supplies the projection consequence of the main
boundedness theorem used in Ogden Lemma 6.15. It is stated for linear maps
between Banach spaces, so it can be reused for left and right multiplication.
The image of each coordinate extraction has a fixed bound in terms of the
image of the whole vector. Assuming every extracted map discontinuous would
produce a convergent series contradicting these bounds.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_continuous_orthogonalExtraction (f : E →ₗ[𝕜] F)
    (P : ℕ → E →L[𝕜] E)
    (hP : ∀ n m x, P n (P m x) = if n = m then P n x else 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hbound : ∀ n x, ‖f (P n x)‖ ≤ c n * ‖f x‖) :
    ∃ n, Continuous (f.comp (P n).toLinearMap) := by
  by_contra h
  push_neg at h
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hrone : r < 1 := by norm_num [r]
  let ε (n : ℕ) : ℝ := r ^ n / (‖P n‖ + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hw (n) := exists_small_large_of_not_continuous
    (f.comp (P n).toLinearMap) (h n) (hε n) ((n : ℝ) * (c n + 1))
  choose x hx hlarge using hw
  let b (n : ℕ) : E := P n (x n)
  have hnorm (n) : ‖b n‖ ≤ r ^ n := by
    calc
      ‖b n‖ ≤ ‖P n‖ * ‖x n‖ := (P n).le_opNorm (x n)
      _ ≤ ‖P n‖ * ε n := mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _)
      _ ≤ (‖P n‖ + 1) * ε n := by gcongr; linarith
      _ = r ^ n := by dsimp [ε]; field_simp
  have hb : Summable b :=
    ((summable_geometric_of_lt_one hr.le hrone).of_nonneg_of_le
      (fun n => norm_nonneg (b n)) hnorm).of_norm
  let T : E := ∑' n, b n
  have hcoordinate (n m) : P n (b m) = if m = n then b n else 0 := by
    by_cases hnm : m = n
    · subst m; simp [b, hP]
    · simp [b, hP, hnm, Ne.symm hnm]
  have hextract (n) : P n T = b n := by
    dsimp [T]
    rw [(P n).map_tsum hb]
    simp only [hcoordinate]
    simp
  obtain ⟨n, hn⟩ := exists_nat_gt ‖f T‖
  have hsmall : c n * ‖f T‖ < (n : ℝ) * (c n + 1) := by
    have hh := mul_lt_mul_of_pos_right hn (by linarith [hc n] : 0 < c n + 1)
    nlinarith [hc n, norm_nonneg (f T)]
  have hh := hbound n T
  rw [hextract n] at hh
  exact (not_lt_of_ge hh) (hsmall.trans (hlarge n))

theorem orthogonalExtraction_exceptions_finite (f : E →ₗ[𝕜] F)
    (P : ℕ → E →L[𝕜] E)
    (hP : ∀ n m x, P n (P m x) = if n = m then P n x else 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hbound : ∀ n x, ‖f (P n x)‖ ≤ c n * ‖f x‖) :
    {n | ¬ Continuous (f.comp (P n).toLinearMap)}.Finite := by
  by_contra hfinite
  let s := Set.Infinite.natEmbedding _ hfinite
  have hPs (n m : ℕ) (x : E) :
      P (s n).val (P (s m).val x) = if n = m then P (s n).val x else 0 := by
    rw [hP]
    by_cases hnm : n = m
    · subst m; simp
    · have hne : (s n).val ≠ (s m).val := by
        intro he
        exact hnm (s.injective (Subtype.ext he))
      rw [if_neg hne, if_neg hnm]
  obtain ⟨n, hn⟩ := exists_continuous_orthogonalExtraction f
    (fun n => P (s n).val) hPs (fun n => c (s n).val)
    (fun n => hc _) (fun n x => hbound _ x)
  exact (s n).property hn

end JLMS
