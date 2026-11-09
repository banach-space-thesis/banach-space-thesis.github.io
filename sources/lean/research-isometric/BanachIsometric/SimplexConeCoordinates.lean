import BanachIsometric.SignedSimplexFaceGeometry

/-! Coordinates for the straight cone with apex at the first vertex. The
remaining barycentric weights are divided by their sum away from that apex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped NNReal

def simplexConeRadius (n : ℕ) (w : Simplex (n + 1)) : ℝ := 1 - w 0

theorem simplexConeRadius_nonneg (n : ℕ) (w : Simplex (n + 1)) :
    0 ≤ simplexConeRadius n w := sub_nonneg.mpr (stdSimplex.le_one w 0)

theorem simplexConeRadius_le_one (n : ℕ) (w : Simplex (n + 1)) :
    simplexConeRadius n w ≤ 1 := sub_le_self _ (stdSimplex.zero_le w 0)

theorem simplexConeRadius_eq_sum (n : ℕ) (w : Simplex (n + 1)) :
    simplexConeRadius n w = ∑ j : Fin (n + 1), w j.succ := by
  have hs := stdSimplex.sum_eq_one w
  rw [Fin.sum_univ_succ] at hs
  change 1 - w 0 = _
  linarith

def simplexConeBase (n : ℕ) (w : Simplex (n + 1)) (h : 0 < simplexConeRadius n w) : Simplex n :=
  ⟨fun j => w j.succ / simplexConeRadius n w,
    fun j => div_nonneg (stdSimplex.zero_le w j.succ) h.le, by
      change (∑ j : Fin (n + 1), w j.succ / simplexConeRadius n w) = 1
      rw [← Finset.sum_div, ← simplexConeRadius_eq_sum, div_self h.ne']⟩

theorem simplexConeRadius_lipschitz (n : ℕ) : LipschitzWith 1 (simplexConeRadius n) := by
  apply LipschitzWith.of_dist_le_mul
  intro w z
  have h := (LipschitzWith.eval (0 : Fin (n + 2)) : LipschitzWith 1
    (Function.eval (0 : Fin (n + 2)) : (Fin (n + 2) → ℝ) → ℝ)).dist_le_mul w.val z.val
  simpa only [simplexConeRadius, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm,
    Function.eval] using h

theorem simplexConeBase_scaled_dist_le (n : ℕ) (w z : Simplex (n + 1))
    (hw : 0 < simplexConeRadius n w) (hz : 0 < simplexConeRadius n z) :
    simplexConeRadius n w * dist (simplexConeBase n w hw) (simplexConeBase n z hz) ≤ 2 * dist w z := by
  have hR : |simplexConeRadius n w - simplexConeRadius n z| ≤ dist w z := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (simplexConeRadius_lipschitz n).dist_le_mul w z
  apply (le_div_iff₀' hw).mp
  change dist (simplexConeBase n w hw).val (simplexConeBase n z hz).val ≤
    2 * dist w z / simplexConeRadius n w
  rw [dist_pi_le_iff (div_nonneg (by positivity) hw.le)]
  intro i
  apply (le_div_iff₀' hw).mpr
  rw [Real.dist_eq, ← abs_of_pos hw, ← abs_mul]
  have hcoord : |w i.succ - z i.succ| ≤ dist w z := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, Function.eval] using
      (LipschitzWith.eval i.succ : LipschitzWith 1
        (Function.eval i.succ : (Fin (n + 2) → ℝ) → ℝ)).dist_le_mul w.val z.val
  let b := simplexConeBase n z hz
  have hb : simplexConeRadius n z * b i = z i.succ := by
    change simplexConeRadius n z * (z i.succ / simplexConeRadius n z) = _
    field_simp
  have he : simplexConeRadius n w * (simplexConeBase n w hw i - b i) =
      (w i.succ - z i.succ) + (simplexConeRadius n z - simplexConeRadius n w) * b i := by
    have ha : simplexConeRadius n w * simplexConeBase n w hw i = w i.succ := by
      change simplexConeRadius n w * (w i.succ / simplexConeRadius n w) = _
      field_simp
    rw [mul_sub, ha, sub_mul, hb]
    ring
  change |simplexConeRadius n w * (simplexConeBase n w hw i - b i)| ≤ 2 * dist w z
  rw [he]
  calc
    |(w i.succ - z i.succ) + (simplexConeRadius n z - simplexConeRadius n w) * b i| ≤
        |w i.succ - z i.succ| + |simplexConeRadius n z - simplexConeRadius n w| * |b i| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    _ ≤ dist w z + dist w z * 1 := by
      rw [abs_sub_comm (simplexConeRadius n z), abs_of_nonneg (stdSimplex.zero_le b i)]
      exact add_le_add hcoord (mul_le_mul hR (stdSimplex.le_one b i) (stdSimplex.zero_le b i) dist_nonneg)
    _ = 2 * dist w z := by ring

end BanachIsometric.SingularPrism
