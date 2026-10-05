import ThesisCommon.Analysis.LpHaarNestedMeans

/-! The constant and dyadic Haar functions, with their actual bounded
coefficient maps and normalized biorthogonality in finite-exponent Lp. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def lpHaarRawVector : Option (Σ n : ℕ, Fin (2 ^ n)) → IntervalLp 𝕜 p
  | none => Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)
  | some ⟨n, k⟩ => lpHaarDyadic 𝕜 p n k

def lpHaarRawCoordinate : Option (Σ n : ℕ, Fin (2 ^ n)) → IntervalLp 𝕜 p →L[𝕜] 𝕜
  | none => lpHaarIntegral
  | some ⟨n, k⟩ => lpHaarDyadicCoefficient 𝕜 p n k

theorem lpHaarIntegral_const (c : 𝕜) :
    lpHaarIntegral (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) c) = c := by
  rw [lpHaarIntegral_apply, integral_congr_ae
    (Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) c)]
  simp

theorem lpHaarDyadicCoefficient_const (n : ℕ) (k : Fin (2 ^ n)) (c : 𝕜) :
    lpHaarDyadicCoefficient 𝕜 p n k
      (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) c) = 0 := by
  have hm : (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell (n + 1) (2 * k)) =
      (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell (n + 1) (2 * k + 1)) := by
    rw [lpHaarCell_measure (n + 1) (2 * k) (by rw [pow_succ]; omega),
      lpHaarCell_measure (n + 1) (2 * k + 1) (by rw [pow_succ]; omega)]
  apply lpHaarCoefficient_constant_on
    (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
    measurableSet_Ioc measurableSet_Ioc (lpHaarCell_disjoint_sameLevel (n + 1) (by omega))
    hm _ c
  filter_upwards [Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) c] with x hx
  intro _
  exact hx

theorem lpHaarRaw_biorthogonal (hp : p.val ≠ ∞)
    (i j : Option (Σ n : ℕ, Fin (2 ^ n))) :
    lpHaarRawCoordinate 𝕜 p i (lpHaarRawVector 𝕜 p j) = if i = j then 1 else 0 := by
  cases i with
  | none =>
      cases j with
      | none => simpa [lpHaarRawCoordinate, lpHaarRawVector] using lpHaarIntegral_const 𝕜 p 1
      | some j =>
          simpa [lpHaarRawCoordinate, lpHaarRawVector] using
            lpHaarDyadic_integral_zero 𝕜 p j.1 j.2 j.2.isLt
  | some i =>
      cases j with
      | none =>
          simpa [lpHaarRawCoordinate, lpHaarRawVector] using
            lpHaarDyadicCoefficient_const 𝕜 p i.1 i.2 1
      | some j =>
          rcases i with ⟨n, k⟩
          rcases j with ⟨m, l⟩
          by_cases h : n = m
          · subst m
            simpa [lpHaarRawCoordinate, lpHaarRawVector] using
              lpHaarDyadicCoefficient_apply_level 𝕜 p n k l
          · have hij : (⟨n, k⟩ : Σ n : ℕ, Fin (2 ^ n)) ≠ ⟨m, l⟩ :=
              fun heq => h (congrArg Sigma.fst heq)
            simpa [lpHaarRawCoordinate, lpHaarRawVector, hij] using
              lpHaarDyadicCoefficient_other_level 𝕜 p hp m n l k h

theorem lpHaarRawVector_norm_pos (hp : p.val ≠ ∞)
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) : 0 < ‖lpHaarRawVector 𝕜 p i‖ := by
  have hself := lpHaarRaw_biorthogonal 𝕜 p hp i i
  simp only [if_pos rfl] at hself
  apply norm_pos_iff.mpr
  intro hz
  rw [hz, map_zero] at hself
  exact zero_ne_one hself

def lpHaarNormalizedVector (i : Option (Σ n : ℕ, Fin (2 ^ n))) : IntervalLp 𝕜 p :=
  ((‖lpHaarRawVector 𝕜 p i‖ : ℝ) : 𝕜)⁻¹ • lpHaarRawVector 𝕜 p i

def lpHaarNormalizedCoordinate (i : Option (Σ n : ℕ, Fin (2 ^ n))) :
    IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
  ((‖lpHaarRawVector 𝕜 p i‖ : ℝ) : 𝕜) • lpHaarRawCoordinate 𝕜 p i

theorem lpHaarNormalizedVector_norm (hp : p.val ≠ ∞)
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) : ‖lpHaarNormalizedVector 𝕜 p i‖ = 1 := by
  rw [lpHaarNormalizedVector, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (lpHaarRawVector_norm_pos 𝕜 p hp i).ne']

theorem lpHaarNormalized_biorthogonal (hp : p.val ≠ ∞)
    (i j : Option (Σ n : ℕ, Fin (2 ^ n))) :
    lpHaarNormalizedCoordinate 𝕜 p i (lpHaarNormalizedVector 𝕜 p j) =
      if i = j then 1 else 0 := by
  simp only [lpHaarNormalizedCoordinate, lpHaarNormalizedVector,
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, lpHaarRaw_biorthogonal 𝕜 p hp]
  split_ifs with h
  · subst j
    have hn : ((‖lpHaarRawVector 𝕜 p i‖ : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (lpHaarRawVector_norm_pos 𝕜 p hp i).ne'
    simp [hn]
  · simp

theorem lpHaarNormalized_term (hp : p.val ≠ ∞)
    (i : Option (Σ n : ℕ, Fin (2 ^ n))) (f : IntervalLp 𝕜 p) :
    lpHaarNormalizedCoordinate 𝕜 p i f • lpHaarNormalizedVector 𝕜 p i =
      lpHaarRawCoordinate 𝕜 p i f • lpHaarRawVector 𝕜 p i := by
  have hn : ((‖lpHaarRawVector 𝕜 p i‖ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (lpHaarRawVector_norm_pos 𝕜 p hp i).ne'
  simp only [lpHaarNormalizedCoordinate, lpHaarNormalizedVector,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  field_simp

end ThesisCommon
