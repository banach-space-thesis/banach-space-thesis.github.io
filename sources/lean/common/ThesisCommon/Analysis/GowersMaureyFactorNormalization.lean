import ThesisCommon.Analysis.FiniteFactorNormalization
import ThesisCommon.Analysis.GowersMaureyInterpolationProfiles
import ThesisCommon.Analysis.GowersMaureyCoding

/-! The actual finite-factor reductions in Gowers--Maurey, arXiv
math/9205204, pp.16–17. Two ordinary factors merge by
submultiplicativity; three equal selected factors merge by the logarithmic
cube estimate. The constructed sizes automatically meet the numerical bound. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_cube_le {x : ℝ} (hx : 1 ≤ x) :
    logarithmicWeight (x ^ 3) ≤ 3 * logarithmicWeight x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have harg : x ^ 3 + 1 ≤ (x + 1) ^ 3 := by nlinarith [sq_nonneg x]
  have hlog := Real.log_le_log (by positivity : 0 < x ^ 3 + 1) harg
  rw [Real.log_pow] at hlog
  unfold logarithmicWeight
  calc
    _ ≤ (3 * Real.log (x + 1)) / Real.log 2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlog) (Real.log_nonneg (by norm_num))
    _ = _ := by ring

theorem logarithmicWeight_cube_le_sqrt_cube {x : ℝ} (hx : 1 ≤ x)
    (hlarge : 9 ≤ logarithmicWeight x) :
    logarithmicWeight (x ^ 3) ≤ (Real.sqrt (logarithmicWeight x)) ^ 3 := by
  have hf0 : 0 ≤ logarithmicWeight x := by linarith
  have hs : 3 ≤ Real.sqrt (logarithmicWeight x) := by
    have h := Real.sqrt_le_sqrt hlarge
    norm_num at h
    exact h
  calc
    _ ≤ 3 * logarithmicWeight x := logarithmicWeight_cube_le hx
    _ ≤ Real.sqrt (logarithmicWeight x) * logarithmicWeight x :=
      mul_le_mul_of_nonneg_right hs hf0
    _ = _ := by rw [pow_succ, Real.sq_sqrt hf0, mul_comm]

theorem interpolationSeed_mul_le_of_unselected
    (K : Set ℕ) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxK : x ∉ (fun k : ℕ => (k : ℝ)) '' K)
    (hyK : y ∉ (fun k : ℕ => (k : ℝ)) '' K) :
    interpolationSeed K (x * y) ≤ interpolationSeed K x * interpolationSeed K y := by
  have hxy : 1 ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  apply (interpolationSeed_bounds K hxy).2.trans
  simpa only [interpolationSeed, if_neg hxK, if_neg hyK] using
    logarithmicWeight_submultiplicative hx hy

theorem interpolationSeed_cube_le_of_selected
    (K : Set ℕ) {k : ℕ} (hk : k ∈ K) (hk1 : (1 : ℝ) ≤ k)
    (hlarge : 9 ≤ logarithmicWeight k) :
    interpolationSeed K ((k : ℝ) ^ 3) ≤ (interpolationSeed K k) ^ 3 := by
  apply (interpolationSeed_bounds K (one_le_pow₀ hk1)).2.trans
  simpa only [interpolationSeed, if_pos (show (k : ℝ) ∈ (fun j : ℕ => (j : ℝ)) '' K from
    ⟨k, hk, rfl⟩)] using logarithmicWeight_cube_le_sqrt_cube hk1 hlarge

theorem exists_normalized_interpolationSeed_factors
    (K : Set ℕ) (hK : ∀ k ∈ K, 9 ≤ logarithmicWeight k)
    (l : List ℝ) (hl : ∀ x ∈ l, 1 ≤ x) :
    ∃ m : List ℝ, (∀ x ∈ m, 1 ≤ x) ∧ m.prod = l.prod ∧
      (m.map (interpolationSeed K)).prod ≤ (l.map (interpolationSeed K)).prod ∧
      FactorListNormalized ((fun k : ℕ => (k : ℝ)) '' K) m := by
  apply exists_normalized_factorList _ _ (fun x hx => interpolationSeed_ge_one K hx)
    (fun x y hx hy hxK hyK => interpolationSeed_mul_le_of_unselected K hx.le hy.le hxK hyK)
    ?_ l hl
  rintro x ⟨k, hk, rfl⟩ hx
  exact interpolationSeed_cube_le_of_selected K hk hx (hK k hk)

theorem ConstructionData.specialSize_weight_large
    {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)
    {k : ℕ} (hk : k ∈ D.specialSizes) : 256 < logarithmicWeight k := by
  obtain ⟨n, rfl⟩ := hk
  apply D.first_large.trans_le
  apply logarithmicWeight_strictMonoOn.monotoneOn
  · change (1 : ℝ) ≤ D.j 0
    exact_mod_cast (Nat.succ_le_iff.mpr (D.j_positive 0))
  · change (1 : ℝ) ≤ D.j (2 * n)
    exact_mod_cast (Nat.succ_le_iff.mpr (D.j_positive (2 * n)))
  · exact_mod_cast D.j_strict.monotone (Nat.zero_le (2 * n))

theorem exists_normalized_interpolationSeed_factors_of_construction
    {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)
    (K : Set ℕ) (hK : K ⊆ D.specialSizes) (l : List ℝ) (hl : ∀ x ∈ l, 1 ≤ x) :
    ∃ m : List ℝ, (∀ x ∈ m, 1 ≤ x) ∧ m.prod = l.prod ∧
      (m.map (interpolationSeed K)).prod ≤ (l.map (interpolationSeed K)).prod ∧
      FactorListNormalized ((fun k : ℕ => (k : ℝ)) '' K) m := by
  apply exists_normalized_interpolationSeed_factors K ?_ l hl
  intro k hk
  have h := D.specialSize_weight_large (hK hk)
  linarith

end ThesisCommon.GowersMaurey
