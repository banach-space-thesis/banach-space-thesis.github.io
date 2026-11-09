import SurveyStatements.P5Support.LpHaarStepDensity
import SurveyStatements.P5Support.LpHaarDyadicRefinement

/-! Normalized indicators and actual Haar differences used to test an L¹
multiplier along a dyadic branch. These lemmas use the concrete interval
vectors and do not assume a multiplier variation theorem. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

abbrev IntervalL1 (𝕜 : Type*) [RCLike 𝕜] := IntervalLp 𝕜 ⟨1, le_rfl⟩

def cellDensity (𝕜 : Type*) [RCLike 𝕜] (n k : ℕ) : IntervalL1 𝕜 :=
  (2 : 𝕜) ^ n • lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k

theorem cellDensity_coe (𝕜 : Type*) [RCLike 𝕜] (n k : ℕ) :
    cellDensity 𝕜 n k =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (lpHaarCell n k).indicator (fun _ => (2 : 𝕜) ^ n) := by
  filter_upwards [Lp.coeFn_smul ((2 : 𝕜) ^ n)
      (lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k),
    (indicatorConstLp_coeFn (p := (1 : ℝ≥0∞))
      (hs := (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc))
      (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _)
      (c := (1 : 𝕜)))] with x h₁ h₂
  change cellDensity 𝕜 n k x = _ at h₁
  change lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k x = _ at h₂
  rw [h₁]
  simp only [Pi.smul_apply, smul_eq_mul, h₂]
  by_cases hx : x ∈ lpHaarCell n k <;> simp [hx]

theorem cellDensity_norm (𝕜 : Type*) [RCLike 𝕜]
    (n k : ℕ) (hk : k < 2 ^ n) : ‖cellDensity 𝕜 n k‖ = 1 := by
  have hv : ‖lpHaarCellVector 𝕜 ⟨1, le_rfl⟩ n k‖ = intervalLpDyadicRadius n := by
    change ‖indicatorConstLp (1 : ℝ≥0∞) measurableSet_Ioc
      (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (1 : 𝕜)‖ = _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    change ‖(1 : 𝕜)‖ * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarCell n k) ^
      (1 / (1 : ℝ≥0∞).toReal) = _
    rw [measureReal_def, lpHaarCell_measure n k hk]
    simp [ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  rw [cellDensity, norm_smul, hv, norm_pow]
  have ht : ‖(2 : 𝕜)‖ = 2 := by norm_num
  rw [ht]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using lpHaarRadius_cancel n

theorem cellDensity_difference_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (n k m j : ℕ) (hk : k < 2 ^ n) (hj : j < 2 ^ m) :
    ‖cellDensity 𝕜 n k - cellDensity 𝕜 m j‖ ≤ 2 := by
  calc
    _ ≤ ‖cellDensity 𝕜 n k‖ + ‖cellDensity 𝕜 m j‖ := norm_sub_le _ _
    _ = 2 := by rw [cellDensity_norm 𝕜 n k hk, cellDensity_norm 𝕜 m j hj]; norm_num

theorem cellDensity_left_difference (𝕜 : Type*) [RCLike 𝕜] (n k : ℕ) :
    cellDensity 𝕜 (n + 1) (2 * k) - cellDensity 𝕜 n k =
      (2 : 𝕜) ^ n • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (cellDensity 𝕜 (n + 1) (2 * k)) (cellDensity 𝕜 n k),
    cellDensity_coe 𝕜 (n + 1) (2 * k), cellDensity_coe 𝕜 n k,
    Lp.coeFn_smul ((2 : 𝕜) ^ n) (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k),
    (lpHaarVector_coe (𝕜 := 𝕜) (p := (1 : ℝ≥0∞))
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
      measurableSet_Ioc measurableSet_Ioc)] with x hsub hl hp hsmul hhaar
  change lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k x = _ at hhaar
  rw [hsub, hsmul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hl, hp, hhaar, ← lpHaarCell_children n k]
  have hd := Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel (n + 1)
    (show 2 * k ≠ 2 * k + 1 by omega))
  by_cases hL : x ∈ lpHaarCell (n + 1) (2 * k)
  · have hR : x ∉ lpHaarCell (n + 1) (2 * k + 1) := fun h => hd hL h
    simp [lpHaarFunction, hL, hR, pow_succ]
    ring
  · by_cases hR : x ∈ lpHaarCell (n + 1) (2 * k + 1) <;>
      simp [lpHaarFunction, hL, hR, pow_succ]

theorem cellDensity_right_difference (𝕜 : Type*) [RCLike 𝕜] (n k : ℕ) :
    cellDensity 𝕜 (n + 1) (2 * k + 1) - cellDensity 𝕜 n k =
      -(2 : 𝕜) ^ n • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (cellDensity 𝕜 (n + 1) (2 * k + 1)) (cellDensity 𝕜 n k),
    cellDensity_coe 𝕜 (n + 1) (2 * k + 1), cellDensity_coe 𝕜 n k,
    Lp.coeFn_smul (-(2 : 𝕜) ^ n) (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k),
    (lpHaarVector_coe (𝕜 := 𝕜) (p := (1 : ℝ≥0∞))
      (μ := volume.restrict (Icc (0 : ℝ) 1))
      (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
      measurableSet_Ioc measurableSet_Ioc)] with x hsub hr hp hsmul hhaar
  change lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k x = _ at hhaar
  rw [hsub, hsmul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hr, hp, hhaar, ← lpHaarCell_children n k]
  have hd := Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel (n + 1)
    (show 2 * k ≠ 2 * k + 1 by omega))
  by_cases hL : x ∈ lpHaarCell (n + 1) (2 * k)
  · have hR : x ∉ lpHaarCell (n + 1) (2 * k + 1) := fun h => hd hL h
    simp [lpHaarFunction, hL, hR, pow_succ]
  · by_cases hR : x ∈ lpHaarCell (n + 1) (2 * k + 1)
    · simp [lpHaarFunction, hL, hR, pow_succ]
      ring
    · simp [lpHaarFunction, hL, hR, pow_succ]

theorem cellDensity_multiplier_difference (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)), D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k •
      lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (n : ℕ) (k : Fin (2 ^ n)) (j : Fin (2 ^ (n + 1)))
    (hj : lpHaarParentIndex n j = k) :
    D (cellDensity 𝕜 (n + 1) j - cellDensity 𝕜 n k) =
      d n k • (cellDensity 𝕜 (n + 1) j - cellDensity 𝕜 n k) := by
  have hval : j.val / 2 = k.val := congrArg Fin.val hj
  have hchild : j.val = 2 * k.val ∨ j.val = 2 * k.val + 1 := by omega
  rcases hchild with h | h
  · rw [h, cellDensity_left_difference, map_smul, hD]
    exact smul_comm _ _ _
  · rw [h, cellDensity_right_difference, map_smul, hD]
    exact smul_comm _ _ _

end SurveyStatements.P5L1Variation
