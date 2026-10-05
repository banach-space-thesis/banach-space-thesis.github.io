import ThesisCommon.Analysis.GowersMaureyLaurentOperators
import ThesisCommon.Analysis.GowersMaureySpreadProperness

/-! Quantitative propagation of a right-shift approximate eigenvector to
every integer shift. The unilateral left inverse is used explicitly. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem completedSpread_composition (D : ConstructionData 𝕜) (m n p q : ℕ) :
    (completedSpread D m n).comp (completedSpread D p q) =
      completedSpread D (p+(m-q)) (n+(q-m)) := by
  apply ContinuousLinearMap.ext
  intro x
  change completedSpread D m n (completedSpread D p q x) = _
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_eq ((completedSpread D m n).continuous.comp
      (completedSpread D p q).continuous) (completedSpread D _ _).continuous
  · intro y
    simp only [completedSpread_denseEmbedding]
    apply congrArg (denseEmbedding D)
    exact DFunLike.congr_fun (spread_comp m n p q) y

theorem completedSpread_zero_zero (D : ConstructionData 𝕜) :
    completedSpread D 0 0 = ContinuousLinearMap.id 𝕜 (ShiftSpace D) := by
  have hh := completedSpread_left_right D 0
  have he := completedSpread_composition D 0 0 0 0
  simpa using he.symm.trans hh

theorem completedRightShift_pow (D : ConstructionData 𝕜) (n : ℕ) :
    (completedSpread D 0 1)^n = completedSpread D 0 n := by
  induction n with
  | zero => simpa using (completedSpread_zero_zero D).symm
  | succ n ih =>
    rw [pow_succ', ih]
    change (completedSpread D 0 1).comp (completedSpread D 0 n) = _
    simpa [Nat.add_comm] using completedSpread_composition D 0 1 0 n

theorem completedLeftShift_pow (D : ConstructionData 𝕜) (n : ℕ) :
    (completedSpread D 1 0)^n = completedSpread D n 0 := by
  induction n with
  | zero => simpa using (completedSpread_zero_zero D).symm
  | succ n ih =>
    rw [pow_succ', ih]
    change (completedSpread D 1 0).comp (completedSpread D n 0) = _
    simpa using completedSpread_composition D 1 0 n 0

theorem contraction_power_eigen_error_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (U : X →L[𝕜] X) (hU : ∀ x, ‖U x‖ ≤ ‖x‖)
    {z : 𝕜} (hz : ‖z‖ = 1) (x : X) (n : ℕ) :
    ‖(U^n) x-z^n • x‖ ≤ (n : ℝ) * ‖U x-z • x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (U^(n+1)) x-z^(n+1) • x =
        U ((U^n) x-z^n • x)+z^n • (U x-z • x) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply, map_sub, map_smul,
        smul_sub, smul_smul, pow_succ]
      abel
    rw [he]
    calc
      _ ≤ ‖U ((U^n) x-z^n • x)‖+‖z^n • (U x-z • x)‖ := norm_add_le _ _
      _ ≤ ‖(U^n) x-z^n • x‖+‖U x-z • x‖ := by
        simpa only [norm_smul, norm_pow, hz, one_pow, one_mul] using
          add_le_add_right (hU ((U^n) x-z^n • x)) ‖z^n • (U x-z • x)‖
      _ ≤ (n : ℝ)*‖U x-z • x‖+‖U x-z • x‖ := add_le_add_right ih _
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

theorem completedLeftShift_eigen_error_le (D : ConstructionData 𝕜)
    {z : 𝕜} (hz : ‖z‖ = 1) (x : ShiftSpace D) :
    ‖completedSpread D 1 0 x-z⁻¹ • x‖ ≤ ‖completedSpread D 0 1 x-z • x‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hid := DFunLike.congr_fun (completedSpread_left_right D 1) x
  change completedSpread D 1 0 (completedSpread D 0 1 x) = x at hid
  have he : completedSpread D 1 0 x-z⁻¹ • x =
      -z⁻¹ • completedSpread D 1 0 (completedSpread D 0 1 x-z • x) := by
    rw [map_sub, hid, map_smul, smul_sub, smul_smul]
    have hz' : -z⁻¹*z = -1 := by rw [neg_mul, inv_mul_cancel₀ hz0]
    rw [hz', neg_one_smul, neg_smul]
    abel
  rw [he, norm_smul, norm_neg, norm_inv, hz, inv_one, one_mul]
  exact completedSpread_norm_le D 1 0 _

theorem integerShift_eigen_error_le (D : ConstructionData 𝕜)
    {z : 𝕜} (hz : ‖z‖ = 1) (x : ShiftSpace D) (d : ℤ) :
    ‖integerShift D d x-z^d • x‖ ≤ (d.natAbs : ℝ) *
      ‖completedSpread D 0 1 x-z • x‖ := by
  cases d with
  | ofNat n =>
    have hh := contraction_power_eigen_error_le (completedSpread D 0 1)
      (completedSpread_norm_le D 0 1) hz x n
    rw [completedRightShift_pow] at hh
    simpa only [integerShift, Int.ofNat_eq_coe, zpow_natCast, Int.natAbs_natCast] using hh
  | negSucc n =>
    have hz' : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
    have hh := contraction_power_eigen_error_le (completedSpread D 1 0)
      (completedSpread_norm_le D 1 0) hz' x (n+1)
    rw [completedLeftShift_pow] at hh
    have hm := mul_le_mul_of_nonneg_left (completedLeftShift_eigen_error_le D hz x)
      (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)
    simpa only [integerShift, Int.natAbs_negSucc, zpow_negSucc, inv_pow] using hh.trans hm

end ThesisCommon.GowersMaurey
