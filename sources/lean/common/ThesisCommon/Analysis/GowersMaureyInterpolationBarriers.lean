import ThesisCommon.Analysis.GowersMaureyInterpolationProfiles
import ThesisCommon.Analysis.GowersMaureyLogProfileCalculus

/-! The actual square-root-logarithmic lower barrier for the constructed
interpolation profiles. The generic hull lemmas and the checked calculus
discharge all barrier assumptions. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem sqrt_logarithmicWeight_monotoneOn :
    MonotoneOn (fun x => Real.sqrt (logarithmicWeight x)) (Set.Ici 1) := by
  intro x hx y hy hxy
  exact Real.sqrt_le_sqrt (logarithmicWeight_strictMonoOn.monotoneOn hx hy hxy)

theorem extended_sqrtLogarithmicProfile_concaveOn :
    ConcaveOn ℝ (Set.Ici 0) (extendedReciprocalProfile (fun x => Real.sqrt (logarithmicWeight x))) :=
  extendedReciprocalProfile_concaveOn (fun _ hx => one_le_sqrt_logarithmicWeight hx)
    (by simp [logarithmicWeight_one]) sqrtLogarithmicProfile_concaveOn

theorem interpolationG_le_extended_sqrtLogarithmicProfile (K : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    interpolationG K x ≤ extendedReciprocalProfile (fun t => Real.sqrt (logarithmicWeight t)) x :=
  concavifiedReciprocal_le_barrier (fun _ ht => interpolationSeed_ge_one K ht)
    (fun _ ht => one_le_sqrt_logarithmicWeight ht) (by simp [logarithmicWeight_one])
    sqrt_logarithmicWeight_monotoneOn (fun _ _ hx hy => sqrt_logarithmicWeight_submultiplicative hx hy)
    (fun _ ht => (interpolationSeed_bounds K ht).1) extended_sqrtLogarithmicProfile_concaveOn hx

theorem interpolationProfile_ge_sqrt (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (logarithmicWeight x) ≤ interpolationProfile K x :=
  barrier_le_regularizedProfile (fun _ ht => interpolationSeed_ge_one K ht) (interpolationSeed_one K).le
    (fun _ ht => one_le_sqrt_logarithmicWeight ht) (by simp [logarithmicWeight_one])
    sqrt_logarithmicWeight_monotoneOn (fun _ _ hx hy => sqrt_logarithmicWeight_submultiplicative hx hy)
    (fun _ ht => (interpolationSeed_bounds K ht).1) extended_sqrtLogarithmicProfile_concaveOn hx

theorem interpolationProfile_at_selected_size (K : Set ℕ) {k : ℕ} (hk : 0 < k) (hK : k ∈ K) :
    interpolationProfile K k = Real.sqrt (logarithmicWeight k) :=
  le_antisymm (interpolationProfile_le_sqrt_at_selected_size K hk hK)
    (interpolationProfile_ge_sqrt K (by exact_mod_cast hk))

theorem interpolationProfile_submultiplicative (K : Set ℕ) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    interpolationProfile K (x * y) ≤ interpolationProfile K x * interpolationProfile K y :=
  regularizedProfile_mul_le (fun _ ht => interpolationSeed_ge_one K ht) (interpolationSeed_one K).le hx hy

theorem interpolationG_support (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    interpolationG K x ≤ 1 + (1 - 1 / (4 * Real.log 2)) * (x - 1) := by
  have hh := interpolationG_le_extended_sqrtLogarithmicProfile K (zero_le_one.trans hx)
  rw [extendedReciprocalProfile_of_one_le (by simp [logarithmicWeight_one]) hx] at hh
  exact hh.trans (sqrtLogarithmicProfile_support hx)

theorem interpolation_support_slope_nonneg : 0 ≤ 1 - 1 / (4 * Real.log 2) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hpos : 0 < 4 * Real.log 2 := by positivity
  have hh : 1 / (4 * Real.log 2) ≤ 1 := (div_le_one hpos).mpr (by linarith)
  linarith

end ThesisCommon.GowersMaurey
