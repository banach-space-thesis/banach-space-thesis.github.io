import ThesisCommon.Analysis.GowersMaureyInterpolationBarriers
import ThesisCommon.Analysis.ConcaveReciprocalMonotone
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The six numerical-profile requirements in Gowers--Maurey, printed
pp. 1--2, are verified for the actual interpolation construction. The
right derivative is obtained from genuine concavity and bounded by the
checked square-root-logarithmic support line. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey

structure IsNumericalProfile (g : ℝ → ℝ) : Prop where
  ge_one : ∀ x, 1 ≤ x → 1 ≤ g x
  one : g 1 = 1
  lt_self : ∀ x, 1 < x → g x < x
  strictMonoOn : StrictMonoOn g (Set.Ici 1)
  tendsto_atTop : Tendsto g atTop atTop
  subpower : ∀ q : ℝ, 0 < q → Tendsto (fun x : ℝ => g x / x^q) atTop (𝓝 0)
  reciprocal_concaveOn : ConcaveOn ℝ (Set.Ici 1) (fun x => x / g x)
  reciprocal_monotoneOn : MonotoneOn (fun x => x / g x) (Set.Ici 1)
  submultiplicative : ∀ x y, 1 ≤ x → 1 ≤ y → g (x*y) ≤ g x * g y
  positive_right_derivative : ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt g d (Set.Ioi 1) 1

theorem interpolationG_one (K : Set ℕ) : interpolationG K 1 = 1 :=
  interpolationG_small K zero_le_one le_rfl

theorem interpolationG_pos (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) : 0 < interpolationG K x :=
  concavifiedReciprocal_pos (fun _ ht => interpolationSeed_ge_one K ht)
    (interpolationSeed_one K).le hx

theorem interpolationG_lt_self (K : Set ℕ) {x : ℝ} (hx : 1 < x) : interpolationG K x < x := by
  have hh := interpolationG_support K hx.le
  have hpos : 0 < 1 / (4 * Real.log 2) := by positivity
  nlinarith [mul_pos hpos (sub_pos.mpr hx)]

theorem interpolationProfile_ge_one (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ interpolationProfile K x :=
  (one_le_sqrt_logarithmicWeight hx).trans (interpolationProfile_ge_sqrt K hx)

theorem interpolationProfile_one (K : Set ℕ) : interpolationProfile K 1 = 1 := by
  change 1 / interpolationG K 1 = 1
  rw [interpolationG_one]
  norm_num

theorem interpolationProfile_lt_self (K : Set ℕ) {x : ℝ} (hx : 1 < x) :
    interpolationProfile K x < x :=
  (interpolationProfile_le_weight K hx.le).trans_lt (logarithmicWeight_lt_self hx)

theorem interpolationProfile_strictMonoOn (K : Set ℕ) :
    StrictMonoOn (interpolationProfile K) (Set.Ici 1) := by
  change StrictMonoOn (fun x => x / interpolationG K x) (Set.Ici 1)
  exact strictMonoOn_div_concave_of_lt_identity
    ((interpolationG_concaveOn K).subset (Set.Ici_subset_Ici.mpr zero_le_one) (convex_Ici 1))
    (interpolationG_one K) (fun _ hx => interpolationG_pos K hx)
    (fun _ hx => interpolationG_lt_self K hx)

theorem tendsto_interpolationProfile_atTop (K : Set ℕ) :
    Tendsto (interpolationProfile K) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have he := tendsto_logarithmicWeight_atTop.eventually
    (eventually_ge_atTop ((max b 0)^2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with x hx hfx
  have hr : max b 0 ≤ Real.sqrt (logarithmicWeight x) :=
    (Real.le_sqrt (le_max_right b 0) ((sq_nonneg (max b 0)).trans hfx)).mpr hfx
  exact (le_max_left b 0).trans (hr.trans (interpolationProfile_ge_sqrt K hx))

theorem tendsto_interpolationProfile_div_rpow (K : Set ℕ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => interpolationProfile K x / x^q) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_logarithmicWeight_div_rpow hq)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (zero_le_one.trans (interpolationProfile_ge_one K hx))
      (Real.rpow_nonneg (zero_le_one.trans hx) q)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (interpolationProfile_le_weight K hx)
      (Real.rpow_nonneg (zero_le_one.trans hx) q)

theorem interpolationProfile_reciprocal (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    x / interpolationProfile K x = interpolationG K x := by
  simpa only [div_eq_mul_inv, mul_comm] using interpolationProfile_inverse_mul K hx

theorem interpolationProfile_reciprocal_concaveOn (K : Set ℕ) :
    ConcaveOn ℝ (Set.Ici 1) (fun x => x / interpolationProfile K x) := by
  apply ((interpolationG_concaveOn K).subset
    (Set.Ici_subset_Ici.mpr zero_le_one) (convex_Ici 1)).congr
  intro x hx
  exact (interpolationProfile_reciprocal K hx).symm

theorem interpolationProfile_reciprocal_monotoneOn (K : Set ℕ) :
    MonotoneOn (fun x => x / interpolationProfile K x) (Set.Ici 1) := by
  intro x hx y hy hxy
  change x / interpolationProfile K x ≤ y / interpolationProfile K y
  rw [interpolationProfile_reciprocal K hx, interpolationProfile_reciprocal K hy]
  have hx0 : x ∈ Set.Ici (0 : ℝ) := zero_le_one.trans (show 1 ≤ x from hx)
  have hy0 : y ∈ Set.Ici (0 : ℝ) := zero_le_one.trans (show 1 ≤ y from hy)
  exact interpolationG_monotoneOn K hx0 hy0 hxy

theorem interpolationProfile_right_derivative (K : Set ℕ) :
    ∃ d : ℝ, 1 / (4 * Real.log 2) ≤ d ∧
      HasDerivWithinAt (interpolationProfile K) d (Set.Ioi 1) 1 := by
  let dG := -derivWithin (fun x => -interpolationG K x) (Set.Ioi 1) 1
  have hdNeg := (interpolationG_concaveOn K).neg.hasDerivWithinAt_rightDeriv_of_mem_interior
    (by simp only [interior_Ici, Set.mem_Ioi]; norm_num : (1 : ℝ) ∈ interior (Set.Ici 0))
  have hdG : HasDerivWithinAt (interpolationG K) dG (Set.Ioi 1) 1 := by
    simpa only [Pi.neg_apply, neg_neg] using hdNeg.neg
  have ht := (hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (1 : ℝ) ∉ Set.Ioi 1)).mp hdG
  have hupper : dG ≤ 1 - 1 / (4 * Real.log 2) := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field, interpolationG_one]
    apply (div_le_iff₀ (sub_pos.mpr hx)).mpr
    have hh := interpolationG_support K hx.le
    linarith
  refine ⟨1 - dG, by linarith, ?_⟩
  convert (hasDerivAt_id (1 : ℝ)).hasDerivWithinAt.div hdG
    (by rw [interpolationG_one]; norm_num) using 1
  simp only [interpolationG_one, id_eq, one_mul, mul_one, one_pow, div_one]

theorem interpolationProfile_isNumericalProfile (K : Set ℕ) :
    IsNumericalProfile (interpolationProfile K) where
  ge_one := fun _ hx => interpolationProfile_ge_one K hx
  one := interpolationProfile_one K
  lt_self := fun _ hx => interpolationProfile_lt_self K hx
  strictMonoOn := interpolationProfile_strictMonoOn K
  tendsto_atTop := tendsto_interpolationProfile_atTop K
  subpower := fun _ hq => tendsto_interpolationProfile_div_rpow K hq
  reciprocal_concaveOn := interpolationProfile_reciprocal_concaveOn K
  reciprocal_monotoneOn := interpolationProfile_reciprocal_monotoneOn K
  submultiplicative := fun _ _ hx hy => interpolationProfile_submultiplicative K hx hy
  positive_right_derivative := by
    obtain ⟨d, hd, hderiv⟩ := interpolationProfile_right_derivative K
    exact ⟨d, (show 0 < 1 / (4 * Real.log 2) by positivity).trans_le hd, hderiv⟩

end ThesisCommon.GowersMaurey
