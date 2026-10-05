import ThesisCommon.Analysis.GowersMaureyNumericalProfiles
import ThesisCommon.Analysis.GowersMaureyLogTangent

/-! The two standard members of the source numerical class, with their
positive right derivatives calculated rather than assumed. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_hasDerivAt_one :
    HasDerivAt logarithmicWeight (1 / (2 * Real.log 2)) 1 := by
  simpa only [logarithmicWeight, id_eq, one_add_one_eq_two, div_div] using
    (((hasDerivAt_id (1 : ℝ)).add_const 1).log (by norm_num)).div_const (Real.log 2)

theorem sqrt_logarithmicWeight_hasDerivAt_one :
    HasDerivAt (fun x => Real.sqrt (logarithmicWeight x)) (1 / (4 * Real.log 2)) 1 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  convert logarithmicWeight_hasDerivAt_one.sqrt (by rw [logarithmicWeight_one]; norm_num) using 1
  simp only [logarithmicWeight_one, Real.sqrt_one]
  field_simp [hL.ne']
  norm_num

theorem tendsto_sqrt_logarithmicWeight_atTop :
    Tendsto (fun x => Real.sqrt (logarithmicWeight x)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have he := tendsto_logarithmicWeight_atTop.eventually
    (eventually_ge_atTop ((max b 0)^2))
  filter_upwards [he] with x hfx
  exact (le_max_left b 0).trans
    ((Real.le_sqrt (le_max_right b 0) ((sq_nonneg (max b 0)).trans hfx)).mpr hfx)

theorem tendsto_sqrt_logarithmicWeight_div_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.sqrt (logarithmicWeight x) / x^q) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_logarithmicWeight_div_rpow hq)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx) q)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (sqrt_logarithmicWeight_le_weight hx)
      (Real.rpow_nonneg (zero_le_one.trans hx) q)

theorem logarithmicWeight_isNumericalProfile : IsNumericalProfile logarithmicWeight where
  ge_one := fun _ hx => one_le_logarithmicWeight_real hx
  one := logarithmicWeight_one
  lt_self := fun _ hx => logarithmicWeight_lt_self hx
  strictMonoOn := logarithmicWeight_strictMonoOn
  tendsto_atTop := tendsto_logarithmicWeight_atTop
  subpower := fun _ hq => tendsto_logarithmicWeight_div_rpow hq
  reciprocal_concaveOn := logarithmicProfile_concaveOn
  reciprocal_monotoneOn := logarithmicProfile_monotoneOn
  submultiplicative := fun _ _ hx hy => logarithmicWeight_submultiplicative hx hy
  positive_right_derivative :=
    ⟨1 / (2 * Real.log 2), by positivity, logarithmicWeight_hasDerivAt_one.hasDerivWithinAt⟩

theorem sqrt_logarithmicWeight_isNumericalProfile :
    IsNumericalProfile (fun x => Real.sqrt (logarithmicWeight x)) where
  ge_one := fun _ hx => one_le_sqrt_logarithmicWeight hx
  one := by rw [logarithmicWeight_one, Real.sqrt_one]
  lt_self := fun _ hx => (sqrt_logarithmicWeight_le_weight hx.le).trans_lt
    (logarithmicWeight_lt_self hx)
  strictMonoOn := by
    intro x hx y hy hxy
    exact Real.sqrt_lt_sqrt (zero_le_one.trans (one_le_logarithmicWeight_real hx))
      (logarithmicWeight_strictMonoOn hx hy hxy)
  tendsto_atTop := tendsto_sqrt_logarithmicWeight_atTop
  subpower := fun _ hq => tendsto_sqrt_logarithmicWeight_div_rpow hq
  reciprocal_concaveOn := sqrtLogarithmicProfile_concaveOn
  reciprocal_monotoneOn := sqrtLogarithmicProfile_monotoneOn
  submultiplicative := fun _ _ hx hy => sqrt_logarithmicWeight_submultiplicative hx hy
  positive_right_derivative :=
    ⟨1 / (4 * Real.log 2), by positivity, sqrt_logarithmicWeight_hasDerivAt_one.hasDerivWithinAt⟩

end ThesisCommon.GowersMaurey
