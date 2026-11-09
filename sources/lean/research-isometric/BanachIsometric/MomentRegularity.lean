import BanachIsometric.Covariance
import BanachIsometric.StarBody
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# Quantitative regularity of normalised moments

We first bound changes of normalised integrals by the measure of the symmetric
difference of their domains. This applies to scalar, tensor, and operator-valued
moments. The geometric estimates below use radial inclusions and homothety
volume scaling, an alternative to the paper's polar-coordinate formula.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped ENNReal NNReal symmDiff Pointwise

section IntegralBounds

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded integrand changes by at most its bound times the measure of the
symmetric difference. -/
theorem norm_setIntegral_sub_le_symmDiff (μ : Measure α) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hfin : μ (S ∪ T) < ∞)
    {f : α → F} (hfS : IntegrableOn f S μ) (hfT : IntegrableOn f T μ)
    {B : ℝ} (hB : ∀ x ∈ S ∪ T, ‖f x‖ ≤ B) :
    ‖(∫ x in S, f x ∂μ) - ∫ x in T, f x ∂μ‖ ≤ B * μ.real (S ∆ T) := by
  have hSfin : μ (S \ T) < ∞ :=
    (measure_mono (diff_subset.trans subset_union_left)).trans_lt hfin
  have hTfin : μ (T \ S) < ∞ :=
    (measure_mono (diff_subset.trans subset_union_right)).trans_lt hfin
  have hsplitS := integral_inter_add_diff hT hfS
  have hsplitT := integral_inter_add_diff hS hfT
  have heq : (∫ x in S, f x ∂μ) - ∫ x in T, f x ∂μ =
      (∫ x in S \ T, f x ∂μ) - ∫ x in T \ S, f x ∂μ := by
    rw [← hsplitS, ← hsplitT, inter_comm T S]
    abel
  have hsum : μ.real (S \ T) + μ.real (T \ S) = μ.real (S ∆ T) := by
    simp only [measureReal_def, measure_symmDiff_eq hS.nullMeasurableSet hT.nullMeasurableSet,
      ENNReal.toReal_add hSfin.ne hTfin.ne]
  rw [heq]
  calc
    _ ≤ ‖∫ x in S \ T, f x ∂μ‖ + ‖∫ x in T \ S, f x ∂μ‖ := norm_sub_le _ _
    _ ≤ B * μ.real (S \ T) + B * μ.real (T \ S) := by
      exact add_le_add
        (norm_setIntegral_le_of_norm_le_const hSfin (fun x hx ↦ hB x (Or.inl hx.1)))
        (norm_setIntegral_le_of_norm_le_const hTfin (fun x hx ↦ hB x (Or.inr hx.1)))
    _ = B * μ.real (S ∆ T) := by rw [← mul_add, hsum]

/-- The algebraic normalisation estimate. Only the two domain masses enter;
an upper bound on the masses is unnecessary. -/
theorem norm_normalized_sub_le {A C : F} {a b m B δ : ℝ}
    (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hdiff : ‖A - C‖ ≤ B * δ) (hC : ‖C‖ ≤ B * b) (hmass : |a - b| ≤ δ) :
    ‖a⁻¹ • A - b⁻¹ • C‖ ≤ (2 * B / m) * δ := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have hinv : |a⁻¹ - b⁻¹| = |a - b| / (a * b) := by
    simpa only [Real.dist_eq, Real.norm_eq_abs, abs_of_pos ha0, abs_of_pos hb0] using
      (dist_inv_inv₀ ha0.ne' hb0.ne')
  have hid : a⁻¹ • A - b⁻¹ • C = a⁻¹ • (A - C) + (a⁻¹ - b⁻¹) • C := by
    rw [smul_sub, sub_smul]
    abel
  rw [hid]
  calc
    _ ≤ ‖a⁻¹ • (A - C)‖ + ‖(a⁻¹ - b⁻¹) • C‖ := norm_add_le _ _
    _ = a⁻¹ * ‖A - C‖ + (|a - b| / (a * b)) * ‖C‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr ha0), hinv]
    _ ≤ a⁻¹ * (B * δ) + (δ / (a * b)) * (B * b) := by
      refine add_le_add (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ha0.le)) ?_
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hmass (mul_pos ha0 hb0).le
      · exact hC
      · exact norm_nonneg _
      · exact div_nonneg hδ (mul_pos ha0 hb0).le
    _ = (2 * B * δ) / a := by field_simp; ring
    _ ≤ (2 * B * δ) / m :=
      div_le_div_of_nonneg_left (by positivity) hm ha
    _ = (2 * B / m) * δ := by ring

/-- Uniform lower bounds on domain masses turn symmetric-difference estimates
into estimates for normalised moments. -/
theorem norm_setAverage_sub_le_symmDiff (μ : Measure α) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hfin : μ (S ∪ T) < ∞)
    {f : α → F} (hfS : IntegrableOn f S μ) (hfT : IntegrableOn f T μ)
    {B m : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ S ∪ T, ‖f x‖ ≤ B)
    (hm : 0 < m) (hSm : m ≤ μ.real S) (hTm : m ≤ μ.real T) :
    ‖(⨍ x in S, f x ∂μ) - ⨍ x in T, f x ∂μ‖ ≤
      (2 * B / m) * μ.real (S ∆ T) := by
  have hSfin : μ S < ∞ := (measure_mono subset_union_left).trans_lt hfin
  have hTfin : μ T < ∞ := (measure_mono subset_union_right).trans_lt hfin
  rw [setAverage_eq, setAverage_eq]
  apply norm_normalized_sub_le hm hSm hTm hB0 measureReal_nonneg
  · exact norm_setIntegral_sub_le_symmDiff μ hS hT hfin hfS hfT hB
  · exact norm_setIntegral_le_of_norm_le_const hTfin (fun x hx ↦ hB x (Or.inr hx))
  · exact abs_measureReal_sub_le_measureReal_symmDiff'
      hS.nullMeasurableSet hT.nullMeasurableSet hSfin.ne hTfin.ne

end IntegralBounds

section RadialGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A radial set specified by its radii on the auxiliary unit sphere. Values
off the sphere are irrelevant. The origin is included even in dimension zero. -/
def radialBody (ρ : V → ℝ) : Set V :=
  {x | x = 0 ∨ ∃ (u : V) (t : ℝ), ‖u‖ = 1 ∧ 0 ≤ t ∧ t ≤ ρ u ∧ x = t • u}

theorem zero_mem_radialBody (ρ : V → ℝ) : (0 : V) ∈ radialBody ρ := Or.inl rfl

theorem IsDefinitePositiveHomogeneous.sublevel_eq_radialBody {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) :
    {x : V | p x ≤ 1} = radialBody (reciprocalRadial p) := hp.sublevel_eq_radial

theorem radialBody_mono {ρ σ : V → ℝ}
    (h : ∀ u : V, ‖u‖ = 1 → ρ u ≤ σ u) : radialBody ρ ⊆ radialBody σ := by
  rintro x (rfl | ⟨u, t, hu, ht, htr, rfl⟩)
  · exact zero_mem_radialBody σ
  · exact Or.inr ⟨u, t, hu, ht, htr.trans (h u hu), rfl⟩

theorem smul_radialBody_subset {ρ : V → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    a • radialBody ρ ⊆ radialBody (fun u ↦ a * ρ u) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_smul_set.mp hz
  rcases hx with rfl | ⟨u, t, hu, ht, htr, rfl⟩
  · simpa only [smul_zero] using zero_mem_radialBody (fun u ↦ a * ρ u)
  · exact Or.inr ⟨u, a * t, hu, mul_nonneg ha ht,
      mul_le_mul_of_nonneg_left htr ha, smul_smul a t u⟩

theorem radialBody_subset_smul {ρ : V → ℝ} {a : ℝ} (ha : 0 < a) :
    radialBody (fun u ↦ a * ρ u) ⊆ a • radialBody ρ := by
  rintro x (rfl | ⟨u, t, hu, ht, htr, rfl⟩)
  · exact mem_smul_set.mpr ⟨0, zero_mem_radialBody ρ, smul_zero a⟩
  · apply mem_smul_set.mpr
    have hta : t / a ≤ ρ u := (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using htr)
    have hsc : a * (t / a) = t := by
      simpa only [mul_comm] using div_mul_cancel₀ t ha.ne'
    refine ⟨(t / a) • u, Or.inr ⟨u, t / a, hu, div_nonneg ht ha.le, hta, rfl⟩, ?_⟩
    rw [smul_smul, hsc]

theorem radialBody_contracts {ρ : V → ℝ}
    (hρ : ∀ u : V, ‖u‖ = 1 → 0 ≤ ρ u) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a • radialBody ρ ⊆ radialBody ρ := by
  apply smul_radialBody_subset ha |>.trans
  apply radialBody_mono
  intro u hu
  nlinarith [hρ u hu]

theorem radialBody_expands {ρ : V → ℝ}
    (hρ : ∀ u : V, ‖u‖ = 1 → 0 ≤ ρ u) {a : ℝ} (ha : 1 ≤ a) :
    radialBody ρ ⊆ a • radialBody ρ := by
  apply (radialBody_mono (ρ := ρ) (σ := fun u ↦ a * ρ u) ?_).trans
    (radialBody_subset_smul (lt_of_lt_of_le zero_lt_one ha))
  intro u hu
  nlinarith [hρ u hu]

/-- Uniformly close positive radii give a homothety sandwich. This uses only
the common positive inner radius; no convexity or symmetry is needed. -/
theorem radialBody_homothety_sandwich {ρ σ : V → ℝ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 ≤ δ) (hsmall : δ ≤ r / 2)
    (hρ : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u)
    (hclose : ∀ u : V, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    (1 - δ / r) • radialBody ρ ⊆ radialBody σ ∧
      radialBody σ ⊆ (1 + δ / r) • radialBody ρ := by
  have he0 : 0 ≤ δ / r := div_nonneg hδ hr.le
  have hehalf : δ / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
  have hmul : (δ / r) * r = δ := div_mul_cancel₀ δ hr.ne'
  have heρ (u : V) (hu : ‖u‖ = 1) : δ ≤ (δ / r) * ρ u := by
    have h := mul_le_mul_of_nonneg_left (hρ u hu) he0
    rwa [hmul] at h
  constructor
  · apply (smul_radialBody_subset (show 0 ≤ 1 - δ / r by linarith)).trans
    apply radialBody_mono
    intro u hu
    have h := (abs_le.mp (hclose u hu)).2
    nlinarith [heρ u hu]
  · apply (radialBody_mono (ρ := σ) (σ := fun u ↦ (1 + δ / r) * ρ u) ?_).trans
      (radialBody_subset_smul (show 0 < 1 + δ / r by linarith))
    intro u hu
    have h := (abs_le.mp (hclose u hu)).1
    nlinarith [heρ u hu]

/-- If two sets have a common inner set and common outer set, their symmetric
difference is contained in the shell between those two sets. -/
theorem symmDiff_subset_shell {α : Type*} {S T I O : Set α}
    (hIS : I ⊆ S) (hIT : I ⊆ T) (hSO : S ⊆ O) (hTO : T ⊆ O) :
    S ∆ T ⊆ O \ I := by
  rintro x (hx | hx)
  · exact ⟨hSO hx.1, fun hI ↦ hx.2 (hIT hI)⟩
  · exact ⟨hTO hx.1, fun hI ↦ hx.2 (hIS hI)⟩

end RadialGeometry

/-- A linear bound for the change in the volume scaling polynomial on the
compact scalar interval `[1/2, 3/2]`. -/
theorem homothety_shell_factor_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    (1 + ε) ^ n - (1 - ε) ^ n ≤ (2 * (n : ℝ) * 2 ^ (n - 1)) * ε := by
  have habs : |(1 + ε) - (1 - ε)| = 2 * ε := by
    have h : (1 + ε) - (1 - ε) = 2 * ε := by ring
    rw [h, abs_of_nonneg (by positivity)]
  have hmax : max |1 + ε| |1 - ε| ≤ (2 : ℝ) := by
    apply max_le
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  calc
    _ ≤ |(1 + ε) ^ n - (1 - ε) ^ n| := le_abs_self _
    _ ≤ |(1 + ε) - (1 - ε)| * (n : ℝ) * max |1 + ε| |1 - ε| ^ (n - 1) :=
      abs_pow_sub_pow_le (1 + ε) (1 - ε) n
    _ ≤ (2 * ε) * (n : ℝ) * 2 ^ (n - 1) := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _) (by positivity)
    _ = (2 * (n : ℝ) * 2 ^ (n - 1)) * ε := by ring

section RadialVolume

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Real-valued Haar volume under a nonnegative homothety. -/
theorem measureReal_smul_of_nonneg (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {a : ℝ} (ha : 0 ≤ a) (S : Set V) :
    μ.real (a • S) = a ^ Module.finrank ℝ V * μ.real S := by
  simp only [measureReal_def, Measure.addHaar_smul_of_nonneg μ ha,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha _)]

/-- Close radii differ in volume only inside a thin homothetic shell. -/
theorem radialBody_symmDiff_measure_small (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ρ σ : V → ℝ} (hS : IsCompact (radialBody ρ)) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 ≤ δ) (hsmall : δ ≤ r / 2)
    (hρ : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u)
    (hclose : ∀ u : V, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    μ.real (radialBody ρ ∆ radialBody σ) ≤
      ((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) *
        μ.real (radialBody ρ) / r) * δ := by
  have he0 : 0 ≤ δ / r := div_nonneg hδ hr.le
  have hehalf : δ / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
  have hc : 0 ≤ 1 - δ / r := by linarith
  have hρ0 : ∀ u : V, ‖u‖ = 1 → 0 ≤ ρ u := fun u hu ↦ hr.le.trans (hρ u hu)
  obtain ⟨hIT, hTO⟩ := radialBody_homothety_sandwich hr hδ hsmall hρ hclose
  have hIS : (1 - δ / r) • radialBody ρ ⊆ radialBody ρ :=
    radialBody_contracts hρ0 hc (by linarith)
  have hSO : radialBody ρ ⊆ (1 + δ / r) • radialBody ρ :=
    radialBody_expands hρ0 (by linarith)
  have hO : IsCompact ((1 + δ / r) • radialBody ρ) := IsCompact.smul _ hS
  have hI : IsCompact ((1 - δ / r) • radialBody ρ) := IsCompact.smul _ hS
  have hIO := hIS.trans hSO
  calc
    _ ≤ μ.real (((1 + δ / r) • radialBody ρ) \ ((1 - δ / r) • radialBody ρ)) :=
      measureReal_mono (symmDiff_subset_shell hIS hIT hSO hTO)
        (measure_ne_top_of_subset diff_subset hO.measure_ne_top)
    _ = μ.real ((1 + δ / r) • radialBody ρ) -
        μ.real ((1 - δ / r) • radialBody ρ) :=
      measureReal_diff hIO hI.measurableSet hO.measure_ne_top
    _ = ((1 + δ / r) ^ Module.finrank ℝ V -
        (1 - δ / r) ^ Module.finrank ℝ V) * μ.real (radialBody ρ) := by
      rw [measureReal_smul_of_nonneg μ (by linarith), measureReal_smul_of_nonneg μ hc]
      ring
    _ ≤ ((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) *
        (δ / r)) * μ.real (radialBody ρ) :=
      mul_le_mul_of_nonneg_right (homothety_shell_factor_le _ he0 hehalf) measureReal_nonneg
    _ = _ := by ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem closedBall_subset_radialBody {ρ : V → ℝ} {r : ℝ}
    (hρ : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u) :
    Metric.closedBall (0 : V) r ⊆ radialBody ρ := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hnorm]
  have hxnorm : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  refine Or.inr ⟨‖x‖⁻¹ • x, ‖x‖, hu, norm_nonneg x, hxnorm.trans (hρ _ hu), ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem radialBody_subset_closedBall {ρ : V → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hρ : ∀ u : V, ‖u‖ = 1 → ρ u ≤ R) :
    radialBody ρ ⊆ Metric.closedBall (0 : V) R := by
  rintro x (rfl | ⟨u, t, hu, ht, htr, rfl⟩)
  · simpa only [Metric.mem_closedBall, dist_self] using hR
  · simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, hu, mul_one] using htr.trans (hρ u hu)

omit [BorelSpace V] in
/-- A common positive inner radius bounds the normalising masses away from
zero by the volume of the common inner ball. -/
theorem radialBody_mass_lower (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ρ : V → ℝ} (hS : IsCompact (radialBody ρ)) {r : ℝ} (hr : 0 < r)
    (hρ : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u) :
    0 < μ.real (Metric.closedBall (0 : V) r) ∧
      μ.real (Metric.closedBall (0 : V) r) ≤ μ.real (radialBody ρ) := by
  constructor
  · apply ENNReal.toReal_pos
    · exact (Measure.measure_pos_of_mem_nhds μ
        (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : V) hr)
          Metric.ball_subset_closedBall)).ne'
    · exact (isCompact_closedBall (0 : V) r).measure_ne_top
  · exact measureReal_mono (closedBall_subset_radialBody hρ) hS.measure_ne_top

/-- The full, uniform symmetric-difference estimate. For close radii this uses
the thin-shell argument. For larger changes, the common outer ball suffices. -/
theorem radialBody_symmDiff_measure_le (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ρ σ : V → ℝ} (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hρlo : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u)
    (hρhi : ∀ u : V, ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : V, ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : V, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    μ.real (radialBody ρ ∆ radialBody σ) ≤
      (((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) + 4) *
        μ.real (Metric.closedBall (0 : V) R) / r) * δ := by
  let K : ℝ := 2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)
  let A : ℝ := μ.real (Metric.closedBall (0 : V) R)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := measureReal_nonneg
  have hSA : μ.real (radialBody ρ) ≤ A :=
    measureReal_mono (radialBody_subset_closedBall hR hρhi)
      (isCompact_closedBall (0 : V) R).measure_ne_top
  have hTA : μ.real (radialBody σ) ≤ A :=
    measureReal_mono (radialBody_subset_closedBall hR hσhi)
      (isCompact_closedBall (0 : V) R).measure_ne_top
  change μ.real (radialBody ρ ∆ radialBody σ) ≤ ((K + 4) * A / r) * δ
  by_cases hsmall : δ ≤ r / 2
  · apply (radialBody_symmDiff_measure_small μ hS hr hδ hsmall hρlo hclose).trans
    apply mul_le_mul_of_nonneg_right _ hδ
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith [mul_le_mul_of_nonneg_left hSA hK]
  · have hcrude : μ.real (radialBody ρ ∆ radialBody σ) ≤ 2 * A := by
      apply (measureReal_mono symmDiff_subset_union (hS.union hT).measure_ne_top).trans
      apply (measureReal_union_le _ _).trans
      linarith
    have hlarge : 2 * A ≤ (4 * A / r) * δ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hr).mpr
      have h := mul_le_mul_of_nonneg_left (show r ≤ 2 * δ by linarith) (show 0 ≤ 2 * A by positivity)
      nlinarith
    apply hcrude.trans (hlarge.trans _)
    apply mul_le_mul_of_nonneg_right _ hδ
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith

/-- Normalised moments are uniformly Lipschitz in the sup distance of their
radial functions, on bodies with common positive inner and finite outer radii.
This proves the regularity needed in §2 without a polar-coordinate formula. -/
theorem norm_radialBody_average_sub_le (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ρ σ : V → ℝ} (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ B : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hB0 : 0 ≤ B)
    (hρlo : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u)
    (hσlo : ∀ u : V, ‖u‖ = 1 → r ≤ σ u)
    (hρhi : ∀ u : V, ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : V, ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : V, ‖u‖ = 1 → |ρ u - σ u| ≤ δ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ B) :
    ‖(⨍ x in radialBody ρ, f x ∂μ) - ⨍ x in radialBody σ, f x ∂μ‖ ≤
      ((2 * B / μ.real (Metric.closedBall (0 : V) r)) *
        (((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) + 4) *
          μ.real (Metric.closedBall (0 : V) R) / r)) * δ := by
  obtain ⟨hm, hSm⟩ := radialBody_mass_lower μ hS hr hρlo
  have hTm := (radialBody_mass_lower μ hT hr hσlo).2
  have hSbound := radialBody_subset_closedBall hR hρhi
  have hTbound := radialBody_subset_closedBall hR hσhi
  have hBunion : ∀ x ∈ radialBody ρ ∪ radialBody σ, ‖f x‖ ≤ B := by
    rintro x (hx | hx)
    · apply hB x
      simpa only [Metric.mem_closedBall, dist_zero_right] using hSbound hx
    · apply hB x
      simpa only [Metric.mem_closedBall, dist_zero_right] using hTbound hx
  apply (norm_setAverage_sub_le_symmDiff μ hS.measurableSet hT.measurableSet
    (hS.union hT).measure_lt_top
    (hf.continuousOn.integrableOn_compact hS) (hf.continuousOn.integrableOn_compact hT)
    hB0 hBunion hm hSm hTm).trans
  have hvol := radialBody_symmDiff_measure_le μ hS hT hr hR hδ hρlo hρhi hσhi hclose
  have hcoeff : 0 ≤ 2 * B / μ.real (Metric.closedBall (0 : V) r) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hvol hcoeff

/-- An explicit uniform Lipschitz bound for a normalised moment whose
integrand has norm at most `B` on the common outer ball. -/
noncomputable def radialMomentBound (μ : Measure V) (r R B : ℝ) : ℝ :=
  (2 * B / μ.real (Metric.closedBall (0 : V) r)) *
    (((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) + 4) *
      μ.real (Metric.closedBall (0 : V) R) / r)

/-- An explicit uniform bound for radial volume variation. -/
noncomputable def radialVolumeBound (μ : Measure V) (r R : ℝ) : ℝ :=
  ((2 * (Module.finrank ℝ V : ℝ) * 2 ^ (Module.finrank ℝ V - 1)) + 4) *
    μ.real (Metric.closedBall (0 : V) R) / r

theorem abs_radialBody_measure_sub_le (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ρ σ : V → ℝ} (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hρlo : ∀ u : V, ‖u‖ = 1 → r ≤ ρ u)
    (hρhi : ∀ u : V, ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : V, ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : V, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    |μ.real (radialBody ρ) - μ.real (radialBody σ)| ≤ radialVolumeBound μ r R * δ := by
  apply (abs_measureReal_sub_le_measureReal_symmDiff' hS.measurableSet.nullMeasurableSet
    hT.measurableSet.nullMeasurableSet hS.measure_ne_top hT.measure_ne_top).trans
  exact radialBody_symmDiff_measure_le μ hS hT hr hR hδ hρlo hρhi hσhi hclose

end RadialVolume

section CovarianceRegularity

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem norm_rankOneCovariance (x : G) : ‖rankOneCovariance x‖ = ‖x‖ ^ 2 := by
  simp only [rankOneCovariance, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, pow_two]

variable [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

/-- The covariance operators themselves have the required uniform Lipschitz
dependence on radial functions. The norm is the original operator norm. -/
theorem norm_covarianceOperator_radialBody_sub_le (μ : Measure G) [Measure.IsAddHaarMeasure μ]
    {ρ σ : G → ℝ} (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hρlo : ∀ u : G, ‖u‖ = 1 → r ≤ ρ u)
    (hσlo : ∀ u : G, ‖u‖ = 1 → r ≤ σ u)
    (hρhi : ∀ u : G, ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : G, ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : G, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    ‖covarianceOperator μ (radialBody ρ) - covarianceOperator μ (radialBody σ)‖ ≤
      radialMomentBound μ r R (R ^ 2) * δ := by
  have hB : ∀ x : G, ‖x‖ ≤ R → ‖rankOneCovariance x‖ ≤ R ^ 2 := by
    intro x hx
    rw [norm_rankOneCovariance]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have h := norm_radialBody_average_sub_le μ hS hT hr hR hδ
    (sq_nonneg R) hρlo hσlo hρhi hσhi hclose continuous_rankOneCovariance hB
  simpa only [radialMomentBound, setAverage_eq, covarianceOperator] using h

end CovarianceRegularity

section TensorRegularity

variable {m j : ℕ}

/-- Full ordered tensor coordinates, with the ordinary sup norm on the finite
coordinate array. No inner-product structure is imposed on this coordinate space. -/
def orderedTensorCoordinates (x : Fin m → ℝ) : (Fin j → Fin m) → ℝ :=
  fun indices ↦ ∏ k, x (indices k)

theorem continuous_orderedTensorCoordinates :
    Continuous (orderedTensorCoordinates : (Fin m → ℝ) → (Fin j → Fin m) → ℝ) := by
  unfold orderedTensorCoordinates
  fun_prop

theorem norm_orderedTensorCoordinates_le {R : ℝ} (hR : 0 ≤ R)
    {x : Fin m → ℝ} (hx : ‖x‖ ≤ R) :
    ‖(orderedTensorCoordinates x : (Fin j → Fin m) → ℝ)‖ ≤ R ^ j := by
  apply (pi_norm_le_iff_of_nonneg (pow_nonneg hR j)).mpr
  intro indices
  unfold orderedTensorCoordinates
  calc
    ‖∏ k, x (indices k)‖ = ∏ k, ‖x (indices k)‖ := norm_prod _ _
    _ ≤ ∏ _k : Fin j, R := by
      apply Finset.prod_le_prod
      · intro k _
        exact norm_nonneg _
      · intro k _
        exact (norm_le_pi_norm (f := x) (indices k)).trans hx
    _ = R ^ j := by simp

/-- The actual full ordered tensor averages are uniformly Lipschitz in radial
sup distance. In particular this includes every odd as well as even moment. -/
theorem norm_orderedTensorAverage_radialBody_sub_le (μ : Measure (Fin m → ℝ))
    [Measure.IsAddHaarMeasure μ] {ρ σ : (Fin m → ℝ) → ℝ}
    (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hρlo : ∀ u : Fin m → ℝ, ‖u‖ = 1 → r ≤ ρ u)
    (hσlo : ∀ u : Fin m → ℝ, ‖u‖ = 1 → r ≤ σ u)
    (hρhi : ∀ u : Fin m → ℝ, ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : Fin m → ℝ, ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : Fin m → ℝ, ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    ‖(⨍ x in radialBody ρ, (orderedTensorCoordinates x : (Fin j → Fin m) → ℝ) ∂μ) -
      ⨍ x in radialBody σ, orderedTensorCoordinates x ∂μ‖ ≤
      radialMomentBound μ r R (R ^ j) * δ := by
  simpa only [radialMomentBound] using
    norm_radialBody_average_sub_le μ hS hT hr hR hδ (pow_nonneg hR j)
      hρlo hσlo hρhi hσhi hclose continuous_orderedTensorCoordinates
      (fun x hx ↦ norm_orderedTensorCoordinates_le hR hx)

end TensorRegularity

section EuclideanTensorRegularity

variable {m j : ℕ}

/-- Euclidean input coordinates, with the actual norm-two Euclidean structure;
only the finite output tensor array has its sup norm. -/
noncomputable def euclideanOrderedTensorCoordinates (x : EuclideanSpace ℝ (Fin m)) :
    (Fin j → Fin m) → ℝ := orderedTensorCoordinates (EuclideanSpace.equiv (Fin m) ℝ x)

theorem continuous_euclideanOrderedTensorCoordinates :
    Continuous (euclideanOrderedTensorCoordinates :
      EuclideanSpace ℝ (Fin m) → (Fin j → Fin m) → ℝ) :=
  continuous_orderedTensorCoordinates.comp (EuclideanSpace.equiv (Fin m) ℝ).continuous

theorem norm_euclideanOrderedTensorCoordinates_le {R : ℝ} (hR : 0 ≤ R)
    {x : EuclideanSpace ℝ (Fin m)} (hx : ‖x‖ ≤ R) :
    ‖(euclideanOrderedTensorCoordinates x : (Fin j → Fin m) → ℝ)‖ ≤ R ^ j := by
  apply norm_orderedTensorCoordinates_le hR
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  exact (PiLp.norm_apply_le x i).trans hx

/-- The moment regularity assertion with the paper's actual Euclidean spheres
and Haar measure. Odd tensor degrees are included. -/
theorem norm_euclideanTensorAverage_radialBody_sub_le
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [Measure.IsAddHaarMeasure μ]
    {ρ σ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hS : IsCompact (radialBody ρ)) (hT : IsCompact (radialBody σ))
    {r R δ : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hρlo : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ = 1 → r ≤ ρ u)
    (hσlo : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ = 1 → r ≤ σ u)
    (hρhi : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ = 1 → ρ u ≤ R)
    (hσhi : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ = 1 → σ u ≤ R)
    (hclose : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ = 1 → |ρ u - σ u| ≤ δ) :
    ‖(⨍ x in radialBody ρ, (euclideanOrderedTensorCoordinates x : (Fin j → Fin m) → ℝ) ∂μ) -
      ⨍ x in radialBody σ, euclideanOrderedTensorCoordinates x ∂μ‖ ≤
      radialMomentBound μ r R (R ^ j) * δ := by
  simpa only [radialMomentBound] using
    norm_radialBody_average_sub_le μ hS hT hr hR hδ (pow_nonneg hR j)
      hρlo hσlo hρhi hσhi hclose continuous_euclideanOrderedTensorCoordinates
      (fun x hx ↦ norm_euclideanOrderedTensorCoordinates_le hR hx)

end EuclideanTensorRegularity

section ParameterFamilies

variable {P V F : Type*} [PseudoMetricSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A parameterwise form for direct use in the exact-section bundle: if the
radial functions depend uniformly Lipschitzly on a parameter, so do all bounded
continuous normalised moments. The constant is exhibited explicitly. -/
theorem exists_lipschitzWith_radialMoment_family (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (ρ : P → V → ℝ) (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R B : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hB0 : 0 ≤ B)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a ↦ ρ a u))
    {f : V → F} (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ B) :
    ∃ K : ℝ≥0, (K : ℝ) = radialMomentBound μ r R B * L ∧
      LipschitzWith K (fun a ↦ ⨍ x in radialBody (ρ a), f x ∂μ) := by
  have hK : 0 ≤ radialMomentBound μ r R B := by
    unfold radialMomentBound
    positivity
  refine ⟨⟨radialMomentBound μ r R B * L, mul_nonneg hK L.coe_nonneg⟩, rfl, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hδ : 0 ≤ (L : ℝ) * dist a b := mul_nonneg L.coe_nonneg dist_nonneg
  have hclose : ∀ u : V, ‖u‖ = 1 → |ρ a u - ρ b u| ≤ (L : ℝ) * dist a b := by
    intro u hu
    simpa only [Real.dist_eq] using (hparam u hu).dist_le_mul a b
  have h := norm_radialBody_average_sub_le μ (hcompact a) (hcompact b) hr hR hδ hB0
    (hlo a) (hlo b) (hhi a) (hhi b) hclose hf hB
  simpa only [dist_eq_norm, radialMomentBound, NNReal.coe_mk, mul_assoc] using h

/-- Continuity of the integrand is enough: the common compact outer ball
supplies the uniform bound required by the quantitative theorem. -/
theorem exists_lipschitzWith_radialMoment_family_of_continuous
    (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (ρ : P → V → ℝ) (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a ↦ ρ a u))
    {f : V → F} (hf : Continuous f) :
    ∃ K : ℝ≥0, LipschitzWith K (fun a ↦ ⨍ x in radialBody (ρ a), f x ∂μ) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) R).bddAbove_image hf.norm.continuousOn
  have hbound : ∀ x : V, ‖x‖ ≤ R → ‖f x‖ ≤ max 0 B := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact (hB (mem_image_of_mem (fun x ↦ ‖f x‖) hx')).trans (le_max_right 0 B)
  obtain ⟨K, _, hK⟩ := exists_lipschitzWith_radialMoment_family μ ρ hcompact hr hR
    (le_max_left 0 B) hlo hhi hparam hf hbound
  exact ⟨K, hK⟩

/-- The unnormalised volumes also depend Lipschitzly on the parameter, with
the same common-radius hypotheses. -/
theorem exists_lipschitzWith_radialVolume_family (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    (ρ : P → V → ℝ) (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a ↦ ρ a u)) :
    ∃ K : ℝ≥0, (K : ℝ) = radialVolumeBound μ r R * L ∧
      LipschitzWith K (fun a ↦ μ.real (radialBody (ρ a))) := by
  have hK : 0 ≤ radialVolumeBound μ r R := by unfold radialVolumeBound; positivity
  refine ⟨⟨radialVolumeBound μ r R * L, mul_nonneg hK L.coe_nonneg⟩, rfl, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hδ : 0 ≤ (L : ℝ) * dist a b := mul_nonneg L.coe_nonneg dist_nonneg
  have hclose : ∀ u : V, ‖u‖ = 1 → |ρ a u - ρ b u| ≤ (L : ℝ) * dist a b := by
    intro u hu
    simpa only [Real.dist_eq] using (hparam u hu).dist_le_mul a b
  have h := abs_radialBody_measure_sub_le μ (hcompact a) (hcompact b) hr hR hδ
    (hlo a) (hhi a) (hhi b) hclose
  simpa only [Real.dist_eq, NNReal.coe_mk, mul_assoc] using h

end ParameterFamilies

end BanachIsometric
