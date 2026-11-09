import PL1.IntervalModel

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PL1.IntervalModel

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
variable (μ : Measure Ω) (w : Ω → ℝ≥0) (hw : Measurable w) (hw0 : ∀ x, w x ≠ 0)

include hw hw0

/-- Reweighting L1 by multiplication with a positive density, over either scalar field. -/
def densityIsometry : Lp 𝕜 1 (μ.withDensity (fun x => w x)) →ₗᵢ[𝕜] Lp 𝕜 1 μ where
  toFun := withDensitySMulLI μ hw
  map_add' := (withDensitySMulLI μ hw).map_add
  map_smul' := by
    intro c u
    apply Lp.ext
    simp only [withDensitySMulLI_apply, RingHom.id_apply]
    filter_upwards [(ae_withDensity_iff hw.coe_nnreal_ennreal).1 (Lp.coeFn_smul c u),
      (memL1_smul_of_L1_withDensity hw (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((memL1_smul_of_L1_withDensity hw u).toLp _),
      (memL1_smul_of_L1_withDensity hw u).coeFn_toLp] with x hx h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, hx (by simpa using hw0 x), Pi.smul_apply, smul_comm]
  norm_map' := (withDensitySMulLI μ hw).norm_map

theorem densityIsometry_coeFn (u : Lp 𝕜 1 (μ.withDensity (fun x => w x))) :
    (densityIsometry μ w hw hw0 u : Ω → 𝕜) =ᵐ[μ] (fun x => w x • u x) :=
  (memL1_smul_of_L1_withDensity hw u).coeFn_toLp

theorem integrable_inverse_density (u : Lp 𝕜 1 μ) :
    Integrable (fun x => (w x)⁻¹ • u x) (μ.withDensity (fun x => w x)) := by
  apply (integrable_withDensity_iff_integrable_smul hw).2
  simpa only [smul_smul, mul_inv_cancel₀ (hw0 _), one_smul] using L1.integrable_coeFn u

/-- Divide by the density to recover an L1 class for the weighted measure. -/
def inverseDensity (u : Lp 𝕜 1 μ) : Lp 𝕜 1 (μ.withDensity (fun x => w x)) :=
  (integrable_inverse_density μ w hw hw0 u).toL1 _

theorem densityIsometry_inverseDensity (u : Lp 𝕜 1 μ) :
    densityIsometry μ w hw hw0 (inverseDensity μ w hw hw0 u) = u := by
  apply Lp.ext
  apply (densityIsometry_coeFn μ w hw hw0 _).trans
  have h := (ae_withDensity_iff hw.coe_nnreal_ennreal).1
    (integrable_inverse_density μ w hw hw0 u).coeFn_toL1
  filter_upwards [h] with x hx
  simp only [inverseDensity]
  rw [hx (by simpa using hw0 x), smul_smul, mul_inv_cancel₀ (hw0 x), one_smul]

/-- An everywhere positive finite measurable density gives an actual surjective L1 isometry. -/
def densityEquiv : Lp 𝕜 1 (μ.withDensity (fun x => w x)) ≃ₗᵢ[𝕜] Lp 𝕜 1 μ :=
  LinearIsometryEquiv.ofSurjective (densityIsometry μ w hw hw0)
    (fun u => ⟨inverseDensity μ w hw hw0 u, densityIsometry_inverseDensity μ w hw hw0 u⟩)

omit hw hw0

/-- Geometric mass of component n in the probability disjoint union. -/
def componentWeight (n : ℕ) : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (n + 1)

@[simp] theorem componentWeight_ne_zero (n : ℕ) : componentWeight n ≠ 0 := by
  simp [componentWeight]

theorem measurable_componentWeight : Measurable componentWeight := measurable_of_countable _

/-- The explicit geometric probability law on the natural numbers. -/
def componentMeasure : Measure ℕ := Measure.count.withDensity (fun n => componentWeight n)

instance componentMeasure_isProbabilityMeasure : IsProbabilityMeasure componentMeasure := by
  constructor
  rw [componentMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, lintegral_count]
  simp only [componentWeight, ENNReal.coe_pow]
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

/-- The actual probability measure with masses 2^(-n-1) on copies of Ω. -/
def probabilityMeasure (μ : Measure Ω) : Measure (ℕ × Ω) := componentMeasure.prod μ

instance probabilityMeasure_isProbabilityMeasure [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (probabilityMeasure μ) := by
  unfold probabilityMeasure
  infer_instance

theorem probabilityMeasure_eq_withDensity [SFinite μ] :
    probabilityMeasure μ = (disjointMeasure μ).withDensity
      (fun z => (componentWeight z.1 : ℝ≥0∞)) := by
  exact prod_withDensity_left measurable_componentWeight.coe_nnreal_ennreal

/-- Multiplication by the geometric component masses identifies the weighted and
counting L1 models isometrically. -/
def probabilityDisjointEquiv [SFinite μ] :
    Lp 𝕜 1 (probabilityMeasure μ) ≃ₗᵢ[𝕜] DisjointL1 (𝕜 := 𝕜) μ := by
  rw [probabilityMeasure_eq_withDensity μ]
  exact densityEquiv (disjointMeasure μ) (fun z => componentWeight z.1)
    (measurable_componentWeight.comp measurable_fst) (fun z => componentWeight_ne_zero z.1)

/-- Explicit probability normalization of the ell1 sum. -/
def sumProbabilityEquiv [SFinite μ] :
    SumSpace (𝕜 := 𝕜) μ ≃ₗᵢ[𝕜] Lp 𝕜 1 (probabilityMeasure μ) :=
  (sumDisjointEquiv μ).trans (probabilityDisjointEquiv μ).symm

/-- The probability model used for transport of the actual Walsh projection. -/
def walshSumProbabilityEquiv : L1Sum (Lp 𝕜 1 Walsh.haar) ≃ₗᵢ[𝕜]
    Lp 𝕜 1 (probabilityMeasure Walsh.haar) :=
  sumProbabilityEquiv Walsh.haar

end PL1.IntervalModel





