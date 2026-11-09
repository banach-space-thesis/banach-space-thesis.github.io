import PL1.L1Sum
import PL1.WalshModel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The countable disjoint-union L1 model

The construction below gives the actual isometry between an ell1 sum of L1
spaces and L1 on counting measure times the original measure. The further
identification with interval Lebesgue L1 is a separate step.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PL1.IntervalModel

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
variable (μ : Measure Ω) [SFinite μ]

/-- The genuine measure on the countable disjoint union. -/
def disjointMeasure : Measure (ℕ × Ω) := Measure.count.prod μ

abbrev SumSpace := L1Sum (Lp 𝕜 1 μ)
abbrev DisjointL1 := Lp 𝕜 1 (disjointMeasure μ)

/-- Flatten the canonical representatives, one function on each component. -/
def flattenFunction (f : SumSpace (𝕜 := 𝕜) μ) (z : ℕ × Ω) : 𝕜 := f z.1 z.2

theorem measurable_flattenFunction (f : SumSpace (𝕜 := 𝕜) μ) :
    Measurable (flattenFunction μ f) :=
  measurable_from_prod_countable_right (fun n => (Lp.stronglyMeasurable (f n)).measurable)

theorem integrable_flattenFunction (f : SumSpace (𝕜 := 𝕜) μ) :
    Integrable (flattenFunction μ f) (disjointMeasure μ) := by
  apply (integrable_prod_iff (measurable_flattenFunction μ f).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun n => L1.integrable_coeFn (f n))
  · simp only [flattenFunction, ← L1.norm_eq_integral_norm]
    apply integrable_count_iff.2
    simpa only [norm_norm] using L1Sum.summable_norm f

/-- The actual L1 class of the flattened function. -/
def flatten (f : SumSpace (𝕜 := 𝕜) μ) : DisjointL1 (𝕜 := 𝕜) μ :=
  (integrable_flattenFunction μ f).toL1 (flattenFunction μ f)

theorem flatten_coeFn (f : SumSpace (𝕜 := 𝕜) μ) :
    (flatten μ f : ℕ × Ω → 𝕜) =ᵐ[disjointMeasure μ] flattenFunction μ f :=
  (integrable_flattenFunction μ f).coeFn_toL1

theorem norm_flatten (f : SumSpace (𝕜 := 𝕜) μ) : ‖flatten μ f‖ = ‖f‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ z, ‖flatten μ f z‖ ∂disjointMeasure μ) =
        ∫ z, ‖flattenFunction μ f z‖ ∂disjointMeasure μ :=
      integral_congr_ae ((flatten_coeFn μ f).fun_comp norm)
    _ = ∫ n, ∫ x, ‖f n x‖ ∂μ ∂Measure.count :=
      integral_prod _ (integrable_flattenFunction μ f).norm
    _ = ∑' n, ‖f n‖ := by
      simp only [← L1.norm_eq_integral_norm]
      rw [integral_countable (integrable_count_iff.2 (by
        simpa only [norm_norm] using L1Sum.summable_norm f))]
      simp
    _ = ‖f‖ := (L1Sum.norm_eq_tsum f).symm

theorem flatten_add (f g : SumSpace (𝕜 := 𝕜) μ) :
    flatten μ (f + g) = flatten μ f + flatten μ g := by
  apply Lp.ext
  apply (flatten_coeFn μ (f + g)).trans
  apply EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  apply EventuallyEq.trans _ ((flatten_coeFn μ f).add (flatten_coeFn μ g)).symm
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_flattenFunction μ (f + g))
    ((measurable_flattenFunction μ f).add (measurable_flattenFunction μ g)))).2
  exact ae_of_all _ (fun n => Lp.coeFn_add (f n) (g n))

theorem flatten_smul (c : 𝕜) (f : SumSpace (𝕜 := 𝕜) μ) :
    flatten μ (c • f) = c • flatten μ f := by
  apply Lp.ext
  apply (flatten_coeFn μ (c • f)).trans
  apply EventuallyEq.trans _ (Lp.coeFn_smul _ _).symm
  apply EventuallyEq.trans _ ((flatten_coeFn μ f).const_smul c).symm
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_flattenFunction μ (c • f))
    ((measurable_flattenFunction μ f).const_smul c))).2
  exact ae_of_all _ (fun n => Lp.coeFn_smul c (f n))

/-- Isometric flattening into actual L1 on the countable disjoint union. -/
def flattenIsometry : SumSpace (𝕜 := 𝕜) μ →ₗᵢ[𝕜] DisjointL1 (𝕜 := 𝕜) μ where
  toFun := flatten μ
  map_add' := flatten_add μ
  map_smul' := by intro c f; exact flatten_smul μ c f
  norm_map' := norm_flatten μ

/-- Each slice of an integrable function is integrable, since counting measure
has no nonempty null sets. -/
theorem integrable_slice (f : DisjointL1 (𝕜 := 𝕜) μ) (n : ℕ) :
    Integrable (fun x => f (n, x)) μ :=
  Measure.ae_count_iff.1 (L1.integrable_coeFn f).prod_right_ae n

/-- Recover the nth actual L1 class. -/
def slice (f : DisjointL1 (𝕜 := 𝕜) μ) (n : ℕ) : Lp 𝕜 1 μ :=
  (integrable_slice μ f n).toL1 (fun x => f (n, x))

theorem slice_coeFn (f : DisjointL1 (𝕜 := 𝕜) μ) (n : ℕ) :
    (slice μ f n : Ω → 𝕜) =ᵐ[μ] (fun x => f (n, x)) :=
  (integrable_slice μ f n).coeFn_toL1

theorem norm_slice (f : DisjointL1 (𝕜 := 𝕜) μ) (n : ℕ) :
    ‖slice μ f n‖ = ∫ x, ‖f (n, x)‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((slice_coeFn μ f n).fun_comp norm)

theorem summable_norm_slice (f : DisjointL1 (𝕜 := 𝕜) μ) :
    Summable (fun n => ‖slice μ f n‖) := by
  have h := integrable_count_iff.1 (L1.integrable_coeFn f).integral_norm_prod_left
  simp only [norm_slice]
  convert h using 1
  ext n
  exact (Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f (n, x))))).symm

/-- Slicing gives an actual ell1 sequence of L1 classes. -/
def unflatten (f : DisjointL1 (𝕜 := 𝕜) μ) : SumSpace (𝕜 := 𝕜) μ :=
  ⟨slice μ f, by
    apply (memℓp_gen_iff (by simp : 0 < (1 : ℝ≥0∞).toReal)).2
    simpa using summable_norm_slice μ f⟩

theorem flatten_unflatten (f : DisjointL1 (𝕜 := 𝕜) μ) : flatten μ (unflatten μ f) = f := by
  apply Lp.ext
  apply (flatten_coeFn μ (unflatten μ f)).trans
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_flattenFunction μ (unflatten μ f)) (Lp.stronglyMeasurable f).measurable)).2
  exact ae_of_all _ (fun n => slice_coeFn μ f n)

theorem unflatten_flatten (f : SumSpace (𝕜 := 𝕜) μ) : unflatten μ (flatten μ f) = f := by
  apply (flattenIsometry μ).injective
  exact flatten_unflatten μ (flatten μ f)

/-- The actual surjective linear isometry between the ell1 sum and L1 on the
countable disjoint union. No isomorphism witness is assumed. -/
def sumDisjointEquiv : SumSpace (𝕜 := 𝕜) μ ≃ₗᵢ[𝕜] DisjointL1 (𝕜 := 𝕜) μ where
  toFun := flatten μ
  invFun := unflatten μ
  left_inv := unflatten_flatten μ
  right_inv := flatten_unflatten μ
  map_add' := flatten_add μ
  map_smul' := by intro c f; exact flatten_smul μ c f
  norm_map' := norm_flatten μ

/-- Specialization to the actual Haar model used by both projection constructions. -/
def walshSumDisjointEquiv : L1Sum (Lp 𝕜 1 Walsh.haar) ≃ₗᵢ[𝕜]
    Lp 𝕜 1 ((Measure.count : Measure ℕ).prod Walsh.haar) :=
  sumDisjointEquiv Walsh.haar

end PL1.IntervalModel


