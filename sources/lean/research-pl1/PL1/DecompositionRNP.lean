import PL1.FiniteDimensionalRNP
import PL1.VectorDensityBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Radon–Nikodym densities from boundedly complete finite-dimensional projections

The hypotheses describe an actual sequence of finite-dimensional projections.
Existence of such a decomposition is not asserted here.
-/

noncomputable section
universe u v
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PL1.DecompositionRNP

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every bounded coherent sequence in the projection ranges converges in norm.
The case `m = n` of coherence already says that its `n`th term is in the range. -/
def BoundedlyComplete (P : ℕ → E →L[ℝ] E) : Prop :=
  ∀ x : ℕ → E, (∀ m n, m ≤ n → P m (x n) = x m) →
    (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ a, Tendsto x atTop (𝓝 a)

/-- A boundedly complete sequence of uniformly bounded finite-dimensional
projections converging strongly to the identity. -/
structure BoundedlyCompleteDecomposition (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  projection : ℕ → E →L[ℝ] E
  finiteDimensional : ∀ n, FiniteDimensional ℝ (projection n).range
  nested : ∀ m n, m ≤ n → (projection m).comp (projection n) = projection m
  uniformBound : ∃ C : ℝ, ∀ n, ‖projection n‖ ≤ C
  tendsto_identity : ∀ x, Tendsto (fun n => projection n x) atTop (𝓝 x)
  bounded_complete : BoundedlyComplete projection

section Densities
variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Uniqueness in the setwise formulation used by the reviewed definition. -/
theorem ae_eq_of_setwise_integral_eq {g h : Ω → E}
    (hg : Integrable g μ) (hh : Integrable h μ)
    (heq : ∀ A : Set Ω, MeasurableSet A → (∫ x in A, g x ∂μ) = ∫ x in A, h x ∂μ) :
    g =ᵐ[μ] h := by
  apply hg.ae_eq_of_withDensityᵥ_eq hh
  apply VectorMeasure.ext
  intro A hA
  simpa only [withDensityᵥ_apply hg hA, withDensityᵥ_apply hh hA] using heq A hA

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- A bounded linear image taking values in an RNP space admits a setwise density. -/
theorem exists_density_of_RNP_image {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : HasRadonNikodymProperty.{_, v} F) (T : E →L[ℝ] F)
    (hμ : μ univ < ∞) (ν : VectorMeasure Ω E) (hν : ν.variation univ < ∞)
    (hAC : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → ν A = 0) :
    ∃ g : Ω → F, Integrable g μ ∧
      ∀ A : Set Ω, MeasurableSet A → T (ν A) = ∫ x in A, g x ∂μ := by
  refine hF Ω ‹MeasurableSpace Ω› μ hμ (RNPBridge.mapVectorMeasure T ν) ?_ ?_
  · exact RNPBridge.mapVectorMeasure_finite_variation T ν hν
  · intro A hA hz
    rw [RNPBridge.mapVectorMeasure_apply, hAC A hA hz, map_zero]

/-- A finite-rank image of a finite-variation vector measure has a Bochner density. -/
theorem exists_density_of_finite_rank (P : E →L[ℝ] E)
    (hP : FiniteDimensional ℝ P.range) (hμ : μ univ < ∞)
    (ν : VectorMeasure Ω E) (hν : ν.variation univ < ∞)
    (hAC : ∀ A : Set Ω, MeasurableSet A → μ A = 0 → ν A = 0) :
    ∃ g : Ω → E, Integrable g μ ∧
      ∀ A : Set Ω, MeasurableSet A → P (ν A) = ∫ x in A, g x ∂μ := by
  let := hP
  have hRNP : HasRadonNikodymProperty.{u, v} P.range :=
    RNPBridge.hasRadonNikodymProperty_of_finiteDimensional P.range
  obtain ⟨g, hg, hrepr⟩ := exists_density_of_RNP_image hRNP P.rangeRestrict hμ ν hν hAC
  refine ⟨fun x => P.range.subtypeL (g x), P.range.subtypeL.integrable_comp hg, ?_⟩
  intro A hA
  rw [P.range.subtypeL.integral_comp_comm hg.integrableOn, ← hrepr A hA]
  rfl
/-- Nested operators force the corresponding densities to agree almost everywhere. -/
theorem densities_coherent (P : ℕ → E →L[ℝ] E)
    (hP : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (ν : VectorMeasure Ω E) (g : ℕ → Ω → E)
    (hg : ∀ n, Integrable (g n) μ)
    (hrepr : ∀ n (A : Set Ω), MeasurableSet A → P n (ν A) = ∫ x in A, g n x ∂μ) :
    ∀ᵐ x ∂μ, ∀ m n, m ≤ n → P m (g n x) = g m x := by
  have hmn (m n : ℕ) (hmn : m ≤ n) : (fun x => P m (g n x)) =ᵐ[μ] g m := by
    apply ae_eq_of_setwise_integral_eq ((P m).integrable_comp (hg n)) (hg m)
    intro A hA
    rw [(P m).integral_comp_comm (hg n).integrableOn, ← hrepr n A hA, ← hrepr m A hA]
    exact congrArg (fun T : E →L[ℝ] E => T (ν A)) (hP m n hmn)
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro n
  by_cases h : m ≤ n
  · filter_upwards [hmn m n h] with x hx using fun _ => hx
  · exact Eventually.of_forall fun _ h' => (h h').elim

omit [CompleteSpace E] in
/-- A common integrable bound turns bounded completeness into an integrable limit. -/
theorem exists_integrable_limit (P : ℕ → E →L[ℝ] E) (hP : BoundedlyComplete P)
    (g : ℕ → Ω → E) (hg : ∀ n, Integrable (g n) μ)
    (hcoh : ∀ᵐ x ∂μ, ∀ m n, m ≤ n → P m (g n x) = g m x)
    (b : Ω → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ b x) :
    ∃ f : Ω → E, Integrable f μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x))) := by
  let f (x : Ω) := limUnder atTop (fun n => g n x)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    filter_upwards [hcoh, ae_all_iff.mpr hbound] with x hx hbx
    exact tendsto_nhds_limUnder (hP (fun n => g n x) hx ⟨b x, hbx⟩)
  have hmeas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hg n).aestronglyMeasurable) hlim
  have hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ b x := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with x hx hbx
    exact le_of_tendsto hx.norm (Eventually.of_forall hbx)
  exact ⟨f, hb.mono' hmeas hfb, hlim⟩

omit [CompleteSpace E] in
/-- Recover a vector measure from dominated densities of strongly convergent
projections. This is the analytic limit step of bounded-completeness implies RNP. -/
theorem exists_density_of_dominated_coherent_projections
    (P : ℕ → E →L[ℝ] E) (hP : BoundedlyComplete P)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (ν : VectorMeasure Ω E) (g : ℕ → Ω → E) (hg : ∀ n, Integrable (g n) μ)
    (hrepr : ∀ n (A : Set Ω), MeasurableSet A → P n (ν A) = ∫ x in A, g n x ∂μ)
    (hcoh : ∀ᵐ x ∂μ, ∀ m n, m ≤ n → P m (g n x) = g m x)
    (b : Ω → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ b x) :
    ∃ f : Ω → E, Integrable f μ ∧
      ∀ A : Set Ω, MeasurableSet A → ν A = ∫ x in A, f x ∂μ := by
  obtain ⟨f, hf, hlim⟩ := exists_integrable_limit P hP g hg hcoh b hb hbound
  refine ⟨f, hf, fun A hA => ?_⟩
  have hi := tendsto_integral_of_dominated_convergence (μ := μ.restrict A) b
    (fun n => (hg n).integrableOn.aestronglyMeasurable) hb.integrableOn
    (fun n => ae_restrict_of_ae (hbound n)) (ae_restrict_of_ae hlim)
  have hp : Tendsto (fun n => ∫ x in A, g n x ∂μ) atTop (𝓝 (ν A)) := by
    simpa only [← hrepr _ A hA] using hstrong (ν A)
  exact tendsto_nhds_unique hp hi

end Densities
/-- A boundedly complete finite-dimensional projection decomposition implies the
full reviewed vector-measure Radon–Nikodym property, for every source universe. -/
theorem hasRadonNikodymProperty_of_boundedlyCompleteDecomposition
    (D : BoundedlyCompleteDecomposition E) : HasRadonNikodymProperty.{u, v} E := by
  intro Ω mΩ
  let := mΩ
  intro μ hμ ν hν hAC
  let : IsFiniteMeasure μ := ⟨hμ⟩
  let : IsFiniteMeasure ν.variation := ⟨hν⟩
  have hdensity (n : ℕ) : ∃ g : Ω → E, Integrable g μ ∧
      ∀ A : Set Ω, MeasurableSet A → D.projection n (ν A) = ∫ x in A, g x ∂μ :=
    exists_density_of_finite_rank (D.projection n) (D.finiteDimensional n) hμ ν hν hAC
  choose g hg hrepr using hdensity
  obtain ⟨C, hC⟩ := D.uniformBound
  have hC0 : 0 ≤ C := (norm_nonneg (D.projection 0)).trans (hC 0)
  let b (x : Ω) : ℝ := C * (ν.variation.rnDeriv μ x).toReal
  have hderiv : Integrable (fun x => (ν.variation.rnDeriv μ x).toReal) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := ν.variation) (ν := μ) (s := univ) hν.ne)
  have hb : Integrable b μ := hderiv.const_mul C
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖g n x‖ ≤ b x := by
    apply VectorDensityBounds.ae_norm_map_density_le_rnDeriv μ ν hAC
      (D.projection n) (hg n) _ C hC0 (hC n)
    apply VectorMeasure.ext
    intro A hA
    rw [withDensityᵥ_apply (hg n) hA, RNPBridge.mapVectorMeasure_apply]
    exact (hrepr n A hA).symm
  exact exists_density_of_dominated_coherent_projections D.projection D.bounded_complete
    D.tendsto_identity ν g hg hrepr (densities_coherent D.projection D.nested ν g hg hrepr)
    b hb hbound

/-- Failure of RNP rules out every decomposition satisfying these concrete properties. -/
theorem no_boundedlyCompleteDecomposition_of_not_RNP
    (hE : ¬ HasRadonNikodymProperty.{u, v} E) :
    IsEmpty (BoundedlyCompleteDecomposition E) :=
  ⟨fun D => hE (hasRadonNikodymProperty_of_boundedlyCompleteDecomposition D)⟩

end PL1.DecompositionRNP












