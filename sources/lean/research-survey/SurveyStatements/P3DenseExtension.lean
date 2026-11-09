import SurveyStatements.P3GeneratedQuotient
import SurveyStatements.P3Diagonal
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Extending the diagonal interpolation map from a countable dense rational
subspace, and recovering its scalar linearity through generator pairings. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem uniformlyContinuous_of_generator_pairing [Module ℚ Y]
    (D : Submodule ℚ Y) (g : ℕ → X →L[𝕜] 𝕜) (w : ℕ → Y →L[𝕜] 𝕜)
    (a₀ : D → X ⧸ preannihilator (generatedDualSpace g))
    (hp : ∀ i d, generatorLift g i (a₀ d) = w i d.val)
    (C : NNReal) (hb : ∀ d : D, ‖a₀ d‖ ≤ C * ‖d‖) : UniformContinuous a₀ := by
  have hsub (d e : D) : a₀ (d - e) = a₀ d - a₀ e := by
    apply sub_eq_zero.mp
    apply quotient_eq_zero_of_generatorLift_eq_zero g
    intro i
    simp only [map_sub, hp, Submodule.coe_sub, sub_self]
  apply (LipschitzWith.of_dist_le_mul (K := C) ?_).uniformContinuous
  intro d e
  rw [dist_eq_norm, dist_eq_norm, ← hsub]
  exact hb (d - e)

theorem extend_generator_pairing [CompleteSpace X] [Module ℚ Y]
    (D : Submodule ℚ Y) (hD : Dense (D : Set Y))
    (g : ℕ → X →L[𝕜] 𝕜) (w : ℕ → Y →L[𝕜] 𝕜)
    (a₀ : D → X ⧸ preannihilator (generatedDualSpace g))
    (ha₀ : UniformContinuous a₀)
    (hp : ∀ i d, generatorLift g i (a₀ d) = w i d.val) :
    ∃ A : Y →L[𝕜] (X ⧸ preannihilator (generatedDualSpace g)),
      ∀ i y, generatorLift g i (A y) = w i y := by
  let hu := isUniformInducing_val (D : Set Y)
  let hd : DenseRange ((↑) : D → Y) := hD.denseRange_val
  let a := (hu.isDenseInducing hd).extend a₀
  have ha : Continuous a := (uniformContinuous_uniformly_extend hu hd ha₀).continuous
  have he (d : D) : a d.val = a₀ d := uniformly_extend_of_ind hu hd ha₀ d
  have hpair (i : ℕ) (y : Y) : generatorLift g i (a y) = w i y := by
    have hfun : (fun y => generatorLift g i (a y)) = w i := by
      apply Continuous.ext_on hD ((generatorLift g i).continuous.comp ha) (w i).continuous
      intro d hd
      change generatorLift g i (a d) = w i d
      rw [he ⟨d, hd⟩]
      exact hp i ⟨d, hd⟩
    exact congrFun hfun y
  exact ⟨operatorOfGeneratorPairing g w a ha hpair, hpair⟩

/-- The constructive extraction statement needed for the main theorem.
The quotient is determined by the algebraic span of an independent sequence;
its preannihilator is closed, so completeness follows from completeness of `X`. -/
theorem exists_separable_extraction [CompleteSpace X] [TopologicalSpace.SeparableSpace Y]
    (J : E →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) (U : E →L[𝕜] (Y →L[𝕜] 𝕜))
    (hE : ¬ FiniteDimensional 𝕜 E) :
    ∃ e : ℕ → E, LinearIndependent 𝕜 e ∧
      ∃ A : Y →L[𝕜] (X ⧸ preannihilator (generatedDualSpace (fun i => J (e i)))),
        ∀ i y, generatorLift (fun i => J (e i)) i (A y) = U (e i) y := by
  letI : Module ℚ Y := RestrictScalars.module ℚ 𝕜 Y
  obtain ⟨D, hcount, hD⟩ := exists_countable_dense_rationalSubspace (Y := Y)
  letI := hcount
  obtain ⟨d, hd⟩ := exists_surjective_nat D
  let y : ℕ → Y := fun n => (d n).val
  obtain ⟨e, x, he, hxnorm, hpair⟩ := exists_diagonal_sequences J U hE y
  let g : ℕ → X →L[𝕜] 𝕜 := fun i => J (e i)
  let k : D → ℕ := fun z => Classical.choose (hd z)
  have hk (z : D) : d (k z) = z := Classical.choose_spec (hd z)
  let a₀ : D → X ⧸ preannihilator (generatedDualSpace g) := fun z =>
    quotientMap (preannihilator (generatedDualSpace g)) (x (k z))
  have haPair (i : ℕ) (z : D) : generatorLift g i (a₀ z) = U (e i) z.val := by
    change J (e i) (x (k z)) = U (e i) z.val
    rw [← hpair i (k z)]
    simp only [y, hk z]
  let C : NNReal := ⟨2 * ‖U‖, mul_nonneg (by norm_num) U.opNorm_nonneg⟩
  have haBound (z : D) : ‖a₀ z‖ ≤ C * ‖z‖ := by
    calc
      ‖a₀ z‖ ≤ ‖x (k z)‖ := Submodule.Quotient.norm_mk_le _ _
      _ ≤ 2 * ‖U‖ * ‖y (k z)‖ := hxnorm (k z)
      _ = C * ‖z‖ := by
        change 2 * ‖U‖ * ‖(d (k z)).val‖ = (2 * ‖U‖) * ‖z.val‖
        rw [hk z]
  have haCont : UniformContinuous a₀ :=
    uniformlyContinuous_of_generator_pairing D g (fun i => U (e i)) a₀ haPair C haBound
  obtain ⟨A, hA⟩ := extend_generator_pairing D hD g (fun i => U (e i)) a₀ haCont haPair
  exact ⟨e, he, A, hA⟩

end SurveyStatements.P3
