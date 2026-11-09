import BanachIsometric.SignedSimplexChainMoments
import BanachIsometric.FiniteDimensionalLipschitzExtension
import BanachIsometric.LipschitzConeNaturality
import BanachIsometric.ExactFamilyPolynomial
import BanachIsometric.SignedCoordinateTransport

/-! One operator-valued Lipschitz extension per simplex produces a polynomial
for its actual signed moment, simultaneously for all evaluation vectors. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set MeasureTheory
open scoped NNReal Topology

def euclideanSimplexWeight (n k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ (2 * k)

theorem continuous_euclideanSimplexWeight (n k : ℕ) : Continuous (euclideanSimplexWeight n k) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.norm).pow _

def operatorSimplexEval (m n : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) y)

theorem exists_homogeneous_operatorSimplex_moment (m n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure] (k : ℕ)
    (σ : RawSingularSimplex (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) n)
    {L : ℝ≥0} (hσ : LipschitzWith L σ) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (n + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m), MvPolynomial.eval (fun i => y i) P =
        ∫ v, signedSimplexCount n ((continuousLinearSingularMap (operatorSimplexEval m n y)).comp σ) v *
          euclideanSimplexWeight n k v ∂μ := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let s := signedSimplexDomain n
  let f : s → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    σ ∘ (signedSimplexCoordinates n).symm
  have hf : LipschitzWith _ f := hσ.comp (signedSimplexCoordinates_symm_lipschitz n)
  obtain ⟨A, ⟨K, hA⟩, hAf⟩ := exists_lipschitz_extension_finiteDimensional s f hf
  let H := A ∘ e
  have hH : LipschitzWith _ H := hA.comp e.lipschitz
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := Measure.map e.symm μ
  letI : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  have hμ : Measure.map e ν = μ := by
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    simp [Function.comp_def]
  let Ω := e.symm '' s
  have hΩ : IsCompact Ω := (isCompact_signedSimplexDomain n).image e.symm.continuous
  obtain ⟨R, hR⟩ := hΩ.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  have hΩR : Ω ⊆ Metric.closedBall 0 R := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right, id_eq] using hR x hx
  obtain ⟨P, hP, hPval⟩ := exists_homogeneous_actual_weightedJacobian_integral
    ν H hH hΩ.measurableSet hΩR k
  refine ⟨P, hP, fun y => ?_⟩
  let S := (continuousLinearSingularMap (operatorSimplexEval m n y)).comp σ
  let F := coordinateMapConjugate e (fun x => H x y)
  have hS : ∃ C : ℝ≥0, LipschitzWith C S := ⟨_, (operatorSimplexEval m n y).lipschitz.comp hσ⟩
  have hF (x : s) : F x.val = S ((signedSimplexCoordinates n).symm x) := by
    change e (A (e (e.symm x.val)) y) = e (f x y)
    rw [e.apply_symm_apply, hAf]
  rw [integral_signedSimplexCount_of_extension n μ S hS F hF (continuous_euclideanSimplexWeight n k), hPval]
  have heΩ : e '' Ω = s := e.image_symm_image s
  have hI := integral_signedJacobian_coordinateConjugate ν e (fun x => H x y) Ω
    (fun v => ‖v‖ ^ (2 * k))
  rw [heΩ, hμ] at hI
  simpa only [F, euclideanSimplexWeight, mul_comm] using hI.symm

theorem exists_homogeneous_operatorChain_moment (m n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure] (k : ℕ)
    (c : RawRationalChains (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) n)
    (hc : c ∈ rawLipschitzCarrier (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) n) :
    ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (n + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m), MvPolynomial.eval (fun i => y i) P =
        rawSignedSimplexMoment n μ (euclideanSimplexWeight n k)
          (rawChainMap (continuousLinearSingularMap (operatorSimplexEval m n y)) n c) := by
  classical
  have hP (σ : c.support) : ∃ P : MvPolynomial (Fin m) ℝ, P.IsHomogeneous (n + 2 * k) ∧
      ∀ y : EuclideanSpace ℝ (Fin m), MvPolynomial.eval (fun i => y i) P =
        ∫ v, signedSimplexCount n ((continuousLinearSingularMap (operatorSimplexEval m n y)).comp σ.val) v *
          euclideanSimplexWeight n k v ∂μ := by
    obtain ⟨L, hL⟩ := (rawLipschitzCarrier_mem c).mp hc σ.val σ.property
    exact exists_homogeneous_operatorSimplex_moment m n μ k σ.val hL
  choose P hPhom hPeval using hP
  refine ⟨∑ σ : c.support, (c σ.val : ℝ) • P σ, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum _ _ _
    intro σ _
    exact (MvPolynomial.homogeneousSubmodule (Fin m) ℝ (n + 2 * k)).smul_mem _ (hPhom σ)
  · intro y
    let M := (rawSignedSimplexMoment n μ (euclideanSimplexWeight n k)).comp
      (rawChainMap (continuousLinearSingularMap (operatorSimplexEval m n y)) n)
    change _ = M c
    have hSum : (∑ σ : c.support, M (Finsupp.single σ.val (c σ.val))) = M c := by
      change (∑ σ ∈ c.support.attach, M (Finsupp.single σ.val (c σ.val))) = M c
      rw [Finset.sum_attach c.support (fun σ => M (Finsupp.single σ (c σ)))]
      have h := congrArg M (Finsupp.sum_single c)
      simpa only [Finsupp.sum, map_sum] using h
    rw [map_sum, ← hSum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, hPeval]
    simp [M, rawChainMap, rawSignedSimplexMoment, Rat.smul_def]

end BanachIsometric.SingularPrism
