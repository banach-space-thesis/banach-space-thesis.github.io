import BanachIsometric.CoordinateOrthogonality
import BanachIsometric.TensorOrbitSection
import BanachIsometric.MomentRegularity
import BanachIsometric.RadialStarBody
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact locally Lipschitz lifts of normalized radial families

Euclidean bodies and their Haar measures are transported through the explicit
coordinate equivalence. The finite moment tuple is the average of an actual
continuous polynomial integrand on the original Euclidean space. Its proved
radial Lipschitz estimate composes with the actual orthogonal orbit section.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

def coordinateMeasure {m : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin m))) :
    Measure (Fin m → ℝ) := μ.map (euclideanCoordinates m)

theorem coordinateMeasure_isAddHaarMeasure {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure] :
    (coordinateMeasure μ).IsAddHaarMeasure :=
  (euclideanCoordinates m).isAddHaarMeasure_map μ

theorem coordinateMeasure_coordinateBody {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) (S : Set (EuclideanSpace ℝ (Fin m))) :
    coordinateMeasure μ (coordinateBody S) = μ S := by
  let e := (euclideanCoordinates m).toHomeomorph.toMeasurableEquiv
  change μ.map e (e '' S) = μ S
  rw [e.map_apply, e.injective.preimage_image]

theorem coordinateBody_regularClosed {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : closure (interior S) = S) :
    closure (interior (coordinateBody S)) = coordinateBody S := by
  let e := (euclideanCoordinates m).toHomeomorph
  change closure (interior (e '' S)) = e '' S
  rw [← e.image_interior, ← e.image_closure, hS]

/-- All selected monomials as one finite-dimensional continuous integrand. -/
def euclideanTupleIntegrand (m : ℕ) (I : Finset ℕ+)
    (x : EuclideanSpace ℝ (Fin m)) : TensorTupleCoordinates m I :=
  fun ij => ∏ k : Fin (ij.1.val : ℕ), x (ij.2 k)

theorem continuous_euclideanTupleIntegrand (m : ℕ) (I : Finset ℕ+) :
    Continuous (euclideanTupleIntegrand m I) := by
  apply continuous_pi
  intro ij
  apply continuous_finset_prod
  intro k _
  exact (EuclideanSpace.proj (ij.2 k)).continuous

/-- Exact coordinate-measure transport, including the normalization factor.
This is an equality of the actual full tuples, including odd tensor degrees. -/
theorem bodyTensorTuple_coordinateBody {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S) (I : Finset ℕ+) :
    bodyTensorTuple (coordinateMeasure μ) (coordinateBody S) I =
      ⨍ x in S, euclideanTupleIntegrand m I x ∂μ := by
  let e := (euclideanCoordinates m).toHomeomorph.toMeasurableEquiv
  have hmap : (normalizedRestriction μ S).map e =
      normalizedRestriction (coordinateMeasure μ) (coordinateBody S) :=
    normalizedRestriction_map μ e S
  have hint : IntegrableOn (euclideanTupleIntegrand m I) S μ :=
    (continuous_euclideanTupleIntegrand m I).continuousOn.integrableOn_compact hS
  funext ij
  change (∫ x, ∏ k : Fin (ij.1.val : ℕ), x (ij.2 k)
      ∂normalizedRestriction (coordinateMeasure μ) (coordinateBody S)) = _
  rw [← hmap, integral_map_equiv e]
  change (∫ x, euclideanTupleIntegrand m I x ij ∂normalizedRestriction μ S) = _
  rw [integral_normalizedRestriction, setAverage_eq]
  change (μ.real S)⁻¹ * (∫ x in S, euclideanTupleIntegrand m I x ij ∂μ) =
    (μ.real S)⁻¹ * ((∫ x in S, euclideanTupleIntegrand m I x ∂μ) ij)
  congr 1
  exact (ContinuousLinearMap.proj ij : TensorTupleCoordinates m I →L[ℝ] ℝ).integral_comp_comm hint

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_lipschitz_coordinateBody_tuple_radial_family {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (ρ : P → EuclideanSpace ℝ (Fin m) → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a => ρ a u))
    (I : Finset ℕ+) :
    ∃ K : ℝ≥0, LipschitzWith K (fun a =>
      bodyTensorTuple (coordinateMeasure μ) (coordinateBody (radialBody (ρ a))) I) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_radialMoment_family_of_continuous μ ρ hcompact
    hr hR hlo hhi hparam (continuous_euclideanTupleIntegrand m I)
  refine ⟨K, ?_⟩
  simpa only [bodyTensorTuple_coordinateBody μ _ (hcompact _) I] using hK

/-- An exact locally Lipschitz family of genuine Euclidean linear equivalences
carrying the reference body to each nearby member. The bodies are in covariance
position and are assumed only real-linearly equivalent to the reference body.
Regular closedness is required solely at the reference body. -/
theorem exists_lipschitz_normalized_radial_lift {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (ρ : P → EuclideanSpace ℝ (Fin m) → ℝ)
    (hcompact : ∀ a, IsCompact (radialBody (ρ a)))
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlo : ∀ a u, ‖u‖ = 1 → r ≤ ρ a u)
    (hhi : ∀ a u, ‖u‖ = 1 → ρ a u ≤ R)
    {L : ℝ≥0} (hparam : ∀ u, ‖u‖ = 1 → LipschitzWith L (fun a => ρ a u))
    (a₀ : P) (hreg : closure (interior (radialBody (ρ a₀))) = radialBody (ρ a₀))
    (hcov : ∀ a, covarianceOperator μ (radialBody (ρ a)) = ContinuousLinearMap.id ℝ _)
    (hequiv : ∀ a, ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      e '' radialBody (ρ a₀) = radialBody (ρ a)) :
    ∃ e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        e a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, e a '' radialBody (ρ a₀) = radialBody (ρ a) := by
  classical
  let ν := coordinateMeasure μ
  letI : ν.IsAddHaarMeasure := coordinateMeasure_isAddHaarMeasure μ
  let S : P → Set (Fin m → ℝ) := fun a => coordinateBody (radialBody (ρ a))
  have hS0 : ν (S a₀) ≠ 0 := by
    rw [coordinateMeasure_coordinateBody]
    have hm := radialBody_mass_lower μ (hcompact a₀) hr (hlo a₀)
    exact (ENNReal.toReal_pos_iff.mp (hm.1.trans_le hm.2)).1.ne'
  obtain ⟨I, s, N, hN, KS, hs, hsLip, hLift⟩ :=
    exists_lipschitz_bodyMoment_image_section ν (S a₀)
      (isCompact_coordinateBody (hcompact a₀)) (coordinateBody_regularClosed hreg) hS0
  let M : P → TensorTupleCoordinates m I := fun a => bodyTensorTuple ν (S a) I
  obtain ⟨KM, hM⟩ := exists_lipschitz_coordinateBody_tuple_radial_family μ ρ hcompact
    hr hR hlo hhi hparam I
  have hMlip : LipschitzWith KM M := hM
  have hMN : M ⁻¹' N ∈ 𝓝 a₀ := hMlip.continuous.continuousAt.preimage_mem_nhds hN
  obtain ⟨U, hUN, hU, ha₀U⟩ := mem_nhds_iff.mp hMN
  let e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun a => orthogonalEuclideanEquiv (s (M a))
  have hQ : LipschitzOnWith (KS * KM) (fun a => ((s (M a)).val : Matrix (Fin m) (Fin m) ℝ)) U := by
    have h := hsLip.comp hMlip.lipschitzOnWith (fun a ha => hUN ha)
    exact h
  refine ⟨e, U, ‖matrixEuclideanOperator m‖₊ * (KS * KM), hU, ha₀U, ?_, ?_, ?_⟩
  · change orthogonalEuclideanEquiv (s (bodyTensorTuple ν (S a₀) I)) = _
    rw [hs, orthogonalEuclideanEquiv_one]
  · have h := (matrixEuclideanOperator m).lipschitz.lipschitzOnWith.comp hQ
      (fun _ _ => mem_univ _)
    simpa only [← orthogonalEuclideanEquiv_toContinuousLinearMap] using h
  · intro a ha
    apply (orthogonalEuclideanEquiv_image_iff (s (M a)) _ _).mpr
    change (s (M a)).val.mulVec '' S a₀ = S a
    apply hLift (S a) ?_ (hUN ha)
    obtain ⟨d, hd⟩ := hequiv a
    exact exists_orthogonal_coordinate_image_of_covariancePosition μ (hcompact a₀)
      (hcov a₀) (hcov a) d hd

end
end BanachIsometric
