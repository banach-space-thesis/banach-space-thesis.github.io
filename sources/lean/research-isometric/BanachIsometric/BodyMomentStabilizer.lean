import BanachIsometric.TensorMoments
import BanachIsometric.OrthogonalStabilizer

/-!
# A finite tuple of actual body moments detects every automorphism

This is the finite-moment stabiliser assertion of Lemma 2.1(ii). The moments
are scalar integrals against the normalised uniform measure of the specified
body. Their transformation rule and their separation of bodies have already
been proved in `TensorMoments` and `MomentSeparation`; neither is assumed here.

The result is proved for every compact regular closed body of positive volume.
It applies to real-linear equivalences, and does not require covariance
normalisation, orthogonality, symmetry, or convexity.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped ENNReal

/-- A real linear homeomorphism preserves the regular-closedness needed to
recover the actual body from the support of its uniform measure. -/
theorem closure_interior_linearEquiv_image {m : ℕ} {S : Set (Fin m → ℝ)}
    (hS : closure (interior S) = S)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    closure (interior (e '' S)) = e '' S := by
  have h : closure (interior (e.toHomeomorph '' S)) = e.toHomeomorph '' S := by
    rw [← e.toHomeomorph.image_interior, ← e.toHomeomorph.image_closure, hS]
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using h

/-- A positive finite-volume body has a positive-volume image. This is derived
from normalised Haar transport and mass one, not assumed as a change-of-variables
axiom. -/
theorem measure_linearEquiv_image_ne_zero {m : ℕ} (μ : Measure (Fin m → ℝ))
    [μ.IsAddHaarMeasure] {S : Set (Fin m → ℝ)} (hS : IsCompact S) (h0 : μ S ≠ 0)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) : μ (e '' S) ≠ 0 := by
  letI : IsProbabilityMeasure (normalizedRestriction μ S) :=
    normalizedRestriction_isProbabilityMeasure μ S h0 hS.measure_ne_top
  have hmass : (normalizedRestriction μ S).map e univ = 1 := by
    simp [Measure.map_apply e.continuous.measurable]
  rw [normalizedRestriction_map_linearEquiv μ e S] at hmass
  intro hz
  simp [normalizedRestriction, hz] at hmass

/-- A real-linear equivalence preserves the body exactly when it fixes every
one of its positive-order moment tensors. The converse recovers boundaries,
not only equality up to measure zero. -/
theorem image_eq_self_iff_bodyTensorMoments_fixed {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    e '' S = S ↔ ∀ d : ℕ+,
      tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap)
        (bodyTensorMoment μ S (d : ℕ)) = bodyTensorMoment μ S (d : ℕ) := by
  constructor
  · intro he d
    calc
      tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap)
          (bodyTensorMoment μ S (d : ℕ)) = bodyTensorMoment μ (e '' S) (d : ℕ) :=
        (bodyTensorMoment_image μ S hS h0 e).symm
      _ = bodyTensorMoment μ S (d : ℕ) := by rw [he]
  · intro hfix
    apply set_eq_of_bodyTensorMoments_eq μ (e '' S) S (hS.image e.continuous) hS
      (closure_interior_linearEquiv_image hreg e) hreg
      (measure_linearEquiv_image_ne_zero μ hS h0 e) h0
    intro r hr
    rw [bodyTensorMoment_image μ S hS h0 e]
    exact hfix ⟨r, hr⟩

/-- Finitely many positive degrees of the actual normalised body moments
characterise its full real-linear automorphism group. Odd degrees are retained.
This is the finite-tuple claim of Lemma 2.1(ii), before restricting to `O(m)`.
-/
theorem exists_finset_bodyMoment_stabilizer_degrees {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+, ∀ e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
      e '' S = S ↔ ∀ d ∈ I,
        tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap)
          (bodyTensorMoment μ S (d : ℕ)) = bodyTensorMoment μ S (d : ℕ) := by
  obtain ⟨I, hI⟩ := exists_finset_tensor_stabilizer_degrees m
    (fun d : ℕ+ => bodyTensorMoment μ S (d : ℕ))
  refine ⟨I, ?_⟩
  intro e
  exact (image_eq_self_iff_bodyTensorMoments_fixed μ S hS hreg h0 e).trans
    (hI (LinearMap.toMatrix' e.toLinearMap))

/-- The same finite tuple applies to purely algebraic real-linear equivalences.
Continuity is supplied automatically by finite dimensionality, so it is not an
extra hypothesis on the automorphisms in the paper. -/
theorem exists_finset_bodyMoment_stabilizer_degrees_linearEquiv {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+, ∀ e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ),
      e '' S = S ↔ ∀ d ∈ I,
        tensorCoordinateAction (LinearMap.toMatrix' e.toLinearMap)
          (bodyTensorMoment μ S (d : ℕ)) = bodyTensorMoment μ S (d : ℕ) := by
  obtain ⟨I, hI⟩ := exists_finset_bodyMoment_stabilizer_degrees μ S hS hreg h0
  exact ⟨I, fun e => hI e.toContinuousLinearEquiv⟩

/-- The same finite tuple defines the concrete compact orthogonal body
stabiliser subgroup. Together with covariance position this is exactly the
stabiliser description in Lemma 2.1(ii). -/
theorem exists_finset_orthogonalBodyMoment_stabilizer_degrees {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+, ∀ Q : Matrix.orthogonalGroup (Fin m) ℝ,
      Q ∈ orthogonalBodyStabilizerSubgroup m S ↔ ∀ d ∈ I,
        tensorCoordinateAction Q.val (bodyTensorMoment μ S (d : ℕ)) =
          bodyTensorMoment μ S (d : ℕ) := by
  obtain ⟨I, hI⟩ := exists_finset_bodyMoment_stabilizer_degrees_linearEquiv μ S hS hreg h0
  refine ⟨I, ?_⟩
  intro Q
  let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv Q
  have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val := by
    change LinearMap.toMatrix' (Matrix.toLin' Q.val) = Q.val
    exact LinearMap.toMatrix'_toLin' Q.val
  have h := hI e
  rw [hmat] at h
  exact h

end BanachIsometric
