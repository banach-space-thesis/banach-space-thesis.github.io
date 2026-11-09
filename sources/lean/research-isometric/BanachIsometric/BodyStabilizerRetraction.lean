import BanachIsometric.AmbientStabilizerRetraction

/-!
# Ambient equivariant Lipschitz retraction onto the actual body group

For an actual compact regular closed body in covariance position, the finite
moment tuple is constructed and its stabilizer is identified with the actual
operator-unit body group. The ambient matrix retraction is transported through
the exact Euclidean operator coordinates, with explicit Lipschitz constants.
-/

namespace BanachIsometric

open Set Filter MeasureTheory
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

set_option maxHeartbeats 800000 in
theorem exists_ambient_lipschitz_body_retraction_covariancePosition {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ U : Set (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      ∃ r : (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) →
        (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)), ∃ L : ℝ≥0,
      IsOpen U ∧ LipschitzOnWith L r U ∧
      (∀ g : bodyAutomorphismGroup S, g.val.val ∈ U) ∧
      (∀ T ∈ U, IsUnit (r T) ∧ r T '' S = S) ∧
      (∀ g : bodyAutomorphismGroup S, r g.val.val = g.val.val) ∧
      (∀ g : bodyAutomorphismGroup S, ∀ T,
        r (g.val.val * T) = g.val.val * r T) ∧
      (∀ g : bodyAutomorphismGroup S, ∀ T ∈ U, g.val.val * T ∈ U) := by
  let ν := coordinateMeasure μ
  letI : ν.IsAddHaarMeasure := coordinateMeasure_isAddHaarMeasure μ
  have hS0 : ν (coordinateBody S) ≠ 0 := by rwa [coordinateMeasure_coordinateBody]
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer ν (coordinateBody S)
    (isCompact_coordinateBody hS) (coordinateBody_regularClosed hreg) hS0
  let M := bodyTensorTuple ν (coordinateBody S) I
  let O := Matrix.orthogonalGroup (Fin m) ℝ
  have hFix : ∀ Q : O, Q.val.mulVec '' coordinateBody S = coordinateBody S ↔
      Q ∈ MulAction.stabilizer O M := by
    intro Q
    let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv Q
    have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val := LinearMap.toMatrix'_toLin' Q.val
    simpa only [hmat] using hI e
  obtain ⟨V, q, KQ, hV, hQLip, hContains, hRange, hFixQ, hEquiv, hInvariant⟩ :=
    exists_ambient_lipschitz_tensor_stabilizer_retraction m I M
  let U : Set (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    euclideanOperatorMatrix m ⁻¹' V
  let r := fun T => matrixEuclideanOperator m (q (euclideanOperatorMatrix m T))
  have hCompose : LipschitzOnWith (KQ * ‖euclideanOperatorMatrix m‖₊)
      (fun T => q (euclideanOperatorMatrix m T)) U :=
    hQLip.comp (euclideanOperatorMatrix m).lipschitz.lipschitzOnWith (fun _ h => h)
  have hrLip : LipschitzOnWith
      (‖matrixEuclideanOperator m‖₊ * (KQ * ‖euclideanOperatorMatrix m‖₊)) r U :=
    (matrixEuclideanOperator m).lipschitz.lipschitzOnWith.comp hCompose (fun _ _ => mem_univ _)
  let Qg : bodyAutomorphismGroup S → O := fun g =>
    (bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC) g).val
  have hQg : ∀ g, Qg g ∈ MulAction.stabilizer O M := fun g => (hFix (Qg g)).mp
    (bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC) g).property
  have hQgVal : ∀ g, (Qg g).val = euclideanOperatorMatrix m g.val.val :=
    bodyAutomorphismToOrthogonal_matrix (μ := μ) (S := S) (hS := hS) (hC := hC)
  refine ⟨U, r, ‖matrixEuclideanOperator m‖₊ * (KQ * ‖euclideanOperatorMatrix m‖₊),
    hV.preimage (euclideanOperatorMatrix m).continuous, hrLip, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    change euclideanOperatorMatrix m g.val.val ∈ V
    rw [← hQgVal g]
    exact hContains (Qg g) (hQg g)
  · intro T hT
    obtain ⟨hUnit, hMoment⟩ := hRange _ hT
    let Q : O := ⟨q (euclideanOperatorMatrix m T), hUnit⟩
    have hBodyQ : Q.val.mulVec '' coordinateBody S = coordinateBody S :=
      (hFix Q).mpr (show Q ∈ MulAction.stabilizer O M from hMoment)
    have hBody : orthogonalEuclideanEquiv Q '' S = S :=
      (orthogonalEuclideanEquiv_image_iff Q S S).mpr hBodyQ
    have hr : r T = (orthogonalEuclideanEquiv Q).toContinuousLinearMap :=
      (orthogonalEuclideanEquiv_toContinuousLinearMap Q).symm
    refine ⟨?_, ?_⟩
    · rw [hr]
      exact ⟨(orthogonalEuclideanEquiv Q).toUnit, rfl⟩
    · rw [hr]
      exact hBody
  · intro g
    change matrixEuclideanOperator m (q (euclideanOperatorMatrix m g.val.val)) = _
    rw [← hQgVal g, hFixQ (Qg g) (hQg g), hQgVal g,
      matrixEuclideanOperator_euclideanOperatorMatrix]
  · intro g T
    change matrixEuclideanOperator m
      (q (euclideanOperatorMatrix m (g.val.val * T))) = _
    rw [euclideanOperatorMatrix_mul, ← hQgVal g, hEquiv (Qg g) (hQg g),
      matrixEuclideanOperator_mul, hQgVal g, matrixEuclideanOperator_euclideanOperatorMatrix]
  · intro g T hT
    change euclideanOperatorMatrix m (g.val.val * T) ∈ V
    rw [euclideanOperatorMatrix_mul, ← hQgVal g]
    exact hInvariant (Qg g) (hQg g) _ hT

end
end BanachIsometric
