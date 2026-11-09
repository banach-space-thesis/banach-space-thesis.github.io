import BanachIsometric.IdentityComponentTransport

/-! The actual operator-unit body group and its identity component are
continuously multiplicatively equivalent to an actual finite-tensor
orthogonal stabilizer. Covariance position and the finite tensor tuple are
constructed internally. These equivalences induce actual homotopy-group
isomorphisms through `identityComponentHomotopyEquiv`. -/

noncomputable section
namespace BanachIsometric
open Set MeasureTheory
open scoped Topology Matrix.Norms.Operator

theorem exists_bodyAutomorphism_tensorStabilizer_equiv_covariancePosition {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
    ∃ f : bodyAutomorphismGroup S ≃*
      unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple (coordinateMeasure μ) (coordinateBody S) I),
      Continuous f ∧ Continuous f.symm := by
  letI := coordinateMeasure_isAddHaarMeasure μ
  have hcoord : coordinateMeasure μ (coordinateBody S) ≠ 0 := by
    rwa [coordinateMeasure_coordinateBody]
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer
    (coordinateMeasure μ) (coordinateBody S) (isCompact_coordinateBody hS)
    (coordinateBody_regularClosed hreg) hcoord
  have hG : orthogonalBodyStabilizerSubgroup m (coordinateBody S) =
      unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple (coordinateMeasure μ) (coordinateBody S) I) := by
    apply Subgroup.ext
    intro Q
    let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv Q
    have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val := LinearMap.toMatrix'_toLin' Q.val
    simpa only [hmat] using hI e
  refine ⟨I, ?_⟩
  rw [← hG]
  exact ⟨bodyAutomorphismOrthogonalMulEquiv (μ := μ) (S := S) (hS := hS) (hC := hC),
    (bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)).continuous,
    (bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)).symm.continuous⟩

theorem exists_bodyAutomorphism_tensorStabilizer_equiv_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
    covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ _ ∧
    ∃ I : Finset ℕ+,
    ∃ f : bodyAutomorphismGroup S ≃*
      unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I),
      Continuous f ∧ Continuous f.symm := by
  obtain ⟨e, he⟩ := exists_covariancePosition μ hS h0
  let T := e '' S
  have hT : IsCompact T := hS.image e.continuous
  have hTreg : closure (interior T) = T := by
    let eh := e.toHomeomorph
    change closure (interior (eh '' S)) = eh '' S
    rw [← eh.image_interior, ← eh.image_closure, hreg]
  have hT0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior T := by
    rw [show interior T = e '' interior S from (e.toHomeomorph.image_interior S).symm]
    exact ⟨0, h0, e.map_zero⟩
  have hμT : μ T ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds μ (mem_interior_iff_mem_nhds.mp hT0)).ne'
  obtain ⟨I, f, hf, hi⟩ :=
    exists_bodyAutomorphism_tensorStabilizer_equiv_covariancePosition μ T hT he hTreg hμT
  let g := bodyAutomorphismConjugation e S T rfl
  let h := bodyAutomorphismConjugationHomeomorph e S T rfl
  refine ⟨e, he, I, g.trans f, ?_, ?_⟩
  · exact hf.comp h.continuous
  · exact h.symm.continuous.comp hi

theorem exists_bodyIdentityComponent_tensorStabilizer_equiv_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
    covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ _ ∧
    ∃ I : Finset ℕ+,
    ∃ f : Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) ≃*
      Subgroup.connectedComponentOfOne
        (unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
          (bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I)),
      Continuous f ∧ Continuous f.symm := by
  obtain ⟨e, he, I, f, hf, hi⟩ :=
    exists_bodyAutomorphism_tensorStabilizer_equiv_of_interior μ S hS hreg h0
  exact ⟨e, he, I, identityComponentMulEquiv f hf hi,
    continuous_identityComponentMulEquiv f hf hi, continuous_symm_identityComponentMulEquiv f hf hi⟩

theorem exists_bodyIdentityComponent_homotopyEquiv_of_interior
    {N : Type*} [DecidableEq N] [Nonempty N] {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
    covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ _ ∧
    ∃ I : Finset ℕ+,
    Nonempty (HomotopyGroup N (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1 ≃*
      HomotopyGroup N (Subgroup.connectedComponentOfOne
        (unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
          (bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I))) 1) := by
  obtain ⟨e, he, I, f, hf, hi⟩ :=
    exists_bodyAutomorphism_tensorStabilizer_equiv_of_interior μ S hS hreg h0
  exact ⟨e, he, I, ⟨identityComponentHomotopyEquiv f hf hi⟩⟩

end BanachIsometric
