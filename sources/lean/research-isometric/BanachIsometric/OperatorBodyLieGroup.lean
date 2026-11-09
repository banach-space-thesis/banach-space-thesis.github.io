import BanachIsometric.BodyStabilizerLieGroup
import BanachIsometric.BodyGroupConjugation
import BanachIsometric.LieGroupHomeomorphTransport

/-! Compact analytic Lie structures on the actual operator-unit body groups.
Actual covariance normalization and the actual continuous multiplicative
coordinate equivalence transport the matrix stabilizer atlas. The original
operator-unit subgroup topology and group operations are kept throughout. -/

noncomputable section
namespace BanachIsometric
open Set MeasureTheory
open scoped Topology Matrix.Norms.Operator

theorem exists_compact_analytic_bodyAutomorphismGroup_covariancePosition {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
    ∃ c : ChartedSpace (bodyStabilizerLieModel (coordinateMeasure μ) (coordinateBody S) I)
        (bodyAutomorphismGroup S),
      letI := c
      LieGroup (modelWithCornersSelf ℝ
        (bodyStabilizerLieModel (coordinateMeasure μ) (coordinateBody S) I)) ⊤
        (bodyAutomorphismGroup S) ∧ CompactSpace (bodyAutomorphismGroup S) := by
  letI := coordinateMeasure_isAddHaarMeasure μ
  have hcoord : coordinateMeasure μ (coordinateBody S) ≠ 0 := by
    rwa [coordinateMeasure_coordinateBody]
  obtain ⟨I, cO, hLie, _hcompact⟩ := exists_compact_analytic_orthogonalBodyStabilizer
    (coordinateMeasure μ) (coordinateBody S) (isCompact_coordinateBody hS)
    (coordinateBody_regularClosed hreg) hcoord
  letI := cO
  letI := hLie
  let f := bodyAutomorphismOrthogonalMulEquiv (μ := μ) (S := S) (hS := hS) (hC := hC)
  let h := bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)
  have hf : Continuous f := h.continuous
  have hi : Continuous f.symm := h.symm.continuous
  refine ⟨I, homeomorphPullbackChartedSpace (mulEquivHomeomorph f hf hi), ?_⟩
  exact ⟨lieGroup_homeomorphPullback f hf hi,
    compactSpace_bodyAutomorphismGroup (μ := μ) (S := S) (hS := hS) (hC := hC)⟩

theorem exists_compact_analytic_bodyAutomorphismGroup_of_interior {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
    covarianceOperator μ (e '' S) = ContinuousLinearMap.id ℝ _ ∧
    ∃ I : Finset ℕ+,
    ∃ c : ChartedSpace (bodyStabilizerLieModel (coordinateMeasure μ) (coordinateBody (e '' S)) I)
        (bodyAutomorphismGroup S),
      letI := c
      LieGroup (modelWithCornersSelf ℝ
        (bodyStabilizerLieModel (coordinateMeasure μ) (coordinateBody (e '' S)) I)) ⊤
        (bodyAutomorphismGroup S) ∧ CompactSpace (bodyAutomorphismGroup S) := by
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
  obtain ⟨I, cT, hLie, _hcompact⟩ :=
    exists_compact_analytic_bodyAutomorphismGroup_covariancePosition μ T hT he hTreg hμT
  letI := cT
  letI := hLie
  let f := bodyAutomorphismConjugation e S T rfl
  let h := bodyAutomorphismConjugationHomeomorph e S T rfl
  have hf : Continuous f := h.continuous
  have hi : Continuous f.symm := h.symm.continuous
  refine ⟨e, he, I, homeomorphPullbackChartedSpace (mulEquivHomeomorph f hf hi), ?_⟩
  exact ⟨lieGroup_homeomorphPullback f hf hi,
    compactSpace_bodyAutomorphismGroup_of_interior μ S hS h0⟩

end BanachIsometric
