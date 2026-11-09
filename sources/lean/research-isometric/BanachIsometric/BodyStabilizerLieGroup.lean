import BanachIsometric.StabilizerLieGroup

/-! The actual orthogonal body automorphism group is a compact analytic Lie
group on its original matrix-subgroup topology. Its finite-dimensional model
is the actual infinitesimal stabilizer of a constructed finite moment tuple.
No tuple, local chart, or closed-subgroup Lie theorem is an extra premise. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology Matrix.Norms.Operator

abbrev bodyStabilizerLieModel {m : ℕ} (μ : MeasureTheory.Measure (Fin m → ℝ))
    (S : Set (Fin m → ℝ)) (I : Finset ℕ+) :=
  StabilizerLieCoordinates.kernel (tensorTupleLinearRepresentation m I) (bodyTensorTuple μ S I)

theorem exists_compact_analytic_orthogonalBodyStabilizer {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
    ∃ c : ChartedSpace (bodyStabilizerLieModel μ S I) (orthogonalBodyStabilizerSubgroup m S),
      letI := c
      LieGroup (modelWithCornersSelf ℝ (bodyStabilizerLieModel μ S I)) ⊤
        (orthogonalBodyStabilizerSubgroup m S) ∧
      CompactSpace (orthogonalBodyStabilizerSubgroup m S) := by
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer μ S hS hreg h0
  refine ⟨I, ?_⟩
  have hG : orthogonalBodyStabilizerSubgroup m S =
      unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple μ S I) := by
    apply Subgroup.ext
    intro Q
    let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv Q
    have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val := LinearMap.toMatrix'_toLin' Q.val
    simpa only [hmat] using hI e
  letI : CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := compactSpace_orthogonalGroup m
  rw [hG]
  exact StabilizerLieCoordinates.exists_compact_analytic_lieGroup
    (tensorTupleLinearRepresentation m I) (bodyTensorTuple μ S I)
    (contDiff_tensorTupleOrbit m I (bodyTensorTuple μ S I))

end BanachIsometric
