import ThesisCommon.Analysis.GowersMaureyContinuousBadVectors
import ThesisCommon.Analysis.GowersMaureyLocalOperatorOrbit
import ThesisCommon.Analysis.RectangularOperatorFixedPoint

/-! Source Lemma 9 for the actual shift space and every actual subspace.
The local conclusion of Lemma 8 and the constructed continuous bad vectors
contradict the checked compact-convex fixed-point theorem. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_operator_orbit_seminorm_approximation (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∃ V ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜)
      (fun a : spreadParameterSquare m => (completedSpread D a.val.1 a.val.2).comp Y.subtypeL) m,
      blockOperatorSeminorm D Y (T-V) ≤ 17*ε := by
  classical
  letI : NormedSpace ℝ (ShiftSpace D) := NormedSpace.restrictScalars ℝ 𝕜 (ShiftSpace D)
  letI : IsScalarTower ℝ 𝕜 (ShiftSpace D) := RestrictScalars.isScalarTower ℝ 𝕜 (ShiftSpace D)
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  letI : IsScalarTower ℝ 𝕜 Y := RestrictScalars.isScalarTower ℝ 𝕜 Y
  obtain ⟨m,hm,hlocal⟩ := exists_local_operator_orbit_approximation D Y T hε
  refine ⟨m,hm,?_⟩
  let U (a : spreadParameterSquare m) : Y →L[𝕜] ShiftSpace D :=
    (completedSpread D a.val.1 a.val.2).comp Y.subtypeL
  let A := finiteAbsoluteConvexOrbit (𝕜 := 𝕜) U m
  by_contra hno
  push_neg at hno
  have hbad : ∀ V ∈ A, 17*ε < blockOperatorSeminorm D Y (T-V) := hno
  obtain ⟨y,hy⟩ := exists_continuous_bad_vectors_on_compact D Y T A
    (isCompact_finiteAbsoluteConvexOrbit U m) hε hbad m m hm
  have hlocal' : ∀ u : A, ∃ v ∈ A, ‖(T-v) (y u)‖ ≤ 8*ε := by
    intro u
    obtain ⟨x,hx,htail,hnorm,_⟩ := hy u
    have hxY : denseEmbedding D x ∈ Y := hx ▸ (y u).property
    obtain ⟨v,hv,hvnorm⟩ := hlocal x hxY hnorm htail
    have hye : y u = (⟨denseEmbedding D x,hxY⟩ : Y) := Subtype.ext hx
    exact ⟨v,hv,by simpa only [hye] using hvnorm⟩
  obtain ⟨u,hu⟩ := finite_rectangular_operator_orbit_fixed_point U (m : ℝ)
    (Nat.cast_nonneg m) T y y.continuous (8*ε) hlocal'
  obtain ⟨_,_,_,_,hlarge⟩ := hy u
  exact (not_lt_of_ge hu) hlarge

end ThesisCommon.GowersMaurey
