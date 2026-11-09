import BanachIsometric.NormalizedRadialLift

/-!
# Local lifts for covariance-normalized families with actual moment regularity

This form is suitable after a parameter-dependent covariance normalization:
the sets need not retain their original radial coordinates. The inputs concern
their actual finite moment tuples, and the output is an exact body equivalence.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_lipschitz_normalized_body_lift {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : P → Set (EuclideanSpace ℝ (Fin m))) (hcompact : ∀ a, IsCompact (S a))
    (a₀ : P) (hreg : closure (interior (S a₀)) = S a₀) (h0 : μ (S a₀) ≠ 0)
    (hcov : ∀ a, covarianceOperator μ (S a) = ContinuousLinearMap.id ℝ _)
    (hequiv : ∀ a, ∃ e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      e '' S a₀ = S a)
    (hmom : ∀ I : Finset ℕ+, ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a =>
        bodyTensorTuple (coordinateMeasure μ) (coordinateBody (S a)) I) V) :
    ∃ e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
      ∃ U : Set P, ∃ K : ℝ≥0, IsOpen U ∧ a₀ ∈ U ∧
        e a₀ = ContinuousLinearEquiv.refl ℝ _ ∧
        LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) U ∧
        ∀ a ∈ U, e a '' S a₀ = S a := by
  classical
  let ν := coordinateMeasure μ
  letI : ν.IsAddHaarMeasure := coordinateMeasure_isAddHaarMeasure μ
  let T : P → Set (Fin m → ℝ) := fun a => coordinateBody (S a)
  have hT0 : ν (T a₀) ≠ 0 := by
    rw [coordinateMeasure_coordinateBody]
    exact h0
  obtain ⟨I, s, N, hN, KS, hs, hsLip, hLift⟩ :=
    exists_lipschitz_bodyMoment_image_section ν (T a₀)
      (isCompact_coordinateBody (hcompact a₀)) (coordinateBody_regularClosed hreg) hT0
  let M : P → TensorTupleCoordinates m I := fun a => bodyTensorTuple ν (T a) I
  obtain ⟨V, hV, KM, hM⟩ := hmom I
  have hMlip : LipschitzOnWith KM M V := hM
  have hMcont : ContinuousAt M a₀ := hMlip.continuousOn.continuousAt hV
  have hMN : M ⁻¹' N ∈ 𝓝 a₀ := hMcont.preimage_mem_nhds hN
  obtain ⟨U, hUVN, hU, ha₀U⟩ := mem_nhds_iff.mp (inter_mem hV hMN)
  have hUV : U ⊆ V := fun _ h => (hUVN h).1
  have hUN : ∀ a ∈ U, M a ∈ N := fun _ h => (hUVN h).2
  let e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun a => orthogonalEuclideanEquiv (s (M a))
  have hQ : LipschitzOnWith (KS * KM)
      (fun a => ((s (M a)).val : Matrix (Fin m) (Fin m) ℝ)) U :=
    hsLip.comp (hMlip.mono hUV) hUN
  refine ⟨e, U, ‖matrixEuclideanOperator m‖₊ * (KS * KM), hU, ha₀U, ?_, ?_, ?_⟩
  · change orthogonalEuclideanEquiv (s (bodyTensorTuple ν (T a₀) I)) = _
    rw [hs, orthogonalEuclideanEquiv_one]
  · have h := (matrixEuclideanOperator m).lipschitz.lipschitzOnWith.comp hQ
      (fun _ _ => mem_univ _)
    simpa only [← orthogonalEuclideanEquiv_toContinuousLinearMap] using h
  · intro a ha
    apply (orthogonalEuclideanEquiv_image_iff (s (M a)) _ _).mpr
    change (s (M a)).val.mulVec '' T a₀ = T a
    apply hLift (T a) ?_ (hUN a ha)
    obtain ⟨d, hd⟩ := hequiv a
    exact exists_orthogonal_coordinate_image_of_covariancePosition μ (hcompact a₀)
      (hcov a₀) (hcov a) d hd

end
end BanachIsometric
