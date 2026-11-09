import BanachIsometric.NormalizedBodyLift

/-!
# Actual moment regularity after varying linear normalization

The image bodies need not have their original radial functions. Their actual
moment tuples instead satisfy the exact tensor transformation law. A smooth
polynomial action and locally Lipschitz operator parameters prove local moment
regularity of the normalized images.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

def euclideanOperatorMatrix (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) →L[ℝ]
      Matrix (Fin m) (Fin m) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => LinearMap.toMatrix'
        ((euclideanCoordinates m).toLinearMap.comp
          (T.toLinearMap.comp (euclideanCoordinates m).symm.toLinearMap))
      map_add' := by
        intro T U
        ext i j
        simp [LinearMap.toMatrix'_apply]
      map_smul' := by
        intro t T
        ext i j
        simp [LinearMap.toMatrix'_apply] }

def coordinateConjugate {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (euclideanCoordinates m).symm.trans (e.trans (euclideanCoordinates m))

theorem coordinateConjugate_toMatrix {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    LinearMap.toMatrix' (coordinateConjugate e).toLinearMap =
      euclideanOperatorMatrix m e.toContinuousLinearMap := rfl

theorem coordinateBody_image {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m))) :
    coordinateBody (e '' S) = coordinateConjugate e '' coordinateBody S := by
  unfold coordinateBody
  rw [image_image, image_image]
  congr 1

theorem bodyTensorTuple_coordinateBody_image {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S) (h0 : μ S ≠ 0)
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) (I : Finset ℕ+) :
    bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e '' S)) I =
      tensorTupleLinearRepresentation m I (euclideanOperatorMatrix m e.toContinuousLinearMap)
        (bodyTensorTuple (coordinateMeasure μ) (coordinateBody S) I) := by
  let ν := coordinateMeasure μ
  letI : ν.IsAddHaarMeasure := coordinateMeasure_isAddHaarMeasure μ
  have hS0 : ν (coordinateBody S) ≠ 0 := by
    rwa [coordinateMeasure_coordinateBody]
  rw [coordinateBody_image]
  funext ij
  obtain ⟨d, out⟩ := ij
  rw [tensorTupleLinearRepresentation_apply]
  have h := congrFun (bodyTensorMoment_image ν (coordinateBody S)
    (isCompact_coordinateBody hS) hS0 (coordinateConjugate e) (r := (d.val : ℕ))) out
  simpa only [coordinateConjugate_toMatrix, bodyTensorTuple, tensorTupleVector] using h

/-- The full tensor action is smooth jointly in its actual input matrix and
its input moment vector. -/
theorem contDiff_tensorTupleEvaluation (m : ℕ) (I : Finset ℕ+) :
    ContDiff ℝ ⊤ (fun p : Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I =>
      tensorTupleLinearRepresentation m I p.1 p.2) := by
  classical
  apply contDiff_pi.mpr
  intro out
  change ContDiff ℝ ⊤ (fun p : Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I =>
    ∑ inp, tensorTupleMatrix m I p.1 out inp * p.2 inp)
  apply ContDiff.sum
  intro inp _
  exact (((matrixEntryCLM out inp).contDiff.comp (contDiff_tensorTupleMatrix m I)).comp
      contDiff_fst).mul
    ((ContinuousLinearMap.proj inp : TensorTupleCoordinates m I →L[ℝ] ℝ).contDiff.comp
      contDiff_snd)

variable {P : Type*} [PseudoMetricSpace P]

/-- Local regularity of moments of the actual image bodies. Both the original
tuple and the normalizing operator are locally Lipschitz inputs; the image
tuple regularity is proved here from the polynomial transformation law. -/
theorem exists_lipschitz_coordinateBody_image_tuple {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : P → Set (EuclideanSpace ℝ (Fin m))) (hcompact : ∀ a, IsCompact (S a))
    (h0 : ∀ a, μ (S a) ≠ 0)
    (e : P → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (a₀ : P)
    (heLip : ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a => (e a).toContinuousLinearMap) V)
    (I : Finset ℕ+)
    (hmom : ∃ V ∈ 𝓝 a₀, ∃ K : ℝ≥0,
      LipschitzOnWith K (fun a =>
        bodyTensorTuple (coordinateMeasure μ) (coordinateBody (S a)) I) V) :
    ∃ U ∈ 𝓝 a₀, ∃ K : ℝ≥0, LipschitzOnWith K (fun a =>
      bodyTensorTuple (coordinateMeasure μ) (coordinateBody (e a '' S a)) I) U := by
  obtain ⟨V₁, hV₁, K₁, he⟩ := heLip
  obtain ⟨V₂, hV₂, K₂, hM⟩ := hmom
  let M : P → TensorTupleCoordinates m I := fun a =>
    bodyTensorTuple (coordinateMeasure μ) (coordinateBody (S a)) I
  let A : P → Matrix (Fin m) (Fin m) ℝ := fun a =>
    euclideanOperatorMatrix m (e a).toContinuousLinearMap
  let H : P → Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I := fun a => (A a, M a)
  let V := V₁ ∩ V₂
  have hV : V ∈ 𝓝 a₀ := inter_mem hV₁ hV₂
  have hA : LipschitzOnWith (‖euclideanOperatorMatrix m‖₊ * K₁) A V :=
    (euclideanOperatorMatrix m).lipschitz.lipschitzOnWith.comp
      (he.mono inter_subset_left) (fun _ _ => mem_univ _)
  have hM' : LipschitzOnWith K₂ M V := hM.mono inter_subset_right
  have hH : LipschitzOnWith (max (‖euclideanOperatorMatrix m‖₊ * K₁) K₂) H V := hA.prodMk hM'
  have hHcont : ContinuousAt H a₀ := hH.continuousOn.continuousAt hV
  obtain ⟨KF, W, hW, hF⟩ :=
    ((contDiff_tensorTupleEvaluation m I).hasStrictFDerivAt
      (x := H a₀) (by simp)).exists_lipschitzOnWith
  let U := V ∩ H ⁻¹' W
  have hU : U ∈ 𝓝 a₀ := inter_mem hV (hHcont.preimage_mem_nhds hW)
  have hcomp := hF.comp (hH.mono (show U ⊆ V from inter_subset_left))
    (fun _ ha => ha.2)
  refine ⟨U, hU, KF * max (‖euclideanOperatorMatrix m‖₊ * K₁) K₂, ?_⟩
  simpa only [bodyTensorTuple_coordinateBody_image μ _ (hcompact _) (h0 _) _ I] using hcomp

end
end BanachIsometric
