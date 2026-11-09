import BanachIsometric.SignedCoordinateTransport
import BanachIsometric.SignedFiberCount
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Actual signed full-fiber counts under real continuous linear coordinates

The actual fibers are equivalent by the coordinate map. Determinants of the
actual derivatives are conjugate at every point, including points where the
maps are not differentiable. Finite fibers therefore have the same integer
signed count; infinite fibers remain infinite and both defined counts are
zero. No finite-fiber premise or change of norm is used.
-/

namespace BanachIsometric

open Set MeasureTheory

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coordinates give an equivalence of the entire actual fibers. -/
def coordinateConjugateFiberEquiv (e : E ≃L[ℝ] F) (f : E → E) (S : Set E) (v : E) :
    {x : E // x ∈ S ∧ f x = v} ≃
      {y : F // y ∈ e '' S ∧ coordinateMapConjugate e f y = e v} :=
  e.toEquiv.subtypeEquiv (fun x => by
    constructor
    · intro hx
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      change e (f (e.symm (e x))) = e v
      simpa only [e.symm_apply_apply] using congrArg e hx.2
    · intro hx
      constructor
      · obtain ⟨z, hz, hzx⟩ := hx.1
        exact e.injective hzx ▸ hz
      · apply e.injective
        have hh : e (f (e.symm (e x))) = e v := hx.2
        simpa only [e.symm_apply_apply] using hh)

theorem coordinateConjugate_fiber_finite_iff (e : E ≃L[ℝ] F) (f : E → E)
    (S : Set E) (v : E) :
    {y : F | y ∈ e '' S ∧ coordinateMapConjugate e f y = e v}.Finite ↔
      {x : E | x ∈ S ∧ f x = v}.Finite :=
  (coordinateConjugateFiberEquiv e f S v).set_finite_iff.symm

theorem signedFiberSum_coordinateConjugate (e : E ≃L[ℝ] F) (f : E → E)
    (S : Set E) (v : E) :
    signedFiberSum (coordinateMapConjugate e f) (fderiv ℝ (coordinateMapConjugate e f))
        (e '' S) (e v) = signedFiberSum f (fderiv ℝ f) S v := by
  let ε := coordinateConjugateFiberEquiv e f S v
  unfold signedFiberSum
  rw [← ε.tsum_eq (fun y => jacobianOrientation (fderiv ℝ (coordinateMapConjugate e f)) y.val)]
  apply tsum_congr
  intro x
  change (SignType.sign (fderiv ℝ (coordinateMapConjugate e f) (e x.val)).det : ℝ) =
    (SignType.sign (fderiv ℝ f x.val).det : ℝ)
  rw [det_fderiv_coordinateConjugate]

/-- The total integer count is invariant under coordinates, with no
regular-value or fiber-finiteness assumption. -/
theorem signedFiberCount_coordinateConjugate (e : E ≃L[ℝ] F) (f : E → E)
    (S : Set E) (v : E) :
    signedFiberCount (coordinateMapConjugate e f) (fderiv ℝ (coordinateMapConjugate e f))
        (e '' S) (e v) = signedFiberCount f (fderiv ℝ f) S v := by
  classical
  by_cases hfin : {x : E | x ∈ S ∧ f x = v}.Finite
  · have hfin' := (coordinateConjugate_fiber_finite_iff e f S v).mpr hfin
    have h := signedFiberSum_coordinateConjugate e f S v
    rw [signedFiberSum_eq_coe_signedFiberCount _ _ _ _ hfin',
      signedFiberSum_eq_coe_signedFiberCount _ _ _ _ hfin] at h
    exact_mod_cast h
  · have hfin' : ¬ {y : F | y ∈ e '' S ∧ coordinateMapConjugate e f y = e v}.Finite :=
      fun h => hfin ((coordinateConjugate_fiber_finite_iff e f S v).mp h)
    simp only [signedFiberCount, dif_neg hfin', dif_neg hfin]

section Measures

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Arbitrary almost-everywhere predicates on the actual count transport
without an extra measurability premise on the predicate. -/
theorem ae_signedFiberCount_coordinateConjugate_iff (μ : Measure E)
    (e : E ≃L[ℝ] F) (f : E → E) (S : Set E) (Q : E → ℤ → Prop) :
    (∀ᵐ w ∂Measure.map e μ, Q (e.symm w)
      (signedFiberCount (coordinateMapConjugate e f) (fderiv ℝ (coordinateMapConjugate e f))
        (e '' S) w)) ↔
      ∀ᵐ v ∂μ, Q v (signedFiberCount f (fderiv ℝ f) S v) := by
  have he : MeasurableEmbedding (e : E → F) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [he.ae_map_iff]
  simp only [e.symm_apply_apply, signedFiberCount_coordinateConjugate]

theorem ae_signedFiberCount_eq_on_image_iff (μ : Measure E)
    (e : E ≃L[ℝ] F) (f : E → E) (S U : Set E) (D : ℤ) :
    (∀ᵐ w ∂Measure.map e μ, w ∈ e '' U →
      signedFiberCount (coordinateMapConjugate e f) (fderiv ℝ (coordinateMapConjugate e f))
        (e '' S) w = D) ↔
      ∀ᵐ v ∂μ, v ∈ U → signedFiberCount f (fderiv ℝ f) S v = D := by
  have he : MeasurableEmbedding (e : E → F) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [he.ae_map_iff]
  simp only [signedFiberCount_coordinateConjugate, Set.mem_image, e.injective.eq_iff,
    exists_eq_right]

theorem map_inverse_coordinates (μ : Measure E) (e : E ≃L[ℝ] F) :
    Measure.map e.symm (Measure.map e μ) = μ := by
  rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  simpa only [Function.comp_def, e.symm_apply_apply] using (Measure.map_id (μ := μ))

theorem map_coordinates_isAddHaarMeasure (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃L[ℝ] F) : (Measure.map e μ).IsAddHaarMeasure :=
  e.isAddHaarMeasure_map μ

theorem map_inverse_coordinates_isAddHaarMeasure (ν : Measure F) [ν.IsAddHaarMeasure]
    (e : E ≃L[ℝ] F) : (Measure.map e.symm ν).IsAddHaarMeasure :=
  e.symm.isAddHaarMeasure_map ν

variable [FiniteDimensional ℝ F]

/-- Arbitrary Haar normalizations have the same null sets in finite
dimensions, so the coordinate count transport applies to either chosen Haar
measure, including the ordinary coordinate Lebesgue measure. -/
theorem ae_signedFiberCount_eq_on_image_iff_of_isAddHaarMeasure
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (e : E ≃L[ℝ] F) (f : E → E) (S U : Set E) (D : ℤ) :
    (∀ᵐ w ∂ν, w ∈ e '' U →
      signedFiberCount (coordinateMapConjugate e f) (fderiv ℝ (coordinateMapConjugate e f))
        (e '' S) w = D) ↔
      ∀ᵐ v ∂μ, v ∈ U → signedFiberCount f (fderiv ℝ f) S v = D := by
  letI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have heq : ae ν = ae (Measure.map e μ) := le_antisymm
    (Measure.absolutelyContinuous_isAddHaarMeasure ν (Measure.map e μ)).ae_le
    (Measure.absolutelyContinuous_isAddHaarMeasure (Measure.map e μ) ν).ae_le
  rw [heq]
  exact ae_signedFiberCount_eq_on_image_iff μ e f S U D

end Measures

end

end BanachIsometric
