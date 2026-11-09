import BanachIsometric.ExactFamilyTheorem
import BanachIsometric.ExactFamilyModelCoordinates

/-!
# The exact-family conclusion on an arbitrary finite-dimensional model

The model need not be the coordinate type. A genuine continuous linear
equivalence transports the family and pulls the resulting quadratic form
back to the original model and its specified real scalar action.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory

theorem exists_posDef_model_quadraticForm_of_nonzero_continuousNormalDegree
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} [NeZero N] {g : EuclideanSpace ℝ (Fin N) → ℝ} {p : E → ℝ}
    (A : ExactTangentialFamily E (EuclideanSpace ℝ (Fin N)) g p)
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [μ.IsAddHaarMeasure]
    (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] PiolaSpace N)
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even N) (hdegree : A.continuousNormalDegree e ≠ 0) :
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  let c : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    (euclideanCoordinates (Module.finrank ℝ E)).trans
      (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv
  let B := A.transportModel c
  have hpB := hp.comp_continuousLinearEquiv c
  have hdegreeB : B.continuousNormalDegree e ≠ 0 := hdegree
  obtain ⟨Q, hQpos, hQ⟩ := B.exists_posDef_quadraticForm_of_nonzero_continuousNormalDegree
    μ e hpB hg hcont hEven hdegreeB
  refine ⟨Q.comp c.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · intro y hy
    apply hQpos
    intro hz
    change c.symm y = 0 at hz
    apply hy
    simpa only [c.apply_symm_apply, map_zero] using congrArg c hz
  · intro y
    change Q (c.symm y) = p y ^ 2
    simpa only [c.apply_symm_apply] using hQ (c.symm y)

end BanachIsometric.ExactTangentialFamily
