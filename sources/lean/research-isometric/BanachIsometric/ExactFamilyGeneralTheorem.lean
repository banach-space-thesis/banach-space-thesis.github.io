import BanachIsometric.ExactFamilyModelTheorem
import BanachIsometric.SphereDegreeIsometricCoordinates

/-!
# The exact-family theorem on the original Euclidean ambient space

Genuine orthonormal coordinates transport the ambient sphere and its degree.
The finite-dimensional model uses an actual continuous linear equivalence.
All polynomial evaluations and the quadratic conclusion are transported back
to the original vectors, norms and real scalar actions.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {g : V → ℝ} {p : E → ℝ}

theorem transportAmbient_continuousNormalDegree {n : ℕ} [NeZero n]
    (A : ExactTangentialFamily E V g p) (e : V ≃L[ℝ] PiolaSpace n) (L : W ≃ₗᵢ[ℝ] V) :
    (A.transportAmbient L).continuousNormalDegree (L.toContinuousLinearEquiv.trans e) =
      A.continuousNormalDegree e :=
  continuousSphereSignedDegree_isometricSphereConjugate e L A.normal

theorem exactFamilyRigidity_original_spaces
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ V)]
    (A : ExactTangentialFamily E V g p)
    (e : V ≃L[ℝ] PiolaSpace (Module.finrank ℝ V))
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (hcont : Continuous g) (hEven : Even (Module.finrank ℝ V))
    (hdegree : A.continuousNormalDegree e ≠ 0) :
    (∃ c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ∀ k : ℕ, ∃ P : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
        P.IsHomogeneous (Module.finrank ℝ V + 2 * k) ∧
        ∀ y : E, MvPolynomial.eval (fun j => c y j) P = p y ^ (Module.finrank ℝ V + 2 * k)) ∧
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  let cV : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃ₗᵢ[ℝ] V :=
    (stdOrthonormalBasis ℝ V).repr.symm
  let cE : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    (euclideanCoordinates (Module.finrank ℝ E)).trans
      (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv
  let B := A.transportAmbient cV
  let C := B.transportModel cE
  have hgB := hg.comp_continuousLinearEquiv cV.toContinuousLinearEquiv
  have hpC := hp.comp_continuousLinearEquiv cE
  have hcontB : Continuous (fun x => g (cV x)) := hcont.comp cV.continuous
  have hdegreeB : B.continuousNormalDegree (cV.toContinuousLinearEquiv.trans e) ≠ 0 := by
    rw [transportAmbient_continuousNormalDegree]
    exact hdegree
  have hdegreeC : C.continuousNormalDegree (cV.toContinuousLinearEquiv.trans e) ≠ 0 := hdegreeB
  constructor
  · refine ⟨cE.symm, fun k => ?_⟩
    obtain ⟨P, hPhom, hP⟩ := C.exists_polynomial_power_of_nonzero_continuousNormalDegree
      volume (cV.toContinuousLinearEquiv.trans e) hpC hgB hcontB hdegreeC k
    refine ⟨P, hPhom, fun y => ?_⟩
    simpa only [cE.apply_symm_apply] using hP (cE.symm y)
  · exact B.exists_posDef_model_quadraticForm_of_nonzero_continuousNormalDegree
      volume (cV.toContinuousLinearEquiv.trans e) hp hgB hcontB hEven hdegreeB

end BanachIsometric.ExactTangentialFamily
