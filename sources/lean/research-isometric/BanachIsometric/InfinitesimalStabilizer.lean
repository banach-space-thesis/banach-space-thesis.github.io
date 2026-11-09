import BanachIsometric.TensorRepresentation
import BanachIsometric.BodyMomentStabilizer
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Integrating the actual infinitesimal moment stabilizer

The finite moment tuple is an actual smooth polynomial representation. The
kernel of the derivative of its exponential orbit at zero integrates to a
one-parameter family of stabilizers. The proof derives the scalar derivative
from the Fréchet derivative and then uses the representation group law; it does
not postulate an orbit manifold, a local section, or the desired stabilizer.

All matrix calculus uses the explicit operator norm. Moment vectors have their
ordinary finite-coordinate norm, as in `TensorRepresentation`.
-/

namespace BanachIsometric

open scoped Matrix.Norms.Operator

section General

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A vector in the kernel of the actual derivative of the exponential orbit
generates a full one-parameter subgroup fixing the original vector. -/
theorem representation_exp_fixed_of_fderiv_eq_zero
    (ρ : A →* Module.End ℝ V) (v : V)
    (hdiff : DifferentiableAt ℝ (fun Y : A => ρ (NormedSpace.exp ℝ Y) v) 0)
    (X : A) (hX : fderiv ℝ (fun Y : A => ρ (NormedSpace.exp ℝ Y) v) 0 X = 0)
    (t : ℝ) : ρ (NormedSpace.exp ℝ (t • X)) v = v := by
  have hline : HasDerivAt (fun s : ℝ => s • X) X 0 := by
    simpa only [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hzero : HasDerivAt (fun s : ℝ => ρ (NormedSpace.exp ℝ (s • X)) v) 0 0 := by
    have hd : HasFDerivAt (fun Y : A => ρ (NormedSpace.exp ℝ Y) v)
        (fderiv ℝ (fun Y : A => ρ (NormedSpace.exp ℝ Y) v) 0) ((0 : ℝ) • X) := by
      simpa only [zero_smul] using hdiff.hasFDerivAt
    simpa only [hX] using hd.comp_hasDerivAt 0 hline
  apply representationOrbit_fixed_of_hasDerivAt_zero ρ
    (fun s : ℝ => NormedSpace.exp ℝ (s • X)) ?_ ?_ v hzero t
  · simp only [zero_smul, NormedSpace.exp_zero]
  · intro s u
    change NormedSpace.exp ℝ ((s + u) • X) =
      NormedSpace.exp ℝ (s • X) * NormedSpace.exp ℝ (u • X)
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left s).smul_right u)

end General

/-- The finite tuple orbit is smooth in the ambient input matrix. -/
theorem contDiff_tensorTupleOrbit (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    ContDiff ℝ ⊤ (fun A : Matrix (Fin m) (Fin m) ℝ =>
      tensorTupleLinearRepresentation m I A M) := by
  classical
  apply contDiff_pi.mpr
  intro out
  change ContDiff ℝ ⊤ (fun A : Matrix (Fin m) (Fin m) ℝ =>
    ∑ inp, tensorTupleMatrix m I A out inp * M inp)
  apply ContDiff.sum
  intro inp _
  exact ((matrixEntryCLM out inp).contDiff.comp (contDiff_tensorTupleMatrix m I)).mul
    contDiff_const

/-- The actual exponential orbit of the selected tensor tuple. -/
noncomputable def tensorTupleExponentialOrbit (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) (X : Matrix (Fin m) (Fin m) ℝ) :
    TensorTupleCoordinates m I :=
  tensorTupleLinearRepresentation m I (NormedSpace.exp ℝ X) M

theorem differentiableAt_tensorTupleExponentialOrbit_zero (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    DifferentiableAt ℝ (tensorTupleExponentialOrbit m I M) 0 := by
  have hrep := (contDiff_tensorTupleOrbit m I M).differentiable (by simp)
  exact hrep.differentiableAt.comp 0
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin m) (Fin m) ℝ)).differentiableAt

/-- The infinitesimal action is the actual Fréchet derivative of the concrete
exponential-orbit map at zero, not an abstract replacement for it. -/
noncomputable def tensorTupleInfinitesimalAction (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    Matrix (Fin m) (Fin m) ℝ →L[ℝ] TensorTupleCoordinates m I :=
  fderiv ℝ (tensorTupleExponentialOrbit m I M) 0

theorem tensorTuple_exp_fixed_of_infinitesimal_eq_zero {m : ℕ} (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) (X : Matrix (Fin m) (Fin m) ℝ)
    (hX : tensorTupleInfinitesimalAction m I M X = 0) (t : ℝ) :
    tensorTupleLinearRepresentation m I (NormedSpace.exp ℝ (t • X)) M = M := by
  exact representation_exp_fixed_of_fderiv_eq_zero (tensorTupleLinearRepresentation m I) M
    (differentiableAt_tensorTupleExponentialOrbit_zero m I M) X hX t

/-- The exponential of a real matrix gives an actual linear equivalence on
the original coordinate space. -/
noncomputable def matrixExpLinearEquiv {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  Matrix.toLinearEquiv' (NormedSpace.exp ℝ X) (NormedSpace.invertibleExp ℝ X)

@[simp] theorem matrixExpLinearEquiv_toMatrix {m : ℕ}
    (X : Matrix (Fin m) (Fin m) ℝ) :
    LinearMap.toMatrix' (matrixExpLinearEquiv X).toLinearMap = NormedSpace.exp ℝ X :=
  LinearMap.toMatrix'_toLin' _

/-- Actual body moments assembled into the selected representation vector. -/
noncomputable def bodyTensorTuple {m : ℕ} (μ : MeasureTheory.Measure (Fin m → ℝ))
    (S : Set (Fin m → ℝ)) (I : Finset ℕ+) : TensorTupleCoordinates m I :=
  tensorTupleVector m I (fun d : ℕ+ => bodyTensorMoment μ S (d : ℕ))

/-- The finite tuple theorem, expressed as the stabilizer of one vector in
the actual finite-dimensional linear representation. -/
theorem exists_finset_bodyTensorTuple_stabilizer {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+, ∀ e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ),
      e '' S = S ↔ tensorTupleLinearRepresentation m I
        (LinearMap.toMatrix' e.toLinearMap) (bodyTensorTuple μ S I) = bodyTensorTuple μ S I := by
  obtain ⟨I, hI⟩ :=
    exists_finset_bodyMoment_stabilizer_degrees_linearEquiv μ S hS hreg h0
  refine ⟨I, fun e => ?_⟩
  exact (hI e).trans
    (tensorTupleVector_fixed_iff I (LinearMap.toMatrix' e.toLinearMap)
      (fun d : ℕ+ => bodyTensorMoment μ S (d : ℕ))).symm

/-- For an actual compact regular closed body of positive volume, the kernel
of the derivative of its finite moment-tuple orbit integrates to body
automorphisms. The finite tuple and the equality of sets are both proved. -/
theorem exists_bodyTensorTuple_infinitesimal_stabilizer {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
      (∀ e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ),
        e '' S = S ↔ tensorTupleLinearRepresentation m I
          (LinearMap.toMatrix' e.toLinearMap) (bodyTensorTuple μ S I) = bodyTensorTuple μ S I) ∧
      ∀ X : Matrix (Fin m) (Fin m) ℝ,
        tensorTupleInfinitesimalAction m I (bodyTensorTuple μ S I) X = 0 →
        ∀ t : ℝ, (NormedSpace.exp ℝ (t • X)).mulVec '' S = S := by
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer μ S hS hreg h0
  refine ⟨I, hI, ?_⟩
  intro X hX t
  have hfix := tensorTuple_exp_fixed_of_infinitesimal_eq_zero I (bodyTensorTuple μ S I) X hX t
  have he := (hI (matrixExpLinearEquiv (t • X))).mpr (by
    simpa only [matrixExpLinearEquiv_toMatrix] using hfix)
  exact he

end BanachIsometric
