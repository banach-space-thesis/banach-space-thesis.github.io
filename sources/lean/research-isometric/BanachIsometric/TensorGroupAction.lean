import BanachIsometric.TensorRepresentation

/-!
# The actual continuous orthogonal-group action on the finite moment tuple

The finite-dimensional tensor representation restricts to the real orthogonal
group. This supplies the `MulAction` and `ContinuousSMul` used in compact orbit
arguments. Its underlying formula is exactly the previously proved moment
transformation law.
-/

namespace BanachIsometric

open scoped Matrix.Norms.Operator

/-- Joint continuity of the actual ambient polynomial representation and its
vector argument, before restriction to the orthogonal group. -/
theorem continuous_tensorTupleLinearRepresentation (m : ℕ) (I : Finset ℕ+) :
    Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I =>
      tensorTupleLinearRepresentation m I p.1 p.2) := by
  have hA : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I =>
      tensorTupleMatrix m I p.1) :=
    (contDiff_tensorTupleMatrix m I).continuous.comp continuous_fst
  change Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × TensorTupleCoordinates m I =>
    (tensorTupleMatrix m I p.1).mulVec p.2)
  exact hA.matrix_mulVec continuous_snd

noncomputable instance tensorTupleOrthogonalMulAction (m : ℕ) (I : Finset ℕ+) :
    MulAction (Matrix.orthogonalGroup (Fin m) ℝ) (TensorTupleCoordinates m I) where
  smul Q M := tensorTupleLinearRepresentation m I Q.val M
  one_smul M := by
    change tensorTupleLinearRepresentation m I 1 M = M
    rw [map_one]
    rfl
  mul_smul Q R M := by
    change tensorTupleLinearRepresentation m I (Q.val * R.val) M =
      tensorTupleLinearRepresentation m I Q.val (tensorTupleLinearRepresentation m I R.val M)
    rw [map_mul]
    rfl

@[simp] theorem tensorTupleOrthogonal_smul_def {m : ℕ} (I : Finset ℕ+)
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) (M : TensorTupleCoordinates m I) :
    Q • M = tensorTupleLinearRepresentation m I Q.val M := rfl

noncomputable instance tensorTupleOrthogonalContinuousSMul (m : ℕ) (I : Finset ℕ+) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin m) ℝ) (TensorTupleCoordinates m I) where
  continuous_smul := by
    have hQ : Continuous (fun p : Matrix.orthogonalGroup (Fin m) ℝ × TensorTupleCoordinates m I =>
        tensorTupleMatrix m I p.1.val) :=
      (contDiff_tensorTupleMatrix m I).continuous.comp (continuous_subtype_val.comp continuous_fst)
    change Continuous (fun p : Matrix.orthogonalGroup (Fin m) ℝ × TensorTupleCoordinates m I =>
      (tensorTupleMatrix m I p.1.val).mulVec p.2)
    exact hQ.matrix_mulVec continuous_snd

end BanachIsometric
