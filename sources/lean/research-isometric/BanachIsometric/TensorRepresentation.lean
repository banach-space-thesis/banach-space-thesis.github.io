import BanachIsometric.OrthogonalStabilizer
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
# Genuine tensor-power and finite moment-tuple representations

The matrix whose entries are products of `r` input-matrix entries is the
ordinary tensor-power representation in ordered coordinates. Its multiplicative,
identity and transpose laws are proved by finite sums and products. A selected
finite tuple of degrees is represented by the corresponding block-diagonal
matrix, on a finite-dimensional real coordinate space.

This is representation groundwork for the orbit/local-section step. No local
section, orbit-manifold, or inverse-Lipschitz conclusion is assumed.
-/

namespace BanachIsometric

abbrev TensorCoordinateIndex (m r : ℕ) := Fin r → Fin m
abbrev TensorCoordinates (m r : ℕ) := TensorCoordinateIndex m r → ℝ

/-- The full matrix of the `r`-fold tensor power of a real matrix. -/
noncomputable def tensorPowerMatrix (m r : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (TensorCoordinateIndex m r) (TensorCoordinateIndex m r) ℝ :=
  fun out inp => ∏ k : Fin r, A (out k) (inp k)

@[simp] theorem tensorPowerMatrix_one (m r : ℕ) :
    tensorPowerMatrix m r (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  classical
  ext out inp
  simp [tensorPowerMatrix, Matrix.one_apply, Finset.prod_boole, funext_iff]

theorem tensorPowerMatrix_mul {m r : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    tensorPowerMatrix m r (A * B) = tensorPowerMatrix m r A * tensorPowerMatrix m r B := by
  classical
  ext out inp
  change (∏ k : Fin r, ∑ j : Fin m, A (out k) j * B j (inp k)) =
    ∑ mid : Fin r → Fin m,
      (∏ k : Fin r, A (out k) (mid k)) * ∏ k : Fin r, B (mid k) (inp k)
  calc
    (∏ k : Fin r, ∑ j : Fin m, A (out k) j * B j (inp k)) =
        ∑ mid : Fin r → Fin m, ∏ k : Fin r, A (out k) (mid k) * B (mid k) (inp k) := by
      simpa using Finset.prod_univ_sum
        (fun _ : Fin r => (Finset.univ : Finset (Fin m)))
        (fun k j => A (out k) j * B j (inp k))
    _ = _ := by simp only [Finset.prod_mul_distrib]

@[simp] theorem tensorPowerMatrix_transpose {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    tensorPowerMatrix m r A.transpose = (tensorPowerMatrix m r A).transpose := rfl

/-- The coordinate action previously used for the moments is exactly the
linear action of this tensor-power matrix. -/
theorem tensorCoordinateAction_eq_mulVec {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (M : TensorCoordinates m r) :
    tensorCoordinateAction A M = (tensorPowerMatrix m r A).mulVec M := by
  funext out
  unfold tensorCoordinateAction tensorPowerMatrix Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro inp _
  exact mul_comm _ _

@[simp] theorem tensorCoordinateAction_one {m r : ℕ} (M : TensorCoordinates m r) :
    tensorCoordinateAction (1 : Matrix (Fin m) (Fin m) ℝ) M = M := by
  rw [tensorCoordinateAction_eq_mulVec, tensorPowerMatrix_one, Matrix.one_mulVec]

theorem tensorCoordinateAction_mul {m r : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (M : TensorCoordinates m r) :
    tensorCoordinateAction (A * B) M = tensorCoordinateAction A (tensorCoordinateAction B M) := by
  simp only [tensorCoordinateAction_eq_mulVec, tensorPowerMatrix_mul, Matrix.mulVec_mulVec]

theorem tensorCoordinateAction_add {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (M N : TensorCoordinates m r) :
    tensorCoordinateAction A (M + N) = tensorCoordinateAction A M + tensorCoordinateAction A N := by
  simp only [tensorCoordinateAction_eq_mulVec, Matrix.mulVec_add]

theorem tensorCoordinateAction_smul {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) (M : TensorCoordinates m r) :
    tensorCoordinateAction A (c • M) = c • tensorCoordinateAction A M := by
  simp only [tensorCoordinateAction_eq_mulVec, Matrix.mulVec_smul]

theorem tensorCoordinateAction_inverse {m r : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hAB : A * B = 1) (M : TensorCoordinates m r) :
    tensorCoordinateAction A (tensorCoordinateAction B M) = M := by
  rw [← tensorCoordinateAction_mul, hAB, tensorCoordinateAction_one]

/-- The tensor power is a monoid representation on its coordinate matrices. -/
noncomputable def tensorPowerMatrixRepresentation (m r : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →*
      Matrix (TensorCoordinateIndex m r) (TensorCoordinateIndex m r) ℝ where
  toFun := tensorPowerMatrix m r
  map_one' := tensorPowerMatrix_one m r
  map_mul' := tensorPowerMatrix_mul

/-- A matrix acts linearly on column vectors. -/
noncomputable def matrixLinearRepresentation (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Matrix κ κ ℝ →* Module.End ℝ (κ → ℝ) where
  toFun := Matrix.toLin'
  map_one' := Matrix.toLin'_one
  map_mul' := Matrix.toLin'_mul

/-- The tensor powers as actual real linear representations, rather than just
polynomial coordinate formulas. -/
noncomputable def tensorPowerLinearRepresentation (m r : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →* Module.End ℝ (TensorCoordinates m r) :=
  (matrixLinearRepresentation (TensorCoordinateIndex m r)).comp
    (tensorPowerMatrixRepresentation m r)

@[simp] theorem tensorPowerLinearRepresentation_apply {m r : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (M : TensorCoordinates m r) :
    tensorPowerLinearRepresentation m r A M = tensorCoordinateAction A M :=
  (tensorCoordinateAction_eq_mulVec A M).symm

/-- Tensor powers preserve orthogonality, using their product and transpose laws. -/
theorem tensorPowerMatrix_orthogonal {m r : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A * A.transpose = 1) :
    tensorPowerMatrix m r A * (tensorPowerMatrix m r A).transpose = 1 := by
  rw [← tensorPowerMatrix_transpose, ← tensorPowerMatrix_mul, hA, tensorPowerMatrix_one]

/-- A finite moment tuple has one coordinate for every tensor component at
every selected positive degree. -/
abbrev TensorTupleIndex (m : ℕ) (I : Finset ℕ+) :=
  (d : I) × TensorCoordinateIndex m (d.val : ℕ)

abbrev TensorTupleCoordinates (m : ℕ) (I : Finset ℕ+) := TensorTupleIndex m I → ℝ

theorem finiteDimensional_tensorTupleCoordinates (m : ℕ) (I : Finset ℕ+) :
    FiniteDimensional ℝ (TensorTupleCoordinates m I) := inferInstance

/-- The tensor powers on a finite tuple, as a single block-diagonal matrix. -/
noncomputable def tensorTupleMatrix (m : ℕ) (I : Finset ℕ+)
    (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (TensorTupleIndex m I) (TensorTupleIndex m I) ℝ :=
  Matrix.blockDiagonal' (fun d : I => tensorPowerMatrix m (d.val : ℕ) A)

@[simp] theorem tensorTupleMatrix_one (m : ℕ) (I : Finset ℕ+) :
    tensorTupleMatrix m I (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
  unfold tensorTupleMatrix
  simp only [tensorPowerMatrix_one]
  exact Matrix.blockDiagonal'_one

theorem tensorTupleMatrix_mul {m : ℕ} (I : Finset ℕ+)
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    tensorTupleMatrix m I (A * B) = tensorTupleMatrix m I A * tensorTupleMatrix m I B := by
  unfold tensorTupleMatrix
  simp only [tensorPowerMatrix_mul]
  exact Matrix.blockDiagonal'_mul _ _

@[simp] theorem tensorTupleMatrix_transpose {m : ℕ} (I : Finset ℕ+)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    tensorTupleMatrix m I A.transpose = (tensorTupleMatrix m I A).transpose := by
  unfold tensorTupleMatrix
  simp only [tensorPowerMatrix_transpose, Matrix.blockDiagonal'_transpose]

noncomputable def tensorTupleMatrixRepresentation (m : ℕ) (I : Finset ℕ+) :
    Matrix (Fin m) (Fin m) ℝ →* Matrix (TensorTupleIndex m I) (TensorTupleIndex m I) ℝ where
  toFun := tensorTupleMatrix m I
  map_one' := tensorTupleMatrix_one m I
  map_mul' := tensorTupleMatrix_mul I

/-- The finite tuple as a real linear representation on a finite-dimensional
space. Its underlying vector consists of the selected actual moment entries. -/
noncomputable def tensorTupleLinearRepresentation (m : ℕ) (I : Finset ℕ+) :
    Matrix (Fin m) (Fin m) ℝ →* Module.End ℝ (TensorTupleCoordinates m I) :=
  (matrixLinearRepresentation (TensorTupleIndex m I)).comp
    (tensorTupleMatrixRepresentation m I)

theorem tensorTupleMatrix_orthogonal {m : ℕ} (I : Finset ℕ+)
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A * A.transpose = 1) :
    tensorTupleMatrix m I A * (tensorTupleMatrix m I A).transpose = 1 := by
  rw [← tensorTupleMatrix_transpose, ← tensorTupleMatrix_mul, hA, tensorTupleMatrix_one]

/-- Each block of the tuple representation acts by the corresponding actual
tensor-coordinate action, with no mixing of degrees. -/
theorem tensorTupleMatrix_mulVec_apply {m : ℕ} (I : Finset ℕ+)
    (A : Matrix (Fin m) (Fin m) ℝ) (M : TensorTupleCoordinates m I)
    (d : I) (out : TensorCoordinateIndex m (d.val : ℕ)) :
    (tensorTupleMatrix m I A).mulVec M ⟨d, out⟩ =
      tensorCoordinateAction A (fun inp => M ⟨d, inp⟩) out := by
  classical
  unfold tensorTupleMatrix Matrix.mulVec dotProduct
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single d]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    exact congrFun (tensorCoordinateAction_eq_mulVec A (fun inp => M ⟨d, inp⟩)).symm out
  · intro e hed
    apply Finset.sum_eq_zero
    intro inp _
    change Matrix.blockDiagonal' (fun degree : I => tensorPowerMatrix m (degree.val : ℕ) A)
      ⟨d, out⟩ ⟨e, inp⟩ * M ⟨e, inp⟩ = 0
    rw [Matrix.blockDiagonal'_apply_ne
      (fun degree : I => tensorPowerMatrix m (degree.val : ℕ) A) out inp hed.symm,
      zero_mul]

/-- Insert a full family of arrays into the finite selected tuple. -/
def tensorTupleVector (m : ℕ) (I : Finset ℕ+)
    (M : (d : ℕ+) → TensorCoordinates m (d : ℕ)) : TensorTupleCoordinates m I :=
  fun ij => M ij.1.val ij.2

@[simp] theorem tensorTupleLinearRepresentation_apply {m : ℕ} (I : Finset ℕ+)
    (A : Matrix (Fin m) (Fin m) ℝ) (M : TensorTupleCoordinates m I)
    (d : I) (out : TensorCoordinateIndex m (d.val : ℕ)) :
    tensorTupleLinearRepresentation m I A M ⟨d, out⟩ =
      tensorCoordinateAction A (fun inp => M ⟨d, inp⟩) out :=
  tensorTupleMatrix_mulVec_apply I A M d out

/-- Fixing the one finite-dimensional tuple is exactly fixing every selected
tensor, the condition obtained from the finite body-moment theorem. -/
theorem tensorTupleVector_fixed_iff {m : ℕ} (I : Finset ℕ+)
    (A : Matrix (Fin m) (Fin m) ℝ) (M : (d : ℕ+) → TensorCoordinates m (d : ℕ)) :
    tensorTupleLinearRepresentation m I A (tensorTupleVector m I M) = tensorTupleVector m I M ↔
      ∀ d ∈ I, tensorCoordinateAction A (M d) = M d := by
  constructor
  · intro h d hd
    funext out
    have hout := congrFun h ⟨⟨d, hd⟩, out⟩
    simpa only [tensorTupleLinearRepresentation_apply, tensorTupleVector] using hout
  · intro h
    funext ij
    obtain ⟨d, out⟩ := ij
    simpa only [tensorTupleLinearRepresentation_apply, tensorTupleVector] using
      congrFun (h d.val d.property) out

open scoped Matrix.Norms.Operator

/-- Matrix coordinate projections are continuous linear maps for the operator
norm, by finite dimensionality. -/
noncomputable def matrixEntryCLM {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (i : κ) (j : ι) : Matrix κ ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem contDiff_matrix_of_entries {E κ ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (f : E → Matrix κ ι ℝ) (hf : ∀ i j, ContDiff ℝ ⊤ (fun x => f x i j)) :
    ContDiff ℝ ⊤ f := by
  classical
  have heq : f = fun x => ∑ i, ∑ j, f x i j • Matrix.single i j (1 : ℝ) := by
    funext x
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      Matrix.matrix_eq_sum_single (f x)
  rw [heq]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (hf i j).smul contDiff_const

/-- The ambient tensor-power map is smooth because its entries are finite
products of matrix entries. Smoothness is proved, rather than assumed for the
representation used in the local-slice argument. -/
theorem contDiff_tensorPowerMatrix (m r : ℕ) : ContDiff ℝ ⊤ (tensorPowerMatrix m r) := by
  apply contDiff_matrix_of_entries
  intro out inp
  apply contDiff_prod
  intro k _
  exact (matrixEntryCLM (out k) (inp k)).contDiff

theorem contDiff_tensorTupleMatrix (m : ℕ) (I : Finset ℕ+) :
    ContDiff ℝ ⊤ (tensorTupleMatrix m I) := by
  classical
  apply contDiff_matrix_of_entries
  intro out inp
  obtain ⟨d, out⟩ := out
  obtain ⟨e, inp⟩ := inp
  by_cases h : d = e
  · subst e
    simp only [tensorTupleMatrix, Matrix.blockDiagonal'_apply_eq]
    exact (matrixEntryCLM out inp).contDiff.comp (contDiff_tensorPowerMatrix m (d.val : ℕ))
  · simp only [tensorTupleMatrix, Matrix.blockDiagonal'_apply_ne
      (fun degree : I => tensorPowerMatrix m (degree.val : ℕ) _) _ _ h]
    exact contDiff_const

section OneParameter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a one-parameter linear action, a zero orbit derivative at zero forces
the orbit derivative to vanish at every parameter, by the group law and a
translation. There is no global differentiability assumption here. -/
theorem oneParameterOrbit_hasDerivAt_zero
    (ρ : ℝ → V →L[ℝ] V)
    (hadd : ∀ s t : ℝ, ρ (s + t) = (ρ s).comp (ρ t))
    (v : V) (hzero : HasDerivAt (fun t => ρ t v) 0 0) (t : ℝ) :
    HasDerivAt (fun s => ρ s v) 0 t := by
  have hzero' : HasDerivAt (fun s => ρ s v) 0 (t - t) := by simpa using hzero
  have hshift := HasDerivAt.comp_sub_const t t hzero'
  have hlin : HasDerivAt (fun s => ρ t (ρ (s - t) v)) 0 t := by
    simpa only [Function.comp_def, map_zero] using
      (ρ t).hasFDerivAt.comp_hasDerivAt t hshift
  have heq : (fun s => ρ t (ρ (s - t) v)) = (fun s => ρ s v) := by
    funext s
    calc
      ρ t (ρ (s - t) v) = ρ (t + (s - t)) v := by rw [hadd t (s - t)]; rfl
      _ = ρ s v := by
        have hs : t + (s - t) = s := by ring
        rw [hs]
  rwa [heq] at hlin

/-- Infinitesimal stabilisers integrate along a one-parameter linear action.
Only the derivative at zero is a premise; all other zero derivatives and the
constant-orbit conclusion are proved. -/
theorem oneParameterOrbit_fixed_of_hasDerivAt_zero
    (ρ : ℝ → V →L[ℝ] V) (hidentity : ρ 0 = ContinuousLinearMap.id ℝ V)
    (hadd : ∀ s t : ℝ, ρ (s + t) = (ρ s).comp (ρ t))
    (v : V) (hzero : HasDerivAt (fun t => ρ t v) 0 0) (t : ℝ) : ρ t v = v := by
  have hd := oneParameterOrbit_hasDerivAt_zero ρ hadd v hzero
  calc
    ρ t v = ρ 0 v := is_const_of_deriv_eq_zero
      (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    _ = v := by rw [hidentity]; rfl

/-- The same infinitesimal stabiliser theorem for a genuine finite-dimensional
linear representation and any one-parameter curve in its source monoid. Matrix
exponential curves are an application once their usual addition law is supplied.
-/
theorem representationOrbit_fixed_of_hasDerivAt_zero
    [FiniteDimensional ℝ V] {G : Type*} [Monoid G]
    (ρ : G →* Module.End ℝ V) (c : ℝ → G) (hc0 : c 0 = 1)
    (hcadd : ∀ s t : ℝ, c (s + t) = c s * c t)
    (v : V) (hzero : HasDerivAt (fun t => ρ (c t) v) 0 0) (t : ℝ) :
    ρ (c t) v = v := by
  let f : ℝ → V →L[ℝ] V := fun s => LinearMap.toContinuousLinearMap (ρ (c s))
  have hf0 : f 0 = ContinuousLinearMap.id ℝ V := by
    ext w
    change ρ (c 0) w = w
    rw [hc0, map_one]
    rfl
  have hfadd (s u : ℝ) : f (s + u) = (f s).comp (f u) := by
    ext w
    change ρ (c (s + u)) w = ρ (c s) (ρ (c u) w)
    rw [hcadd, map_mul]
    rfl
  exact oneParameterOrbit_fixed_of_hasDerivAt_zero f hf0 hfadd v hzero t

end OneParameter

end BanachIsometric
