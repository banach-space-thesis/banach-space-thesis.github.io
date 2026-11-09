import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v w

/-- The Taylor complexification of a real normed space, realised as the
real-linear maps ℂ → X with their operator norm. A scalar acts by
precomposition with complex multiplication. This norm is rotation invariant
and makes sense for an arbitrary real Banach space. -/
def BanachComplexification (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  ℂ →L[ℝ] X

namespace BanachComplexification
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

instance : NormedAddCommGroup (BanachComplexification X) :=
  inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] X))

instance : NormedSpace ℝ (BanachComplexification X) :=
  inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] X))

instance [CompleteSpace X] : CompleteSpace (BanachComplexification X) :=
  inferInstanceAs (CompleteSpace (ℂ →L[ℝ] X))

def toRealMap (f : BanachComplexification X) : ℂ →L[ℝ] X := f

@[simp] theorem toRealMap_zero : toRealMap (0 : BanachComplexification X) = 0 := rfl
@[simp] theorem toRealMap_add (f g : BanachComplexification X) :
    toRealMap (f + g) = toRealMap f + toRealMap g := rfl
@[simp] theorem toRealMap_neg (f : BanachComplexification X) :
    toRealMap (-f) = -toRealMap f := rfl
@[simp] theorem toRealMap_real_smul (r : ℝ) (f : BanachComplexification X) :
    toRealMap (r • f) = r • toRealMap f := rfl

def scalarOperator (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ

@[simp] theorem scalarOperator_apply (z w : ℂ) : scalarOperator z w = z * w := rfl

instance : Module ℂ (BanachComplexification X) where
  smul z f := (toRealMap f).comp (scalarOperator z)
  one_smul f := by
    change (toRealMap f).comp (scalarOperator 1) = toRealMap f
    ext z
    simp
  mul_smul z w f := by
    change (toRealMap f).comp (scalarOperator (z * w)) =
      ((toRealMap f).comp (scalarOperator w)).comp (scalarOperator z)
    ext a
    simp only [ContinuousLinearMap.comp_apply, scalarOperator_apply]
    congr 1
    ring
  smul_zero z := by
    change (0 : ℂ →L[ℝ] X).comp (scalarOperator z) = 0
    ext a
    rfl
  smul_add z f g := by
    change (toRealMap f + toRealMap g).comp (scalarOperator z) =
      (toRealMap f).comp (scalarOperator z) + (toRealMap g).comp (scalarOperator z)
    ext a
    rfl
  add_smul z w f := by
    change (toRealMap f).comp (scalarOperator (z + w)) =
      (toRealMap f).comp (scalarOperator z) + (toRealMap f).comp (scalarOperator w)
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      scalarOperator_apply, add_mul, map_add]
  zero_smul f := by
    change (toRealMap f).comp (scalarOperator 0) = 0
    ext a
    simp

@[simp] theorem toRealMap_smul_apply (z : ℂ) (f : BanachComplexification X) (w : ℂ) :
    toRealMap (z • f) w = toRealMap f (z * w) := rfl

instance : NormedSpace ℂ (BanachComplexification X) where
  norm_smul_le z f := by
    change ‖(toRealMap f).comp (scalarOperator z)‖ ≤ ‖z‖ * ‖f‖
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg z) (norm_nonneg f))
    intro w
    change ‖toRealMap f (z * w)‖ ≤ _
    calc
      ‖toRealMap f (z * w)‖ ≤ ‖f‖ * ‖z * w‖ := (toRealMap f).le_opNorm _
      _ = (‖z‖ * ‖f‖) * ‖w‖ := by rw [norm_mul]; ring

/-- The original real scalar action agrees with restriction of the new
complex scalar action. -/
instance : IsScalarTower ℝ ℂ (BanachComplexification X) where
  smul_assoc r z f := by
    change (toRealMap f).comp (scalarOperator (r • z)) =
      r • (toRealMap f).comp (scalarOperator z)
    ext w
    simp only [ContinuousLinearMap.comp_apply, scalarOperator_apply,
      ContinuousLinearMap.smul_apply]
    rw [smul_mul_assoc, map_smul]

variable (X)

/-- Evaluation at a fixed scalar is bounded for the actual complexification
norm. -/
def evaluation (z : ℂ) : BanachComplexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun f => toRealMap f z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖z‖ (fun f => by
      simpa only [mul_comm] using (toRealMap f).le_opNorm z)

@[simp] theorem evaluation_apply (z : ℂ) (f : BanachComplexification X) :
    evaluation X z f = toRealMap f z := rfl

/-- The canonical real embedding x ↦ (w ↦ Re(w) x). -/
def embedding : X →L[ℝ] BanachComplexification X :=
  LinearMap.mkContinuous
    { toFun := fun x => Complex.reCLM.smulRight x
      map_add' := by
        intro x y
        change Complex.reCLM.smulRight (x + y) = _
        ext z
        change z.re • (x + y) = z.re • x + z.re • y
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        change Complex.reCLM.smulRight (r • x) = _
        ext z
        simp only [ContinuousLinearMap.smulRight_apply,
          Complex.reCLM_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
    1 (fun x => by
      change ‖Complex.reCLM.smulRight x‖ ≤ 1 * ‖x‖
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro z
      simp only [ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, norm_smul,
        Real.norm_eq_abs, one_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg x))

@[simp] theorem embedding_apply (x : X) (z : ℂ) :
    toRealMap (embedding X x) z = z.re • x := rfl

theorem norm_embedding (x : X) : ‖embedding X x‖ = ‖x‖ := by
  apply le_antisymm
  · have h := (embedding X).le_opNorm x
    have hnorm : ‖embedding X‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ (by norm_num) _
    exact h.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))
  · have h := (toRealMap (embedding X x)).le_opNorm 1
    simpa using h

variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Complexification of a real bounded linear map is postcomposition. -/
def map (T : X →L[ℝ] Y) : BanachComplexification X →L[ℂ] BanachComplexification Y :=
  LinearMap.mkContinuous
    { toFun := fun f => T.comp (toRealMap f)
      map_add' := by
        intro f g
        change T.comp (toRealMap f + toRealMap g) = _
        ext z
        change T (toRealMap f z + toRealMap g z) = T (toRealMap f z) + T (toRealMap g z)
        exact T.map_add _ _
      map_smul' := by
        intro z f
        change T.comp ((toRealMap f).comp (scalarOperator z)) =
          (T.comp (toRealMap f)).comp (scalarOperator z)
        rfl }
    ‖T‖ (fun f => ContinuousLinearMap.opNorm_comp_le T (toRealMap f))

@[simp] theorem map_apply (T : X →L[ℝ] Y) (f : BanachComplexification X) (z : ℂ) :
    toRealMap (map X T f) z = T (toRealMap f z) := rfl

@[simp] theorem map_embedding (T : X →L[ℝ] Y) (x : X) :
    map X T (embedding X x) = embedding Y (T x) := by
  change T.comp (Complex.reCLM.smulRight x) = Complex.reCLM.smulRight (T x)
  ext z
  change T (z.re • x) = z.re • T x
  exact T.map_smul _ _

/-- Complexification preserves the operator norm of a real bounded map. -/
theorem norm_map (T : X →L[ℝ] Y) : ‖map X T‖ = ‖T‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    calc
      ‖T x‖ = ‖embedding Y (T x)‖ := (norm_embedding Y (T x)).symm
      _ = ‖map X T (embedding X x)‖ := by rw [map_embedding]
      _ ≤ ‖map X T‖ * ‖embedding X x‖ := (map X T).le_opNorm _
      _ = ‖map X T‖ * ‖x‖ := by rw [norm_embedding]

@[simp] theorem map_id : map X (ContinuousLinearMap.id ℝ X) =
    ContinuousLinearMap.id ℂ (BanachComplexification X) := by
  apply ContinuousLinearMap.ext
  intro f
  change (ContinuousLinearMap.id ℝ X).comp (toRealMap f) = toRealMap f
  ext z
  rfl

variable {Z : Type w} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

@[simp] theorem map_comp (T : X →L[ℝ] Y) (S : Y →L[ℝ] Z) :
    map X (S.comp T) = (map Y S).comp (map X T) := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

end BanachComplexification
end NonCalkinAlgebra
