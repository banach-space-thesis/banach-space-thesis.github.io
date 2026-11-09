import NonCalkinAlgebra.BanachComplexification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra.BanachComplexification
universe u v
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

def rotation : BanachComplexification X →L[ℝ] BanachComplexification X :=
  (Complex.I • ContinuousLinearMap.id ℂ (BanachComplexification X)).restrictScalars ℝ

@[simp] theorem rotation_apply (f : BanachComplexification X) :
    rotation X f = Complex.I • f := rfl

/-- The imaginary coordinate is -f(i), for the chosen precomposition action.
With this sign, multiplication by i has the usual coordinates (-y,x). -/
def toCoordinates : BanachComplexification X →L[ℝ] X × X :=
  (evaluation X 1).prod (-(evaluation X Complex.I))

@[simp] theorem toCoordinates_apply (f : BanachComplexification X) :
    toCoordinates X f = (toRealMap f 1, -toRealMap f Complex.I) := rfl

def fromCoordinates : (X × X) →L[ℝ] BanachComplexification X :=
  (embedding X).comp (ContinuousLinearMap.fst ℝ X X) +
    (rotation X).comp ((embedding X).comp (ContinuousLinearMap.snd ℝ X X))

theorem fromCoordinates_apply (p : X × X) (z : ℂ) :
    toRealMap (fromCoordinates X p) z = z.re • p.1 - z.im • p.2 := by
  change toRealMap (embedding X p.1 + Complex.I • embedding X p.2) z = _
  rw [toRealMap_add, ContinuousLinearMap.add_apply, embedding_apply,
    toRealMap_smul_apply, embedding_apply]
  simp [Complex.mul_re, sub_eq_add_neg]

/-- A real-linear map on ℂ is determined by its values at 1 and i. -/
theorem toRealMap_eq_re_im (f : BanachComplexification X) (z : ℂ) :
    toRealMap f z = z.re • toRealMap f 1 + z.im • toRealMap f Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  calc
    toRealMap f z = toRealMap f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg _ hz
    _ = _ := by rw [map_add, map_smul, map_smul]

theorem from_to_coordinates (f : BanachComplexification X) :
    fromCoordinates X (toCoordinates X f) = f := by
  change toRealMap (fromCoordinates X (toCoordinates X f)) = toRealMap f
  ext z
  rw [fromCoordinates_apply]
  change z.re • toRealMap f 1 - z.im • (-toRealMap f Complex.I) = toRealMap f z
  rw [smul_neg, sub_neg_eq_add]
  exact (toRealMap_eq_re_im X f z).symm

theorem to_from_coordinates (p : X × X) :
    toCoordinates X (fromCoordinates X p) = p := by
  change (toRealMap (fromCoordinates X p) 1,
    -toRealMap (fromCoordinates X p) Complex.I) = p
  apply Prod.ext
  · change toRealMap (fromCoordinates X p) 1 = p.1
    rw [fromCoordinates_apply]
    simp
  · change -toRealMap (fromCoordinates X p) Complex.I = p.2
    rw [fromCoordinates_apply]
    simp

/-- A bounded real-linear identification with X × X. It does not replace the
rotation-invariant complexification norm by a product norm. -/
def coordinates : BanachComplexification X ≃L[ℝ] X × X where
  toFun := toCoordinates X
  invFun := fromCoordinates X
  map_add' := (toCoordinates X).map_add
  map_smul' := (toCoordinates X).map_smul
  left_inv := from_to_coordinates X
  right_inv := to_from_coordinates X
  continuous_toFun := (toCoordinates X).continuous
  continuous_invFun := (fromCoordinates X).continuous

theorem norm_fromCoordinates_le (p : X × X) :
    ‖fromCoordinates X p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  calc
    ‖fromCoordinates X p‖ = ‖embedding X p.1 + Complex.I • embedding X p.2‖ := rfl
    _ ≤ ‖embedding X p.1‖ + ‖Complex.I • embedding X p.2‖ := norm_add_le _ _
    _ = ‖p.1‖ + ‖p.2‖ := by rw [norm_embedding, norm_smul, Complex.norm_I,
      norm_embedding, one_mul]

theorem norm_toCoordinates_le (f : BanachComplexification X) :
    ‖toCoordinates X f‖ ≤ ‖f‖ := by
  change max ‖toRealMap f 1‖ ‖-toRealMap f Complex.I‖ ≤ ‖f‖
  apply max_le
  · simpa using (toRealMap f).le_opNorm 1
  · simpa using (toRealMap f).le_opNorm Complex.I

variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

@[simp] theorem toCoordinates_map (T : X →L[ℝ] Y) (f : BanachComplexification X) :
    toCoordinates Y (map X T f) =
      (T (toCoordinates X f).1, T (toCoordinates X f).2) := by
  simp only [toCoordinates_apply, map_apply, map_neg]

end NonCalkinAlgebra.BanachComplexification
