import LindenstraussRetraction.Definitions
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The anisotropic equivalent norm

The paper's space with norm `max {ε * ‖y‖, ‖Q y‖}` is represented by a closed
subspace of the product with its maximum norm. The original vector `y`
corresponds to `(ε • y, Q y)`. This model inherits its normed-space structure
and completeness from the product, without changing instances on `Y`.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v w

variable {𝕜 : Type v} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {W : Type w} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The closed graph equation `Q a = ε • w`. -/
def anisotropicConstraint (Q : Y →L[𝕜] W) (ε : ℝ) : (Y × W) →L[𝕜] W :=
  Q.comp (ContinuousLinearMap.fst 𝕜 Y W) -
    (ε : 𝕜) • ContinuousLinearMap.snd 𝕜 Y W

/-- A concrete normed model of the paper's equivalent renorming `Y_ε`. -/
abbrev AnisotropicSpace (Q : Y →L[𝕜] W) (ε : ℝ) :=
  LinearMap.ker (anisotropicConstraint Q ε)

/-- The graph is closed; consequently the model is Banach when `Y` and `W`
are Banach. Its `CompleteSpace` instance is inherited from the closed kernel. -/
theorem anisotropicSpace_isClosed (Q : Y →L[𝕜] W) (ε : ℝ) :
    IsClosed (AnisotropicSpace Q ε : Set (Y × W)) :=
  ContinuousLinearMap.isClosed_ker (anisotropicConstraint Q ε)

theorem anisotropicSpace_complete (Q : Y →L[𝕜] W) (ε : ℝ)
    [CompleteSpace Y] [CompleteSpace W] : CompleteSpace (AnisotropicSpace Q ε) :=
  inferInstance

/-- The isometric embedding of the renormed model into the maximum-norm
product used in the manuscript's bidual-norm argument. -/
def anisotropicInclusion (Q : Y →L[𝕜] W) (ε : ℝ) :
    AnisotropicSpace Q ε →ₗᵢ[𝕜] (Y × W) :=
  (AnisotropicSpace Q ε).subtypeₗᵢ

/-- Send the original vector `y` to `(ε • y, Q y)`. -/
def toAnisotropic (Q : Y →L[𝕜] W) (ε : ℝ) : Y →L[𝕜] AnisotropicSpace Q ε :=
  (((ε : 𝕜) • ContinuousLinearMap.id 𝕜 Y).prod Q).codRestrict
    (AnisotropicSpace Q ε) (by
      intro y
      simp [anisotropicConstraint, LinearMap.mem_ker])

@[simp] theorem toAnisotropic_coe (Q : Y →L[𝕜] W) (ε : ℝ) (y : Y) :
    (toAnisotropic Q ε y : Y × W) = ((ε : 𝕜) • y, Q y) := rfl

/-- Recover the original vector from the first graph coordinate. -/
def fromAnisotropic (Q : Y →L[𝕜] W) (ε : ℝ) : AnisotropicSpace Q ε →L[𝕜] Y :=
  (ε : 𝕜)⁻¹ • (ContinuousLinearMap.fst 𝕜 Y W).comp
    (AnisotropicSpace Q ε).subtypeL

@[simp] theorem fromAnisotropic_apply (Q : Y →L[𝕜] W) (ε : ℝ)
    (z : AnisotropicSpace Q ε) : fromAnisotropic Q ε z = (ε : 𝕜)⁻¹ • z.val.1 := rfl

theorem from_toAnisotropic (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε) (y : Y) :
    fromAnisotropic Q ε (toAnisotropic Q ε y) = y := by
  have h : (ε : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (ne_of_gt hε)
  simp [fromAnisotropic_apply, inv_smul_smul₀ h]

theorem to_fromAnisotropic (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    (z : AnisotropicSpace Q ε) : toAnisotropic Q ε (fromAnisotropic Q ε z) = z := by
  have h : (ε : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (ne_of_gt hε)
  have hz : Q z.val.1 = (ε : 𝕜) • z.val.2 := by
    have hz' := z.property
    change Q z.val.1 - (ε : 𝕜) • z.val.2 = 0 at hz'
    exact sub_eq_zero.mp hz'
  apply Subtype.ext
  apply Prod.ext
  · simp [inv_smul_smul₀ h]
  · simp [map_smul, hz, inv_smul_smul₀ h]

/-- The equivalent renorming is continuously linearly isomorphic to `Y`, with
the explicit correspondence used throughout the paper. -/
def anisotropicEquiv (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε) :
    Y ≃L[𝕜] AnisotropicSpace Q ε :=
  ContinuousLinearEquiv.equivOfInverse (toAnisotropic Q ε) (fromAnisotropic Q ε)
    (from_toAnisotropic Q hε) (to_fromAnisotropic Q hε)

@[simp] theorem anisotropicEquiv_apply (Q : Y →L[𝕜] W) {ε : ℝ}
    (hε : 0 < ε) (y : Y) : anisotropicEquiv Q hε y = toAnisotropic Q ε y := rfl

@[simp] theorem anisotropicEquiv_symm_apply (Q : Y →L[𝕜] W) {ε : ℝ}
    (hε : 0 < ε) (z : AnisotropicSpace Q ε) :
    (anisotropicEquiv Q hε).symm z = fromAnisotropic Q ε z := rfl

/-- Equivalent renorming preserves norm-topology separability. -/
theorem anisotropicSpace_separable (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    [TopologicalSpace.SeparableSpace Y] :
    TopologicalSpace.SeparableSpace (AnisotropicSpace Q ε) :=
  (anisotropicEquiv Q hε).surjective.denseRange.separableSpace
    (anisotropicEquiv Q hε).continuous

/-- The exact norm prescribed by the manuscript. -/
theorem norm_toAnisotropic (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 ≤ ε) (y : Y) :
    ‖toAnisotropic Q ε y‖ = max (ε * ‖y‖) ‖Q y‖ := by
  change ‖((ε : 𝕜) • y, Q y)‖ = max (ε * ‖y‖) ‖Q y‖
  rw [Prod.norm_mk, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hε]

theorem anisotropic_norm_lower (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 ≤ ε) (y : Y) :
    ε * ‖y‖ ≤ ‖toAnisotropic Q ε y‖ := by
  rw [norm_toAnisotropic Q hε]
  exact le_max_left _ _

theorem anisotropic_norm_upper (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 ≤ ε) (y : Y) :
    ‖toAnisotropic Q ε y‖ ≤ max ε ‖Q‖ * ‖y‖ := by
  rw [norm_toAnisotropic Q hε]
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_max_left ε ‖Q‖) (norm_nonneg y)
  · exact (Q.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (le_max_right ε ‖Q‖) (norm_nonneg y))

/-- The identity from the renorming back to `Y` has bound `ε⁻¹`. -/
theorem norm_fromAnisotropic_le (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    (z : AnisotropicSpace Q ε) : ‖fromAnisotropic Q ε z‖ ≤ ε⁻¹ * ‖z‖ := by
  have h := anisotropic_norm_lower Q hε.le (fromAnisotropic Q ε z)
  rw [to_fromAnisotropic Q hε] at h
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hε).mpr
  simpa only [mul_comm] using h

/-- The quotient in renormed coordinates is simply the second graph
coordinate. It is contractive for every `ε`. -/
def anisotropicQuotient (Q : Y →L[𝕜] W) (ε : ℝ) : AnisotropicSpace Q ε →L[𝕜] W :=
  (ContinuousLinearMap.snd 𝕜 Y W).comp (AnisotropicSpace Q ε).subtypeL

@[simp] theorem anisotropicQuotient_toAnisotropic (Q : Y →L[𝕜] W) (ε : ℝ) (y : Y) :
    anisotropicQuotient Q ε (toAnisotropic Q ε y) = Q y := rfl

@[simp] theorem quotient_fromAnisotropic (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    (z : AnisotropicSpace Q ε) : Q (fromAnisotropic Q ε z) = anisotropicQuotient Q ε z := by
  have h := congrArg (anisotropicQuotient Q ε) (to_fromAnisotropic Q hε z)
  simpa only [anisotropicQuotient_toAnisotropic] using h

/-- The exact norm formula also holds directly on the renormed model. -/
theorem anisotropic_norm (Q : Y →L[𝕜] W) {ε : ℝ} (hε : 0 < ε)
    (z : AnisotropicSpace Q ε) :
    ‖z‖ = max (ε * ‖fromAnisotropic Q ε z‖) ‖anisotropicQuotient Q ε z‖ := by
  rw [← quotient_fromAnisotropic Q hε z, ← norm_toAnisotropic Q hε.le,
    to_fromAnisotropic Q hε]

theorem anisotropicQuotient_norm_le (Q : Y →L[𝕜] W) (ε : ℝ)
    (z : AnisotropicSpace Q ε) : ‖anisotropicQuotient Q ε z‖ ≤ ‖z‖ :=
  norm_snd_le z.val

theorem anisotropicQuotient_opNorm_le (Q : Y →L[𝕜] W) (ε : ℝ) :
    ‖anisotropicQuotient Q ε‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using anisotropicQuotient_norm_le Q ε z

end LindenstraussRetraction
