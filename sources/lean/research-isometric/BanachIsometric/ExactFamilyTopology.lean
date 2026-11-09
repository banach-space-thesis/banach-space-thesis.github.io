import BanachIsometric.SphereHomotopy

/-!
# Tangency supplies the actual homotopy used in Theorem 3.1

The data below are the Lipschitz operator family and its two exact identities.
No nonzero-degree, degree-invariance, or polynomiality theorem is encoded as a
typeclass or a field. We construct the normalised evaluation map and an actual
sphere homotopy to the prescribed normal field.
-/

namespace BanachIsometric

open NormedSpace
open scoped Topology NNReal

variable (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure ExactTangentialFamily (g : V → ℝ) (p : E → ℝ) where
  normal : C(Metric.sphere (0 : V) 1, Metric.sphere (0 : V) 1)
  maps : Metric.sphere (0 : V) 1 → E →L[ℝ] V
  maps_lipschitz : ∃ L : ℝ≥0, LipschitzWith L maps
  tangent : ∀ z y, inner ℝ (maps z y) (normal z).val = 0
  gauge_eq : ∀ z y, g (maps z y) = p y

namespace ExactTangentialFamily

variable {E V} {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)

theorem evaluation_ne_zero (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (z : Metric.sphere (0 : V) 1) : A.maps z y ≠ 0 := by
  intro hzero
  have h := A.gauge_eq z y
  rw [hzero, hg0] at h
  linarith

theorem continuous_evaluation (y : E) :
    Continuous (fun z => A.maps z y) := by
  obtain ⟨L, hL⟩ := A.maps_lipschitz
  exact (ContinuousLinearMap.apply ℝ V y).continuous.comp hL.continuous

/-- The paper's actual `w_y(z) = A_z y / ‖A_z y‖` as a continuous sphere map. -/
noncomputable def direction (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    C(Metric.sphere (0 : V) 1, Metric.sphere (0 : V) 1) where
  toFun z := ⟨normalize (A.maps z y), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      norm_normalize (A.evaluation_ne_zero hg0 hy z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((A.continuous_evaluation y).norm.inv₀
      (fun z => norm_ne_zero_iff.mpr (A.evaluation_ne_zero hg0 hy z))).smul
        (A.continuous_evaluation y)

theorem normal_inner_direction (hg0 : g 0 = 0) {y : E} (hy : 0 < p y)
    (z : Metric.sphere (0 : V) 1) :
    inner ℝ (A.normal z).val ((A.direction hg0 hy) z).val = 0 := by
  change inner ℝ (A.normal z).val (‖A.maps z y‖⁻¹ • A.maps z y) = 0
  have horth : inner ℝ (A.normal z).val (A.maps z y) = 0 := by
    calc
      inner ℝ (A.normal z).val (A.maps z y) = inner ℝ (A.maps z y) (A.normal z).val :=
        real_inner_comm _ _
      _ = 0 := A.tangent z y
  rw [inner_smul_right, horth, mul_zero]

/-- The homotopy underlying `deg w_y = deg φ`, before any degree theory is
invoked. Unlike an assumed invariance equality, this is the actual homotopy. -/
noncomputable def normalDirectionHomotopy (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    ContinuousMap.Homotopy A.normal (A.direction hg0 hy) :=
  orthogonalSphereHomotopy A.normal (A.direction hg0 hy) (A.normal_inner_direction hg0 hy)

theorem normal_homotopic_direction (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    ContinuousMap.Homotopic A.normal (A.direction hg0 hy) :=
  ⟨A.normalDirectionHomotopy hg0 hy⟩

end ExactTangentialFamily

end BanachIsometric
