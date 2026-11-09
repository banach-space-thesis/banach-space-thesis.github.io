import BanachIsometric.RadialHomeomorphism
import BanachIsometric.CoordinateOrthogonality
import Mathlib.Topology.Homotopy.HomotopyGroup

/-! Actual radial coordinates between the unit cube and the Euclidean disk.
The coordinate sup norm is an explicit gauge on the genuine Euclidean space;
it is never substituted for the Euclidean inner-product norm. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology unitInterval

def coordinateSupGauge (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖euclideanCoordinates n x‖

theorem coordinateSupGauge_homogeneous (n : ℕ) : IsDefinitePositiveHomogeneous (coordinateSupGauge n) where
  nonneg x := norm_nonneg _
  eq_zero_iff x := by
    change ‖euclideanCoordinates n x‖ = 0 ↔ x = 0
    rw [norm_eq_zero]
    constructor
    · intro h
      apply (euclideanCoordinates n).injective
      simpa only [map_zero] using h
    · rintro rfl
      exact map_zero _
  smul_nonneg t ht x := by
    change ‖euclideanCoordinates n (t • x)‖ = t * ‖euclideanCoordinates n x‖
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

theorem continuous_coordinateSupGauge (n : ℕ) : Continuous (coordinateSupGauge n) :=
  (euclideanCoordinates n).continuous.norm

def centeredCube (n : ℕ) (y : I^ (Fin n)) : Fin n → ℝ := fun i => 2 * (y i : ℝ) - 1

theorem norm_centeredCube_le_one (n : ℕ) (y : I^ (Fin n)) : ‖centeredCube n y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> dsimp [centeredCube] <;> linarith [(y i).property.1, (y i).property.2]

theorem centeredCube_norm_eq_one_iff_boundary (n : ℕ) (y : I^ (Fin n)) :
    ‖centeredCube n y‖ = 1 ↔ y ∈ Cube.boundary (Fin n) := by
  constructor
  · intro he
    by_contra hnot
    have hlt : ‖centeredCube n y‖ < 1 := by
      apply (pi_norm_lt_iff zero_lt_one).mpr
      intro i
      have h0 : (y i : ℝ) ≠ 0 := fun hz => hnot ⟨i, Or.inl (Subtype.ext hz)⟩
      have h1 : (y i : ℝ) ≠ 1 := fun hz => hnot ⟨i, Or.inr (Subtype.ext hz)⟩
      rw [Real.norm_eq_abs, abs_lt]
      have hi0 : 0 < (y i : ℝ) := lt_of_le_of_ne (y i).property.1 (Ne.symm h0)
      have hi1 : (y i : ℝ) < 1 := lt_of_le_of_ne (y i).property.2 h1
      constructor <;> dsimp [centeredCube] <;> linarith
    linarith
  · rintro ⟨i, hi | hi⟩
    · have hle := norm_le_pi_norm (centeredCube n y) i
      have hbound := norm_centeredCube_le_one n y
      norm_num [centeredCube, hi] at hle
      exact le_antisymm hbound hle
    · have hle := norm_le_pi_norm (centeredCube n y) i
      have hbound := norm_centeredCube_le_one n y
      norm_num [centeredCube, hi] at hle
      exact le_antisymm hbound hle

def cubeToEuclideanDisk (n : ℕ) : (Fin n → unitInterval) → closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  intro y
  refine ⟨(radialGaugeHomeomorph (coordinateSupGauge_homogeneous n)
    (continuous_coordinateSupGauge n)).symm ((euclideanCoordinates n).symm (centeredCube n y)), ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖radialGaugeMapInv (coordinateSupGauge n)
    ((euclideanCoordinates n).symm (centeredCube n y))‖ ≤ 1
  rw [norm_radialGaugeMapInv (coordinateSupGauge_homogeneous n)]
  change ‖euclideanCoordinates n ((euclideanCoordinates n).symm (centeredCube n y))‖ ≤ 1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact norm_centeredCube_le_one n y

theorem continuous_cubeToEuclideanDisk (n : ℕ) : Continuous (cubeToEuclideanDisk n) := by
  apply Continuous.subtype_mk
  apply (radialGaugeHomeomorph (coordinateSupGauge_homogeneous n)
    (continuous_coordinateSupGauge n)).symm.continuous.comp
  apply (euclideanCoordinates n).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const

theorem norm_cubeToEuclideanDisk (n : ℕ) (y : I^ (Fin n)) :
    ‖(cubeToEuclideanDisk n y).val‖ = ‖centeredCube n y‖ := by
  change ‖radialGaugeMapInv (coordinateSupGauge n)
    ((euclideanCoordinates n).symm (centeredCube n y))‖ = _
  rw [norm_radialGaugeMapInv (coordinateSupGauge_homogeneous n)]
  change ‖euclideanCoordinates n ((euclideanCoordinates n).symm (centeredCube n y))‖ = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end BanachIsometric
