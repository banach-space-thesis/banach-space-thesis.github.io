import PL1.TraceBounds
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Hilbert space bounds for finite partition traces -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.HilbertTraceBounds

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem integral_norm_sign_sum_sq (s : Finset ℕ) (v : ℕ → H) :
    (∫ x, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i‖ ^ 2 ∂Walsh.haar) =
      ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have h := TraceBounds.finiteTrace_eq_sign_average s v
    (fun i => InnerProductSpace.toDual 𝕜 H (v i)) (ContinuousLinearMap.id 𝕜 H)
  have hsum (x : Walsh.Group) :
      (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • InnerProductSpace.toDual 𝕜 H (v i)) =
        InnerProductSpace.toDual 𝕜 H (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i) := by
    simp only [map_sum, map_smulₛₗ, starRingEnd_apply, Walsh.star_scalarCharacter]
  simp only [TraceBounds.finiteTrace, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply_apply, inner_self_eq_norm_sq_to_K] at h
  simp_rw [hsum, InnerProductSpace.toDual_apply_apply, inner_self_eq_norm_sq_to_K] at h
  have hc : ((∑ i ∈ s, ‖v i‖ ^ 2 : ℝ) : 𝕜) =
      ((∫ x, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i‖ ^ 2 ∂Walsh.haar : ℝ) : 𝕜) := by
    simp only [← RCLike.ofReal_pow] at h
    rw [integral_ofReal] at h
    simpa only [RCLike.ofReal_sum] using h
  exact (RCLike.ofReal_injective hc).symm

theorem sum_norm_sq_le_of_sign_bound (s : Finset ℕ) (v : ℕ → H) (C : ℝ)
    (_hC : 0 ≤ C)
    (hv : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i‖ ≤ C) :
    (∑ i ∈ s, ‖v i‖ ^ 2) ≤ C ^ 2 := by
  rw [← integral_norm_sign_sum_sq (𝕜 := 𝕜) s v]
  have hint := integral_mono_of_nonneg (μ := Walsh.haar)
    (ae_of_all _ (fun x => sq_nonneg _)) (integrable_const (C ^ 2))
    (ae_of_all _ (fun x => pow_le_pow_left₀ (norm_nonneg _) (hv x) 2))
  simpa using hint

theorem sum_dual_norm_sq_le_of_sign_bound (s : Finset ℕ) (φ : ℕ → H →L[𝕜] 𝕜)
    (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i‖ ≤ C) :
    (∑ i ∈ s, ‖φ i‖ ^ 2) ≤ C ^ 2 := by
  let v (i : ℕ) : H := (InnerProductSpace.toDual 𝕜 H).symm (φ i)
  have hv : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i‖ ≤ C := by
    intro x
    have heq : (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • v i) =
        (InnerProductSpace.toDual 𝕜 H).symm
          (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i) := by
      simp only [map_sum, map_smulₛₗ, starRingEnd_apply, Walsh.star_scalarCharacter, v]
    rw [heq, LinearIsometryEquiv.norm_map]
    exact hφ x
  simpa only [v, LinearIsometryEquiv.norm_map] using
    sum_norm_sq_le_of_sign_bound (𝕜 := 𝕜) s v C hC hv

theorem norm_sum_dual_apply_le (s : Finset ℕ) (φ : ℕ → H →L[𝕜] 𝕜)
    (v : ℕ → H) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i‖ ≤ C) :
    ‖∑ i ∈ s, φ i (v i)‖ ≤ C * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  calc
    _ ≤ ∑ i ∈ s, ‖φ i (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖φ i‖ * ‖v i‖ := Finset.sum_le_sum (fun i _ => (φ i).le_opNorm _)
    _ ≤ Real.sqrt (∑ i ∈ s, ‖φ i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ C * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_sqrt (sum_dual_norm_sq_le_of_sign_bound s φ C hC hφ)).trans_eq
        (Real.sqrt_sq hC)

section Partition

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))

/-- The square sum of Hilbert dual rows is controlled by the operator norm, without
choosing any L-infinity representative of a Banach dual functional. -/
theorem sum_cell_dual_norm_sq_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (T : H →L[𝕜] Lp 𝕜 1 μ) :
    (∑ i ∈ s, ‖(TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T‖ ^ 2) ≤ ‖T‖ ^ 2 := by
  apply sum_dual_norm_sq_le_of_sign_bound s _ ‖T‖ (norm_nonneg _)
  intro x
  have heq : (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x •
      (TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T) =
      (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x •
        TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply]
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (TraceBounds.norm_sign_cellFunctional_le μ A hA s hdisj x) (norm_nonneg T))

theorem norm_sum_cell_apply_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (T : H →L[𝕜] Lp 𝕜 1 μ) (v : ℕ → H) :
    ‖∑ i ∈ s, TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i (T (v i))‖ ≤
      ‖T‖ * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  calc
    _ ≤ ∑ i ∈ s, ‖(TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T (v i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖(TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T‖ * ‖v i‖ :=
      Finset.sum_le_sum (fun i _ => ContinuousLinearMap.le_opNorm _ _)
    _ ≤ Real.sqrt (∑ i ∈ s, ‖(TraceBounds.cellFunctional (𝕜 := 𝕜) μ A hA i).comp T‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ ‖T‖ * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_sqrt (sum_cell_dual_norm_sq_le μ A hA s hdisj T)).trans_eq
        (Real.sqrt_sq (norm_nonneg T))

end Partition

end PL1.HilbertTraceBounds
