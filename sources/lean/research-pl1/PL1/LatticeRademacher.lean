import PL1.LatticeAbsoluteContinuity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite orthogonal fragment estimates

This module supplies the analytic part of the atomless-lattice Rademacher
argument. Fragment partitions and their scalar orthogonality are explicit
inputs; their existence is not assumed as a lattice instance.
-/

noncomputable section
open Filter TopologicalSpace Finset
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- The finite disjoint modulus identity with an arbitrary finite index
type; this extends BanLat's `Fin n` formulation. -/
theorem abs_sum_smul_disjoint {ι : Type*} [Fintype ι] (p : ι → E) (a : ι → ℝ)
    (hd : Pairwise (fun i j => IsVLDisjoint (p i) (p j))) :
    |∑ i, a i • p i| = ∑ i, |a i| • |p i| := by
  classical
  let e := (Fintype.equivFin ι).symm
  have h := abs_sum_of_pairwise_isVLDisjoint (x := fun i => p (e i))
    (α := fun i => a (e i)) (fun i j hij => hd (e.injective.ne hij))
  rw [e.sum_comp (fun i => a i • p i), e.sum_comp (fun i => |a i| • |p i|)] at h
  exact h

/-- Weighted finite Cauchy--Schwarz in the lattice modulus seminorm. -/
theorem dual_abs_sum_sq_le {ι : Type*} [Fintype ι]
    (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (p : ι → E) (a : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hd : Pairwise (fun i j => IsVLDisjoint (p i) (p j))) :
    (φ |∑ i, a i • p i|) ^ 2 ≤ φ (∑ i, p i) * ∑ i, (a i) ^ 2 * φ (p i) := by
  classical
  rw [abs_sum_smul_disjoint p a hd]
  simp_rw [abs_of_nonneg (hp _), map_sum, map_smul, smul_eq_mul]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := fun i => φ (p i)) (g := fun i => a i ^ 2 * φ (p i))
  · intro i _
    exact StrongDual.apply_nonneg_of_nonneg hφ (hp i)
  · intro i _
    exact mul_nonneg (sq_nonneg _) (StrongDual.apply_nonneg_of_nonneg hφ (hp i))
  · intro i _
    rw [mul_pow, sq_abs]
    exact le_of_eq (by ring)

/-- Expanding a finite weighted orthogonal system gives the exact square
sum, without any infinite-dimensional spectral theorem. -/
theorem sum_sq_eq_of_weighted_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (σ : ι → κ → ℝ) (w : κ → ℝ) (W : ℝ)
    (hσ : ∀ i k, (∑ j, w j * σ i j * σ k j) = if i = k then W else 0)
    (a : ι → ℝ) :
    (∑ j, (∑ i, a i * σ i j) ^ 2 * w j) = W * ∑ i, a i ^ 2 := by
  classical
  have hexpand (j : κ) : (∑ i, a i * σ i j) ^ 2 * w j =
      ∑ i, ∑ k, a i * a k * (w j * σ i j * σ k j) := by
    rw [pow_two, sum_mul, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro k _
    ring
  simp_rw [hexpand]
  rw [sum_comm]
  simp_rw [sum_comm (f := fun j k => a _ * a k * (w j * σ _ j * σ k j))]
  simp_rw [← mul_sum, hσ]
  simp only [mul_ite, mul_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  simp [mul_comm, pow_two]

/-- Orthogonal signs on a positive disjoint partition give an actual
lattice estimate for all finite scalar combinations. -/
theorem dual_abs_sum_sq_le_of_orthogonal_fragments
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (u : E)
    (p : κ → E) (hp : ∀ j, 0 ≤ p j)
    (hd : Pairwise (fun i j => IsVLDisjoint (p i) (p j)))
    (hsum : ∑ j, p j = u) (r : ι → E) (σ : ι → κ → ℝ)
    (hr : ∀ i, r i = ∑ j, σ i j • p j)
    (hσ : ∀ i k, (∑ j, φ (p j) * σ i j * σ k j) =
      if i = k then φ u else 0) (a : ι → ℝ) :
    (φ |∑ i, a i • r i|) ^ 2 ≤ (φ u) ^ 2 * ∑ i, a i ^ 2 := by
  classical
  have heq : (∑ i, a i • r i) = ∑ j, (∑ i, a i * σ i j) • p j := by
    simp_rw [hr, smul_sum, smul_smul, sum_smul]
    exact sum_comm
  rw [heq]
  have h := dual_abs_sum_sq_le φ hφ p (fun j => ∑ i, a i * σ i j) hp hd
  rw [hsum, sum_sq_eq_of_weighted_orthogonal σ (fun j => φ (p j)) (φ u) hσ a] at h
  convert h using 1; ring

end PL1.SchurLattice
