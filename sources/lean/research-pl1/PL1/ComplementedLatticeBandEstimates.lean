import PL1.ComplementedLatticeSumming
import PL1.AtomicBandDecomposition

/-! # The finite-band estimate in the AL-renorming argument

This proves the norm estimate underlying Proposition 2.1 of de Hevia et al.
from explicitly quantified 1- and 2-summing estimates. Those deep estimates
are mathematical premises here, not axioms or implicit instances.
-/

noncomputable section
open scoped BigOperators

namespace PL1.ComplementedLattice
open AtomicBandDecomposition

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

theorem disjoint_of_mem_generated {a b y z : E} (hab : IsVLDisjoint a b)
    (hy : y ∈ Band.generated ({a} : Set E)) (hz : z ∈ Band.generated ({b} : Set E)) :
    IsVLDisjoint y z := by
  have hb : Band.generated ({b} : Set E) ≤ Band.disjointComplement ({a} : Set E) := by
    apply Band.generated_le
    intro t ht s hs
    have ht' : t = b := Set.mem_singleton_iff.mp ht
    have hs' : s = a := Set.mem_singleton_iff.mp hs
    rw [ht', hs']
    exact isVLDisjoint_comm.mpr hab
  have ha : Band.generated ({a} : Set E) ≤
      Band.disjointComplement (Band.generated ({b} : Set E) : Set E) := by
    apply Band.generated_le
    intro t ht s hs
    have ht' : t = a := Set.mem_singleton_iff.mp ht
    rw [ht']
    exact isVLDisjoint_comm.mpr (hb hs a (Set.mem_singleton a))
  exact ha hy z hz

/-- An arbitrary finite disjoint family dominated in modulus has its entire
sum dominated by the same modulus. -/
theorem abs_disjoint_sum_le (n : ℕ) (y : Fin n → E)
    (hy : Pairwise fun i j => IsVLDisjoint (y i) (y j))
    (z : E) (hz : ∀ i, |y i| ≤ |z|) : |∑ i, y i| ≤ |z| := by
  have habs : Pairwise fun i j => IsVLDisjoint |y i| |y j| := by
    intro i j hij
    simpa only [IsVLDisjoint, abs_abs] using hy hij
  have hsum : |∑ i, y i| = ∑ i, |y i| := by
    simpa only [one_smul, abs_one] using
      (abs_sum_of_pairwise_isVLDisjoint (α := fun _ => (1 : ℝ)) hy)
  rw [hsum]
  by_cases hn : n = 0
  · subst n
    simpa using abs_nonneg z
  rw [sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg (Nat.pos_of_ne_zero hn)
    (fun i => abs_nonneg (y i)) habs]
  exact Finset.sup'_le _ _ (fun i _ => hz i)

theorem norm_sum_band_projections_le (n : ℕ) (B : Fin n → ProjectionBand E)
    (hB : ∀ i j, i ≠ j → ∀ y ∈ B i, ∀ z ∈ B j, IsVLDisjoint y z) (x : E) :
    ‖∑ i, projection (B i) x‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  apply abs_disjoint_sum_le n _
  · intro i j hij
    exact hB i j hij _ (projection_mem _ _) _ (projection_mem _ _)
  · intro i
    exact (Positive.abs_le_map_abs
      (Positive.zero_le_iff.mp (B i).bandProjection_nonneg) x).trans
      (Positive.le_iff.mp (B i).bandProjection_le_id _ (abs_nonneg x))

def bandCoordinates (n : ℕ) (B : Fin n → ProjectionBand E)
    (φ : Fin n → E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (φ i).comp (projection (B i))))

@[simp] theorem bandCoordinates_apply (n : ℕ) (B : Fin n → ProjectionBand E)
    (φ : Fin n → E →L[ℝ] ℝ) (x : E) (i : Fin n) :
    bandCoordinates n B φ x i = φ i (projection (B i) x) := rfl

theorem norm_bandCoordinates_le (C : ℝ) (hC : 0 ≤ C)
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (n : ℕ) (B : Fin n → ProjectionBand E)
    (hB : ∀ i j, i ≠ j → ∀ y ∈ B i, ∀ z ∈ B j, IsVLDisjoint y z)
    (φ : Fin n → E →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1) :
    ‖bandCoordinates n B φ‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hd : Pairwise fun i j => IsVLDisjoint (projection (B i) x) (projection (B j) x) := by
    intro i j hij
    exact hB i j hij _ (projection_mem _ _) _ (projection_mem _ _)
  let T := disjointSynthesis n (fun i => projection (B i) x) hd
  have hT : ‖T‖ ≤ ‖x‖ :=
    (norm_disjointSynthesis_le n _ hd).trans (norm_sum_band_projections_le n B hB x)
  calc
    _ ≤ ∑ i, ‖projection (B i) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      change (φ i (projection (B i) x)) ^ 2 ≤ _
      have h := (φ i).le_of_opNorm_le (hφ i) (projection (B i) x)
      simpa only [one_mul, Real.norm_eq_abs, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (C * ‖T‖) ^ 2 := disjoint_square_sum_le_of_twoSumming n _ hd (hTwo n T)
    _ ≤ (C * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg T))
        (mul_le_mul_of_nonneg_left hT hC) 2

theorem disjoint_sum_norm_le_of_summing_estimates
    [HasPrincipalProjectionProperty E] (C : ℝ) (hC : 0 ≤ C)
    (hOne : ∀ (n : ℕ) (S : E →L[ℝ] EuclideanSpace ℝ (Fin n)),
      OneSummingWith S (C * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] E),
      TwoSummingWith T (C * ‖T‖))
    (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, ‖x i‖ ≤ C ^ 2 * ‖∑ i, x i‖ := by
  classical
  choose B hB using fun i : Fin n =>
    HasPrincipalProjectionProperty.exists_projectionBand (x i)
  have hBdisj : ∀ i j, i ≠ j → ∀ y ∈ B i, ∀ z ∈ B j, IsVLDisjoint y z := by
    intro i j hij y hy z hz
    exact disjoint_of_mem_generated (hx hij)
      (by change y ∈ (B i : Set E) at hy; rw [hB i] at hy; exact hy)
      (by change z ∈ (B j : Set E) at hz; rw [hB j] at hz; exact hz)
  choose φ hφ hφx using fun i : Fin n => exists_dual_vector'' ℝ (x i)
  let S := bandCoordinates n B φ
  have hS : ‖S‖ ≤ C := norm_bandCoordinates_le C hC hTwo n B hBdisj φ hφ
  have hnorm (i : Fin n) : ‖x i‖ ≤ ‖S (x i)‖ := by
    have hmem : x i ∈ B i := by
      change x i ∈ (B i : Set E)
      rw [show (B i : Set E) = (Band.generated ({x i} : Set E) : Set E) from hB i]
      exact Band.subset_generated _ (Set.mem_singleton _)
    have hcoord : S (x i) i = ‖x i‖ := by
      change φ i (projection (B i) (x i)) = ‖x i‖
      rw [projection_eq_self _ hmem]
      simpa using hφx i
    have h := PiLp.norm_apply_le (S (x i)) i
    simpa only [hcoord, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  calc
    _ ≤ ∑ i, ‖S (x i)‖ := Finset.sum_le_sum (fun i _ => hnorm i)
    _ ≤ (C * ‖S‖) * ‖∑ i, x i‖ := (hOne n S).disjoint_sum_le n x hx
    _ ≤ C ^ 2 * ‖∑ i, x i‖ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC) (norm_nonneg _)

#print axioms disjoint_sum_norm_le_of_summing_estimates

end PL1.ComplementedLattice
