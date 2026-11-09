import PL1.PrincipalIdealDual
import PL1.ComplementedLatticeBandEstimates
import PL1.SummingTransport
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Disjoint norming functionals without principal projections

Positive norming functionals are localized using scalar suprema of their
values on genuine lattice truncations. This removes the principal-projection
assumption from the finite summing-to-disjoint-norm estimate.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace PL1.DisjointNormingFunctionals
open PrincipalIdealDual PL1.ComplementedLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

private theorem orderDual_nonneg (ν : StrongDual ℝ E) (hν : 0 ≤ ν) :
    0 ≤ StrongDual.toOrderDualSpace ν := by
  apply OrderBoundedHom.le_iff.mpr
  intro x hx
  exact StrongDual.apply_nonneg_of_nonneg hν hx

def localizationLinear (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a) :
    E →ₗ[ℝ] ℝ :=
  (witOp (orderDual_nonneg ν hν) ha).toLinearMap

theorem localizationLinear_positive (ν : StrongDual ℝ E) (hν : 0 ≤ ν)
    (a : E) (ha : 0 ≤ a) : Positive (localizationLinear ν hν a ha) :=
  witLin_positive (orderDual_nonneg ν hν) ha

theorem localizationLinear_le (ν : StrongDual ℝ E) (hν : 0 ≤ ν)
    (a : E) (ha : 0 ≤ a) (x : E) (hx : 0 ≤ x) : localizationLinear ν hν a ha x ≤ ν x :=
  OrderBoundedHom.le_iff.mp (witOp_le_f (orderDual_nonneg ν hν) ha) x hx

theorem localizationLinear_norm_le (ν : StrongDual ℝ E) (hν : 0 ≤ ν)
    (a : E) (ha : 0 ≤ a) (x : E) : ‖localizationLinear ν hν a ha x‖ ≤ ‖ν‖ * ‖x‖ := by
  calc
    _ = |localizationLinear ν hν a ha x| := Real.norm_eq_abs _
    _ ≤ localizationLinear ν hν a ha |x| :=
      Positive.abs_le_map_abs (localizationLinear_positive ν hν a ha) x
    _ ≤ ν |x| := localizationLinear_le ν hν a ha |x| (abs_nonneg x)
    _ ≤ |ν (|x|)| := le_abs_self _
    _ ≤ ‖ν‖ * ‖|x|‖ := ν.le_opNorm _
    _ = _ := by rw [norm_abs_eq_norm]

/-- A positive contractive localization of a continuous functional. -/
def localization (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a) :
    StrongDual ℝ E :=
  (localizationLinear ν hν a ha).mkContinuous ‖ν‖
    (localizationLinear_norm_le ν hν a ha)

theorem localization_nonneg (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a) :
    0 ≤ localization ν hν a ha :=
  StrongDual.nonneg_iff.mpr (localizationLinear_positive ν hν a ha)

theorem norm_localization_le (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a) :
    ‖localization ν hν a ha‖ ≤ ‖ν‖ :=
  (localizationLinear ν hν a ha).mkContinuous_norm_le (norm_nonneg ν)
    (localizationLinear_norm_le ν hν a ha)

theorem localization_self (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a) :
    localization ν hν a ha a = ν a :=
  witOp_apply_self (orderDual_nonneg ν hν) ha

theorem localization_isLUB (ν : StrongDual ℝ E) (hν : 0 ≤ ν) (a : E) (ha : 0 ≤ a)
    (x : E) (hx : 0 ≤ x) :
    IsLUB (Set.range fun n : ℕ => ν (x ⊓ n • a)) (localization ν hν a ha x) := by
  change IsLUB _ (witLin (orderDual_nonneg ν hν) ha x)
  rw [witLin_apply_nonneg (orderDual_nonneg ν hν) ha hx]
  exact witFun_isLUB (orderDual_nonneg ν hν) ha hx

theorem tendsto_truncation_localization (ν : StrongDual ℝ E) (hν : 0 ≤ ν)
    (a : E) (ha : 0 ≤ a) (x : E) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => ν (x ⊓ n • a)) atTop (𝓝 (localization ν hν a ha x)) := by
  apply tendsto_atTop_isLUB _ (localization_isLUB ν hν a ha x hx)
  intro n m hnm
  apply StrongDual.apply_le_apply_of_nonneg hν
  exact inf_le_inf_left _ (nsmul_le_nsmul_left ha hnm)


/-- Genuine finite truncations inherit disjointness from their generators. -/
theorem truncations_disjoint (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j)) (x : E) (n : ℕ) :
    Pairwise fun i j => IsVLDisjoint (|x| ⊓ n • a i) (|x| ⊓ n • a j) := by
  intro i j hij
  have hbase : IsVLDisjoint (n • a i) (n • a j) := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      ((hd hij).smul_left (n : ℝ)).smul_right (n : ℝ)
  apply (hbase.mono_left ?_).mono_right ?_
  · rw [abs_of_nonneg (le_inf (abs_nonneg x) (nsmul_nonneg (ha i) n)),
      abs_of_nonneg (nsmul_nonneg (ha i) n)]
    exact inf_le_right
  · rw [abs_of_nonneg (le_inf (abs_nonneg x) (nsmul_nonneg (ha j) n)),
      abs_of_nonneg (nsmul_nonneg (ha j) n)]
    exact inf_le_right

theorem norm_sum_truncations_le (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j)) (x : E) (n : ℕ) :
    ‖∑ i, |x| ⊓ n • a i‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  apply abs_disjoint_sum_le d _ (truncations_disjoint d a ha hd x n) x
  intro i
  rw [abs_of_nonneg (le_inf (abs_nonneg x) (nsmul_nonneg (ha i) n))]
  exact inf_le_left

/-- The actual two-summing hypothesis controls every finite truncation level. -/
theorem truncation_square_sum_le (C : ℝ) (hC : 0 ≤ C)
    (hTwo : ∀ (d : ℕ) (T : (Fin d → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j))
    (ν : Fin d → StrongDual ℝ E) (hνnorm : ∀ i, ‖ν i‖ ≤ 1) (x : E) (n : ℕ) :
    ∑ i, (ν i (|x| ⊓ n • a i)) ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
  let y : Fin d → E := fun i => |x| ⊓ n • a i
  have hy := truncations_disjoint d a ha hd x n
  let T := disjointSynthesis d y hy
  have hTnorm : ‖T‖ ≤ ‖x‖ :=
    (norm_disjointSynthesis_le d y hy).trans (norm_sum_truncations_le d a ha hd x n)
  calc
    _ ≤ ∑ i, ‖y i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs, sq_abs, one_mul] using
        pow_le_pow_left₀ (norm_nonneg _) ((ν i).le_of_opNorm_le (hνnorm i) (y i)) 2
    _ ≤ (C * ‖T‖) ^ 2 := disjoint_square_sum_le_of_twoSumming d y hy (hTwo d T)
    _ ≤ (C * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hC (norm_nonneg T))
        (mul_le_mul_of_nonneg_left hTnorm hC) 2
    _ = _ := mul_pow _ _ 2

/-- Scalar monotone convergence supplies the localized square estimate;
no primal vector-lattice supremum or weak completeness is invoked. -/
theorem localization_square_sum_le (C : ℝ) (hC : 0 ≤ C)
    (hTwo : ∀ (d : ℕ) (T : (Fin d → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j))
    (ν : Fin d → StrongDual ℝ E) (hν : ∀ i, 0 ≤ ν i) (hνnorm : ∀ i, ‖ν i‖ ≤ 1)
    (x : E) :
    ∑ i, (localization (ν i) (hν i) (a i) (ha i) x) ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
  have ht : Tendsto (fun n : ℕ => ∑ i, (ν i (|x| ⊓ n • a i)) ^ 2) atTop
      (𝓝 (∑ i, (localization (ν i) (hν i) (a i) (ha i) |x|) ^ 2)) := by
    apply tendsto_finsetSum
    intro i _
    exact (tendsto_truncation_localization (ν i) (hν i) (a i) (ha i) |x| (abs_nonneg x)).pow 2
  have hlim := le_of_tendsto ht (Eventually.of_forall
    (truncation_square_sum_le C hC hTwo d a ha hd ν hνnorm x))
  apply le_trans _ hlim
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (StrongDual.abs_apply_le_apply_abs (localization_nonneg (ν i) (hν i) (a i) (ha i)) x) 2

def coordinates (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (ν : Fin d → StrongDual ℝ E) (hν : ∀ i, 0 ≤ ν i) :
    E →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => localization (ν i) (hν i) (a i) (ha i))

@[simp] theorem coordinates_apply (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (ν : Fin d → StrongDual ℝ E) (hν : ∀ i, 0 ≤ ν i) (x : E) (i : Fin d) :
    coordinates d a ha ν hν x i = localization (ν i) (hν i) (a i) (ha i) x := rfl

theorem norm_coordinates_le (C : ℝ) (hC : 0 ≤ C)
    (hTwo : ∀ (d : ℕ) (T : (Fin d → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j))
    (ν : Fin d → StrongDual ℝ E) (hν : ∀ i, 0 ≤ ν i) (hνnorm : ∀ i, ‖ν i‖ ≤ 1) :
    ‖coordinates d a ha ν hν‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow]
  exact localization_square_sum_le C hC hTwo d a ha hd ν hν hνnorm x

/-- The finite disjoint lower-1 estimate holds without principal projections. -/
theorem positive_disjoint_sum_norm_le (C : ℝ) (hC : 0 ≤ C)
    (hOne : ∀ (d : ℕ) (S : E →L[ℝ] EuclideanSpace ℝ (Fin d)), OneSummingWith S (C * ‖S‖))
    (hTwo : ∀ (d : ℕ) (T : (Fin d → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (d : ℕ) (a : Fin d → E) (ha : ∀ i, 0 ≤ a i)
    (hd : Pairwise fun i j => IsVLDisjoint (a i) (a j)) :
    ∑ i, ‖a i‖ ≤ C ^ 2 * ‖∑ i, a i‖ := by
  choose ν hν hνnorm hνa using fun i => StrongDual.exists_positive_dual_norming (ha i)
  let S := coordinates d a ha ν hν
  have hSnorm : ‖S‖ ≤ C := norm_coordinates_le C hC hTwo d a ha hd ν hν hνnorm
  have hdiag (i : Fin d) : ‖a i‖ ≤ ‖S (a i)‖ := by
    have hentry : S (a i) i = ‖a i‖ := by
      change localization (ν i) (hν i) (a i) (ha i) (a i) = _
      rw [localization_self, hνa i]
    have h := PiLp.norm_apply_le (S (a i)) i
    simpa only [hentry, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  calc
    _ ≤ ∑ i, ‖S (a i)‖ := Finset.sum_le_sum (fun i _ => hdiag i)
    _ ≤ (C * ‖S‖) * ‖∑ i, a i‖ := (hOne d S).disjoint_sum_le d a hd
    _ ≤ C ^ 2 * ‖∑ i, a i‖ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSnorm hC) (norm_nonneg _)

theorem disjoint_sum_norm_le (C : ℝ) (hC : 0 ≤ C)
    (hOne : ∀ (d : ℕ) (S : E →L[ℝ] EuclideanSpace ℝ (Fin d)), OneSummingWith S (C * ‖S‖))
    (hTwo : ∀ (d : ℕ) (T : (Fin d → ℝ) →L[ℝ] E), TwoSummingWith T (C * ‖T‖))
    (d : ℕ) (x : Fin d → E) (hd : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, ‖x i‖ ≤ C ^ 2 * ‖∑ i, x i‖ := by
  have habs : Pairwise fun i j => IsVLDisjoint |x i| |x j| := by
    intro i j hij
    simpa only [IsVLDisjoint, abs_abs] using hd hij
  have h := positive_disjoint_sum_norm_le C hC hOne hTwo d (fun i => |x i|)
    (fun i => abs_nonneg _) habs
  have hsum : |∑ i, x i| = ∑ i, |x i| := by
    simpa only [one_smul, abs_one] using
      (abs_sum_of_pairwise_isVLDisjoint (α := fun _ => (1 : ℝ)) hd)
  rw [← hsum, norm_abs_eq_norm] at h
  simpa only [norm_abs_eq_norm] using h


/-- The summing-to-lattice consequence for an actual complemented copy,
with no principal-projection hypothesis on the lattice. -/
theorem disjoint_sum_norm_le_of_complemented_ambient
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : EnfloStarbird.ComplementedCopy ℝ E Y) {G : ℝ} (hG : 0 ≤ G)
    (hOne : ∀ (n : ℕ) (S : Y →L[ℝ] EuclideanSpace ℝ (Fin n)), OneSummingWith S (G * ‖S‖))
    (hTwo : ∀ (n : ℕ) (T : (Fin n → ℝ) →L[ℝ] Y), TwoSummingWith T (G * ‖T‖))
    (d : ℕ) (x : Fin d → E) (hd : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, ‖x i‖ ≤ (G * ‖Q.embedding‖ * ‖Q.retraction‖) ^ 2 * ‖∑ i, x i‖ := by
  obtain ⟨hC, hOneE, hTwoE⟩ := uniform_finite_summing_estimates Q hG hOne hTwo
  exact disjoint_sum_norm_le _ hC hOneE hTwoE d x hd

end PL1.DisjointNormingFunctionals
