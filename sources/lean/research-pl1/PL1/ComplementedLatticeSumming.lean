import BanLat.Disjoint
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Finite summing estimates for the complemented-lattice classification

The definitions express quantitative absolute summability through universal
bounds on dual evaluations, avoiding a choice of a maximizing functional.
The deep Grothendieck estimates are not assumed as instances or axioms.
-/

noncomputable section
open scoped BigOperators

namespace PL1.ComplementedLattice

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The usual 1-summing inequality, with an explicit upper bound for the
weak 1-norm of each finite family. -/
def OneSummingWith (T : E →L[ℝ] F) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E) (M : ℝ),
    (∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ≤ M) →
    ∑ i, ‖T (x i)‖ ≤ C * M

/-- The usual 2-summing inequality in squared form. -/
def TwoSummingWith (T : E →L[ℝ] F) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E) (M : ℝ), 0 ≤ M →
    (∀ φ : E →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ^ 2 ≤ M ^ 2) →
    ∑ i, ‖T (x i)‖ ^ 2 ≤ C ^ 2 * M ^ 2

end General

section Lattice

variable {E F : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_signed_disjoint_sum (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j))
    (a : Fin n → ℝ) (ha : ∀ i, |a i| = 1) :
    ‖∑ i, a i • x i‖ = ‖∑ i, x i‖ := by
  have hsum : |∑ i, x i| = ∑ i, |x i| := by
    simpa only [one_smul, abs_one] using
      (abs_sum_of_pairwise_isVLDisjoint (α := fun _ => (1 : ℝ)) hx)
  rw [← norm_abs_eq_norm, abs_sum_of_pairwise_isVLDisjoint hx]
  simp only [ha, one_smul]
  rw [← hsum, norm_abs_eq_norm]

/-- The weak 1-norm of a finite disjoint family is exactly the norm of its
sum. This direction suffices for the 1-summing estimate in de Hevia et al.
Proposition 2.1 and needs no lattice structure on the dual. -/
theorem disjoint_dual_sum_le (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) (φ : E →L[ℝ] ℝ) :
    ∑ i, |φ (x i)| ≤ ‖φ‖ * ‖∑ i, x i‖ := by
  classical
  let a : Fin n → ℝ := fun i => if 0 ≤ φ (x i) then 1 else -1
  have ha (i : Fin n) : |a i| = 1 := by dsimp [a]; split <;> norm_num
  have he (i : Fin n) : a i * φ (x i) = |φ (x i)| := by
    dsimp [a]
    split_ifs with hi
    · simp only [one_mul, abs_of_nonneg hi]
    · simp only [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]
  calc
    _ = φ (∑ i, a i • x i) := by simp only [map_sum, map_smul, smul_eq_mul, he]
    _ ≤ |φ (∑ i, a i • x i)| := le_abs_self _
    _ ≤ ‖φ‖ * ‖∑ i, a i • x i‖ := φ.le_opNorm _
    _ = _ := by rw [norm_signed_disjoint_sum n x hx a ha]

theorem disjoint_dual_sum_le_of_norm_le_one (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j))
    (φ : E →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) : ∑ i, |φ (x i)| ≤ ‖∑ i, x i‖ :=
  (disjoint_dual_sum_le n x hx φ).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (norm_nonneg (∑ i, x i)))

theorem OneSummingWith.disjoint_sum_le {T : E →L[ℝ] F} {C : ℝ}
    (hT : OneSummingWith T C) (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, ‖T (x i)‖ ≤ C * ‖∑ i, x i‖ :=
  hT.2 n x ‖∑ i, x i‖ (disjoint_dual_sum_le_of_norm_le_one n x hx)

theorem norm_disjoint_sum_le (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) (a : Fin n → ℝ) :
    ‖∑ i, a i • x i‖ ≤ ‖∑ i, x i‖ * ‖a‖ := by
  have hsum : |∑ i, x i| = ∑ i, |x i| := by
    simpa only [one_smul, abs_one] using
      (abs_sum_of_pairwise_isVLDisjoint (α := fun _ => (1 : ℝ)) hx)
  have hab : |∑ i, a i • x i| ≤ ‖a‖ • |∑ i, x i| := by
    rw [abs_sum_of_pairwise_isVLDisjoint hx, hsum, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact smul_le_smul_of_nonneg_right (norm_le_pi_norm a i) (abs_nonneg _)
  have hnorm := norm_le_norm_of_abs_le_abs (b := ‖a‖ • ∑ i, x i) (by
    simpa only [abs_smul', abs_of_nonneg (norm_nonneg a)] using hab)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), mul_comm] using hnorm

/-- Synthesis of a disjoint family from finite ell-infinity, with its
dimension-independent lattice bound. -/
def disjointSynthesis (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) : (Fin n → ℝ) →L[ℝ] E :=
  (Fintype.linearCombination ℝ x).mkContinuous ‖∑ i, x i‖ (by
    intro a
    simpa only [Fintype.linearCombination_apply] using norm_disjoint_sum_le n x hx a)

theorem norm_disjointSynthesis_le (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ‖disjointSynthesis n x hx‖ ≤ ‖∑ i, x i‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_disjoint_sum_le n x hx)

@[simp] theorem disjointSynthesis_single (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) (i : Fin n) :
    disjointSynthesis n x hx (Pi.single i 1) = x i := by
  change Fintype.linearCombination ℝ x (Pi.single i 1) = x i
  simp

end Lattice

theorem dual_sum_coordinate_units_le (n : ℕ) (φ : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∑ i, |φ (Pi.single i 1)| ≤ ‖φ‖ := by
  classical
  let a : Fin n → ℝ := fun i => if 0 ≤ φ (Pi.single i 1) then 1 else -1
  have ha (i : Fin n) : |a i| = 1 := by dsimp [a]; split <;> norm_num
  have hnorm : ‖a‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => (ha i).le)
  have he (i : Fin n) : a i * φ (Pi.single i 1) = |φ (Pi.single i 1)| := by
    dsimp [a]
    split_ifs with hi
    · simp only [one_mul, abs_of_nonneg hi]
    · simp only [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]
  have hsum : ∑ i, a i • Pi.single i (1 : ℝ) = a := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    _ = φ (∑ i, a i • Pi.single i (1 : ℝ)) := by simp only [map_sum, map_smul, smul_eq_mul, he]
    _ = φ a := by rw [hsum]
    _ ≤ |φ a| := le_abs_self _
    _ ≤ ‖φ‖ * ‖a‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (norm_nonneg φ)

theorem dual_sq_sum_coordinate_units_le_one (n : ℕ)
    (φ : (Fin n → ℝ) →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    ∑ i, |φ (Pi.single i 1)| ^ 2 ≤ (1 : ℝ) ^ 2 := by
  have hh := (dual_sum_coordinate_units_le n φ).trans hφ
  calc
    _ ≤ (∑ i, |φ (Pi.single i 1)|) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hh 2

section TwoSumming
variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- The 2-summing step of Proposition 2.1 for a finite disjoint family.
The summing estimate is an explicit input, not a formalized Grothendieck theorem. -/
theorem disjoint_square_sum_le_of_twoSumming (n : ℕ) (x : Fin n → E)
    (hx : Pairwise fun i j => IsVLDisjoint (x i) (x j)) {C : ℝ}
    (hT : TwoSummingWith (disjointSynthesis n x hx) C) :
    ∑ i, ‖x i‖ ^ 2 ≤ C ^ 2 := by
  simpa only [disjointSynthesis_single, one_pow, mul_one] using
    hT.2 n (fun i => Pi.single i 1) 1 zero_le_one (dual_sq_sum_coordinate_units_le_one n)

end TwoSumming

end PL1.ComplementedLattice
