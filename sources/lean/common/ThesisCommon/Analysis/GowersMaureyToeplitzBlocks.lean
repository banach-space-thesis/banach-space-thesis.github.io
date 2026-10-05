import ThesisCommon.Analysis.GowersMaureyCoordinateLowerBounds
import ThesisCommon.Analysis.GowersMaureyLaurentOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual disjoint coordinate blocks for finite-band Laurent operators.
The images of widely separated unit vectors recover every coefficient
without cancellation. These are concrete test vectors in ShiftSpace. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem toeplitz_block_difference_outside {M i t j : ℕ}
    (hit : i ≠ t) (hj : j < 2 * M + 1) :
    (((2 * M + 1) * i + j : ℕ) : ℤ) - ((2 * M + 1) * t + M : ℕ) < -(M : ℤ) ∨
      (M : ℤ) < (((2 * M + 1) * i + j : ℕ) : ℤ) - ((2 * M + 1) * t + M : ℕ) := by
  rcases lt_or_gt_of_ne hit with hit | hti
  · have hh := Nat.mul_le_mul_left (2*M+1) (show i + 1 ≤ t by omega)
    rw [Nat.mul_add, Nat.mul_one] at hh
    left
    omega
  · have hh := Nat.mul_le_mul_left (2*M+1) (show t + 1 ≤ i by omega)
    rw [Nat.mul_add, Nat.mul_one] at hh
    right
    omega

theorem laurent_block_coordinate (D : ConstructionData 𝕜) (M r : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    (i : Fin r) (j : Fin (2*M+1)) :
    completedCoordinate D ((2*M+1)*i.val+j.val)
      (laurentOperator D a (∑ t : Fin r, basisVector D ((2*M+1)*t.val+M))) =
      a ((j.val : ℤ) - M) := by
  classical
  rw [map_sum, map_sum, Finset.sum_eq_single i]
  · change matrixEntry D _ _ (laurentOperator D a) = _
    rw [matrixEntry_laurentOperator]
    apply congrArg (fun d : ℤ => a d)
    push_cast
    ring
  · intro t _ hti
    change matrixEntry D _ _ (laurentOperator D a) = _
    rw [matrixEntry_laurentOperator]
    exact hband _ (toeplitz_block_difference_outside
      (by intro h; apply hti; exact Fin.ext h.symm) j.isLt)
  · simp

theorem laurent_block_coordinate_sum (D : ConstructionData 𝕜) (M r : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0) :
    (∑ k : Fin (r * (2*M+1)), ‖completedCoordinate D k.val
      (laurentOperator D a (∑ t : Fin r, basisVector D ((2*M+1)*t.val+M)))‖) =
      (r : ℝ) * ∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖ := by
  have he := (finProdFinEquiv : Fin r × Fin (2*M+1) ≃ Fin (r*(2*M+1))).sum_comp
    (fun k => ‖completedCoordinate D k.val
      (laurentOperator D a (∑ t : Fin r, basisVector D ((2*M+1)*t.val+M)))‖)
  rw [← he, Fintype.sum_prod_type]
  have hb : ∀ i : Fin r, ∀ j : Fin (2*M+1),
      ‖completedCoordinate D (finProdFinEquiv (i,j)).val
        (laurentOperator D a (∑ t : Fin r, basisVector D ((2*M+1)*t.val+M)))‖ =
        ‖a ((j.val : ℤ)-M)‖ := by
    intro i j
    have hh := laurent_block_coordinate D M r a hband i j
    change completedCoordinate D ((2*M+1)*i.val+j.val) _ = _ at hh
    change ‖completedCoordinate D (j.val+(2*M+1)*i.val) _‖ = _
    rw [Nat.add_comm, hh]
  simp_rw [hb]
  simp

theorem laurent_band_norm_lower_at_size (D : ConstructionData 𝕜) (M r m : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    (hr : (r : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ)) (Real.exp (D.j (2*m+1) : ℝ))) :
    (logarithmicWeight r / logarithmicWeight ((r * (2*M+1) : ℕ) : ℝ)) *
      (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖) ≤ ‖laurentOperator D a‖ := by
  have hrlarge : (2 : ℝ) ≤ r := by have hh := D.log_size_large (2*m+1); linarith [hr.1]
  have hr2 : 2 ≤ r := by exact_mod_cast hrlarge
  have hrp : (0 : ℝ) < r := by linarith
  have hc : 0 < 2*M+1 := by omega
  have hrc : 2 ≤ r*(2*M+1) := by nlinarith
  have hfr : 0 < logarithmicWeight r := zero_lt_one.trans_le (one_le_logarithmicWeight (by omega))
  have hfc : 0 < logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) :=
    zero_lt_one.trans_le (one_le_logarithmicWeight (by omega))
  let v : ShiftSpace D := ∑ t : Fin r, basisVector D ((2*M+1)*t.val+M)
  have haMono : StrictMono (fun t : Fin r => (2*M+1)*t.val+M) := by
    intro t u htu
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left htu hc) M
  have hv : ‖v‖ ≤ (r : ℝ) / logarithmicWeight r := basisVector_sum_norm_le_div_weight D haMono m hr
  have hcoord := completedCoordinate_sum_norm_le_weight D hrc
    (show StrictMono (fun k : Fin (r*(2*M+1)) => k.val) from fun _ _ h => h)
    (laurentOperator D a v)
  rw [laurent_block_coordinate_sum D M r a hband] at hcoord
  have hb : (r : ℝ) * (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖) ≤
      logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) * (‖laurentOperator D a‖ * (r / logarithmicWeight r)) :=
    hcoord.trans (mul_le_mul_of_nonneg_left
      (((laurentOperator D a).le_opNorm v).trans
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) hfc.le)
  have hcancel : logarithmicWeight r * (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖) ≤
      ‖laurentOperator D a‖ * logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) := by
    apply (mul_le_mul_iff_right₀ hrp).mp
    calc
      _ = ((r : ℝ) * (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖)) * logarithmicWeight r := by ring
      _ ≤ (logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) * (‖laurentOperator D a‖ * (r / logarithmicWeight r))) *
          logarithmicWeight r := mul_le_mul_of_nonneg_right hb hfr.le
      _ = _ := by field_simp
  have heq : (logarithmicWeight r / logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ)) *
      (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖) =
      (logarithmicWeight r * (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖)) /
        logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) := by ring
  rw [heq]
  exact (div_le_iff₀ hfc).mpr hcancel

end ThesisCommon.GowersMaurey
