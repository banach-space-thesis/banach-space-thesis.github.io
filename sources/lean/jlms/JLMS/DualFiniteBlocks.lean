import JLMS.CZeroFiniteBlocks
import JLMS.WeakStarSequenceOperator
import JLMS.CZeroCoordinateExtensions

/-!
# Coordinate dual blocks and their exact phase pairing

Normalized finite ℓ¹ combinations of uniformly bounded coordinate
extensions retain the same bound. Pairing each block with its phase
vector gives one, while disjoint blocks pair to zero. This step is valid
for real and complex scalars.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def dualFiniteBlock (f : ℕ → (X →L[𝕜] 𝕜)) (F : Finset ℕ) (a : ℕ → 𝕜) : X →L[𝕜] 𝕜 :=
  ∑ k ∈ F, a k • f k

theorem norm_dualFiniteBlock_le (f : ℕ → (X →L[𝕜] 𝕜)) (F : Finset ℕ) (a : ℕ → 𝕜)
    {C : ℝ} (hf : ∀ k, ‖f k‖ ≤ C) (ha : ∑ k ∈ F, ‖a k‖ = 1) :
    ‖dualFiniteBlock f F a‖ ≤ C := by
  calc
    _ ≤ ∑ k ∈ F, ‖a k • f k‖ := norm_sum_le _ _
    _ = ∑ k ∈ F, ‖a k‖ * ‖f k‖ := by simp only [norm_smul]
    _ ≤ ∑ k ∈ F, ‖a k‖ * C := Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (hf k) (norm_nonneg _))
    _ = C := by rw [← Finset.sum_mul, ha, one_mul]

theorem dualFiniteBlock_onRange (J : cZero 𝕜 →L[𝕜] X)
    (f : ℕ → (X →L[𝕜] 𝕜)) (hcoord : ∀ k a, f k (J a) = a k)
    (F : Finset ℕ) (a : ℕ → 𝕜) (b : cZero 𝕜) :
    dualFiniteBlock f F a (J b) = ∑ k ∈ F, a k * b k := by
  simp only [dualFiniteBlock, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    hcoord, smul_eq_mul]

theorem dualFiniteBlock_phase_pair (J : cZero 𝕜 →L[𝕜] X)
    (f : ℕ → (X →L[𝕜] 𝕜)) (hcoord : ∀ k a, f k (J a) = a k)
    (F : ℕ → Finset ℕ) (hF : Pairwise fun n m => Disjoint (F n) (F m))
    (a : ℕ → ℕ → 𝕜) (ha : ∀ n, ∑ k ∈ F n, ‖a n k‖ = 1) (n m : ℕ) :
    dualFiniteBlock f (F n) (a n) (J (cZeroFinitePhaseBlock (F m) (a m))) =
      if m = n then 1 else 0 := by
  classical
  rw [dualFiniteBlock_onRange J f hcoord]
  by_cases hmn : m = n
  · subst m
    simp only [ite_true]
    have heq : (∑ k ∈ F n, a n k * cZeroFinitePhaseBlock (F n) (a n) k) =
        (∑ k ∈ F n, ‖a n k‖ : ℝ) := by
      rw [RCLike.ofReal_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [cZeroFinitePhaseBlock_apply, if_pos hk, mul_comm, scalarPhase_mul]
    rw [heq, ha, RCLike.ofReal_one]
  · rw [if_neg hmn]
    apply Finset.sum_eq_zero
    intro k hk
    have hkm : k ∉ F m := fun hm => Finset.disjoint_left.mp (hF (Ne.symm hmn)) hk hm
    simp [hkm]

end JLMS
