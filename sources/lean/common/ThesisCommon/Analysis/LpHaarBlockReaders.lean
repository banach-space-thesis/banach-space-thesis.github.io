import ThesisCommon.Analysis.LpHaarSignedBlocks
import ThesisCommon.Analysis.LpHaarDyadicCoefficient

/-! Explicit bounded readers of finite signed Haar blocks. Their
biorthogonality and their action on genuine Haar multipliers are proved
from the actual Haar coefficient functionals. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

def lpHaarSignedBlockReader (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
  (S.card : 𝕜)⁻¹ • ∑ k ∈ S, signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k)

theorem lpHaarSignedBlockReader_apply (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (f : IntervalLp 𝕜 p) :
    lpHaarSignedBlockReader 𝕜 p n S θ f =
      (S.card : 𝕜)⁻¹ * ∑ k ∈ S, signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f) := by
  simp only [lpHaarSignedBlockReader, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  cases θ k <;> simp [signedValue]

theorem lpHaarSignedBlock_coefficient (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (k : Fin (2 ^ n)) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarSignedBlock 𝕜 p n S θ) =
      if k ∈ S then signedValue (θ k) (1 : 𝕜) else 0 := by
  rw [lpHaarSignedBlock, map_sum]
  have hterm (j : Fin (2 ^ n)) :
      lpHaarDyadicCoefficient 𝕜 p n k (signedValue (θ j) (lpHaarDyadic 𝕜 p n j)) =
        if k = j then signedValue (θ j) (1 : 𝕜) else 0 := by
    by_cases hkj : k = j <;> cases θ j <;>
      simp [signedValue, lpHaarDyadicCoefficient_apply_level, hkj]
  simp_rw [hterm]
  simp [Finset.sum_ite_eq]

theorem lpHaarSignedBlockReader_self (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (hS : S.Nonempty) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ (lpHaarSignedBlock 𝕜 p n S θ) = 1 := by
  rw [lpHaarSignedBlockReader_apply]
  have hsum : (∑ k ∈ S, signedValue (θ k)
      (lpHaarDyadicCoefficient 𝕜 p n k (lpHaarSignedBlock 𝕜 p n S θ))) = (S.card : 𝕜) := by
    calc
      _ = ∑ _k ∈ S, (1 : 𝕜) := Finset.sum_congr rfl (fun k hk => by
        rw [lpHaarSignedBlock_coefficient, if_pos hk, signedValue_self])
      _ = _ := by simp
  rw [hsum, inv_mul_cancel₀]
  exact_mod_cast (Finset.card_pos.mpr hS).ne'

/-- The diagonal entry of a compressed Haar multiplier is its arithmetic
mean on the selected atoms and is independent of the block signs. -/
theorem lpHaarSignedBlockReader_multiplier (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (D : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (d : Fin (2 ^ n) → 𝕜)
    (hD : ∀ k : Fin (2 ^ n), D (lpHaarDyadic 𝕜 p n k) = d k • lpHaarDyadic 𝕜 p n k) :
    lpHaarSignedBlockReader 𝕜 p n S θ (D (lpHaarSignedBlock 𝕜 p n S θ)) =
      (S.card : 𝕜)⁻¹ * ∑ k ∈ S, d k := by
  rw [lpHaarSignedBlockReader_apply, lpHaarSignedBlock, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hcoef : lpHaarDyadicCoefficient 𝕜 p n k
      (∑ j ∈ S, D (signedValue (θ j) (lpHaarDyadic 𝕜 p n j))) =
      signedValue (θ k) (d k) := by
    rw [map_sum, Finset.sum_eq_single k]
    · cases θ k <;> simp [signedValue, hD, lpHaarDyadicCoefficient_apply_level]
    · intro j _ hjk
      have hkj : k ≠ j := hjk.symm
      cases θ j <;> simp [signedValue, hD, lpHaarDyadicCoefficient_apply_level, hkj]
    · exact fun h => (h hk).elim
  rw [hcoef, signedValue_self]

end ThesisCommon
