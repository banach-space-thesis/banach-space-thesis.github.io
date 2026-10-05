import JLMS.L1Restriction

/-!
# Indicator functionals on ℓ¹

Every subset of ℕ defines a norm-at-most-one functional by summing those
coordinates of an ℓ¹ sequence. Its values on the coordinate vectors identify
the subset. Distinct subsets therefore give dual functionals at distance at
least one, the elementary obstruction to separability of the ℓ¹ dual.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

def ellOneIndicatorValues (S : Set ℕ) (a : ellOne 𝕜) (n : ℕ) : 𝕜 :=
  if n ∈ S then a n else 0

theorem summable_ellOneIndicatorValues (S : Set ℕ) (a : ellOne 𝕜) :
    Summable (ellOneIndicatorValues S a) :=
  (ellOneOn_summable_norm a).of_norm_bounded (fun n => by
    by_cases hn : n ∈ S <;> simp [ellOneIndicatorValues, hn])

theorem norm_tsum_ellOneIndicatorValues_le (S : Set ℕ) (a : ellOne 𝕜) :
    ‖∑' n, ellOneIndicatorValues S a n‖ ≤ ‖a‖ := by
  have hbound (n : ℕ) : ‖ellOneIndicatorValues S a n‖ ≤ ‖a n‖ := by
    by_cases hn : n ∈ S <;> simp [ellOneIndicatorValues, hn]
  have hs := (ellOneOn_summable_norm a).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    _ ≤ ∑' n, ‖ellOneIndicatorValues S a n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖a n‖ := hs.tsum_le_tsum hbound (ellOneOn_summable_norm a)
    _ = ‖a‖ := (ellOneOn_norm_eq_tsum a).symm

def ellOneIndicatorFunctional (S : Set ℕ) : ellOne 𝕜 →L[𝕜] 𝕜 :=
  ({ toFun a := ∑' n, ellOneIndicatorValues S a n
     map_add' a b := by
       have heq (n : ℕ) : ellOneIndicatorValues S (a + b) n =
           ellOneIndicatorValues S a n + ellOneIndicatorValues S b n := by
         by_cases hn : n ∈ S <;> simp [ellOneIndicatorValues, hn]
       simp_rw [heq]
       exact (summable_ellOneIndicatorValues S a).tsum_add (summable_ellOneIndicatorValues S b)
     map_smul' c a := by
       have heq (n : ℕ) : ellOneIndicatorValues S (c • a) n = c * ellOneIndicatorValues S a n := by
         by_cases hn : n ∈ S <;> simp [ellOneIndicatorValues, hn]
       simp_rw [heq]
       exact tsum_mul_left } : ellOne 𝕜 →ₗ[𝕜] 𝕜).mkContinuous 1
        (fun a => by simpa using norm_tsum_ellOneIndicatorValues_le S a)

@[simp] theorem ellOneIndicatorFunctional_single (S : Set ℕ) (n : ℕ) :
    ellOneIndicatorFunctional (𝕜 := 𝕜) S (lp.single 1 n (1 : 𝕜)) =
      if n ∈ S then 1 else 0 := by
  change (∑' j, ellOneIndicatorValues S (lp.single 1 n (1 : 𝕜)) j) = _
  rw [tsum_eq_single n]
  · simp [ellOneIndicatorValues]
  · intro j hj
    simp [ellOneIndicatorValues, lp.single_apply, hj]

end JLMS
