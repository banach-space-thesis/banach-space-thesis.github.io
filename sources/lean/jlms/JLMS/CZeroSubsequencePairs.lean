import JLMS.PairedDisjointFunctions

/-!
# Pairing a subsequence of the c₀ coordinates

Insert each coefficient twice, with opposite signs, on consecutive pairs of
a strictly increasing sequence of coordinates. The resulting map is a
contraction. Its exact coordinate formulas allow half-difference functionals
to recover the original sequence in the weak-star projection construction.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable (s : ℕ → ℕ) (hs : StrictMono s)

include hs in
theorem cZero_subsequenceUnits_disjoint :
    Pairwise fun i j => Disjoint (Function.support (cZeroUnit 𝕜 (s i)))
      (Function.support (cZeroUnit 𝕜 (s j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro m hi hj
  have him : m = s i := by simpa [cZeroUnit_apply] using hi
  have hjm : m = s j := by simpa [cZeroUnit_apply] using hj
  exact hij (hs.injective (him.symm.trans hjm))

theorem cZero_subsequenceUnits_norm_le (n : ℕ) : ‖cZeroUnit 𝕜 (s n)‖ ≤ 1 :=
  norm_clopenIndicator_le _ _ _

/-- Insert coefficients on the selected coordinates, setting others to zero. -/
def cZeroSubsequenceInsertion : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  disjointSynthesis (fun n => cZeroUnit 𝕜 (s n))
    (cZero_subsequenceUnits_norm_le s) (cZero_subsequenceUnits_disjoint s hs)

theorem norm_cZeroSubsequenceInsertion_le :
    ‖cZeroSubsequenceInsertion (𝕜 := 𝕜) s hs‖ ≤ 1 := norm_disjointSynthesis_le _ _ _

@[simp] theorem cZeroSubsequenceInsertion_unit (n : ℕ) :
    cZeroSubsequenceInsertion s hs (cZeroUnit 𝕜 n) = cZeroUnit 𝕜 (s n) :=
  disjointSynthesis_unit _ _ _ n

def cZeroPairInsertion : cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  disjointSynthesis (pairedDisjointFunction (fun n => cZeroUnit 𝕜 (s n)))
    (pairedDisjointFunction_norm_le _ (cZero_subsequenceUnits_norm_le s)
      (cZero_subsequenceUnits_disjoint s hs))
    (pairedDisjointFunction_disjoint _ (cZero_subsequenceUnits_disjoint s hs))

theorem norm_cZeroPairInsertion_le : ‖cZeroPairInsertion (𝕜 := 𝕜) s hs‖ ≤ 1 :=
  norm_disjointSynthesis_le _ _ _

@[simp] theorem cZeroPairInsertion_unit (n : ℕ) :
    cZeroPairInsertion s hs (cZeroUnit 𝕜 n) =
      cZeroUnit 𝕜 (s (2 * n)) - cZeroUnit 𝕜 (s (2 * n + 1)) :=
  disjointSynthesis_unit _ _ _ n

theorem cZeroPairInsertion_even (a : cZero 𝕜) (n : ℕ) :
    cZeroPairInsertion s hs a (s (2 * n)) = a n := by
  classical
  let η := pairedDisjointFunction (fun j => cZeroUnit 𝕜 (s j))
  have hη (i : ℕ) : η i (s (2 * n)) = if n = i then 1 else 0 := by
    change cZeroUnit 𝕜 (s (2 * i)) (s (2 * n)) -
      cZeroUnit 𝕜 (s (2 * i + 1)) (s (2 * n)) = _
    simp only [cZeroUnit_apply, hs.injective.eq_iff]
    have he : 2 * n = 2 * i ↔ n = i := by omega
    have ho : 2 * n ≠ 2 * i + 1 := by omega
    simp [he, ho]
  change evaluation (s (2 * n)) (∑' i, a i • η i) = a n
  rw [(evaluation (s (2 * n))).map_tsum (summable_smul_disjoint η
    (pairedDisjointFunction_norm_le _ (cZero_subsequenceUnits_norm_le s)
      (cZero_subsequenceUnits_disjoint s hs))
    (pairedDisjointFunction_disjoint _ (cZero_subsequenceUnits_disjoint s hs)) a)]
  simp only [map_smul, evaluation_apply, hη, smul_eq_mul]
  rw [tsum_eq_single n]
  · simp
  · intro i hi
    simp [Ne.symm hi]

theorem cZeroPairInsertion_odd (a : cZero 𝕜) (n : ℕ) :
    cZeroPairInsertion s hs a (s (2 * n + 1)) = -a n := by
  classical
  let η := pairedDisjointFunction (fun j => cZeroUnit 𝕜 (s j))
  have hη (i : ℕ) : η i (s (2 * n + 1)) = if n = i then -1 else 0 := by
    change cZeroUnit 𝕜 (s (2 * i)) (s (2 * n + 1)) -
      cZeroUnit 𝕜 (s (2 * i + 1)) (s (2 * n + 1)) = _
    simp only [cZeroUnit_apply, hs.injective.eq_iff]
    have he : 2 * n + 1 ≠ 2 * i := by omega
    have ho : 2 * n + 1 = 2 * i + 1 ↔ n = i := by omega
    by_cases hni : n = i <;> simp [he, ho, hni]
  change evaluation (s (2 * n + 1)) (∑' i, a i • η i) = -a n
  rw [(evaluation (s (2 * n + 1))).map_tsum (summable_smul_disjoint η
    (pairedDisjointFunction_norm_le _ (cZero_subsequenceUnits_norm_le s)
      (cZero_subsequenceUnits_disjoint s hs))
    (pairedDisjointFunction_disjoint _ (cZero_subsequenceUnits_disjoint s hs)) a)]
  simp only [map_smul, evaluation_apply, hη, smul_eq_mul]
  rw [tsum_eq_single n]
  · simp
  · intro i hi
    simp [Ne.symm hi]

end JLMS
