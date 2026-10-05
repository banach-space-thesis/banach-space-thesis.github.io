import JLMS.CZeroMatrixNorm
import JLMS.PhaseFunctions

/-!
# Disjoint finite phase blocks in c₀

Each finite coordinate set carries unimodular phases chosen to norm a
prescribed coefficient vector. Disjoint sets give disjoint unit-ball
functions and therefore a contractive block insertion map. These are the
coordinate blocks in the Galego–Plichko projection argument.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]

def cZeroFinitePhaseBlock (F : Finset ℕ) (a : ℕ → 𝕜) : cZero 𝕜 :=
  ∑ k ∈ F, scalarPhase (a k) • cZeroUnit 𝕜 k

@[simp] theorem cZeroFinitePhaseBlock_apply (F : Finset ℕ) (a : ℕ → 𝕜) (k : ℕ) :
    cZeroFinitePhaseBlock F a k = if k ∈ F then scalarPhase (a k) else 0 := by
  classical
  change evaluation k (∑ j ∈ F, scalarPhase (a j) • cZeroUnit 𝕜 j) = _
  simp only [map_sum, map_smul, evaluation_apply, cZeroUnit_apply, smul_eq_mul]
  by_cases hk : k ∈ F
  · rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j hj hjk; simp [Ne.symm hjk]
    · exact fun h => (h hk).elim
  · rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro j hj
      have hkj : k ≠ j := by intro h; subst j; exact hk hj
      simp [hkj]

theorem norm_cZeroFinitePhaseBlock_le (F : Finset ℕ) (a : ℕ → 𝕜) :
    ‖cZeroFinitePhaseBlock F a‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro k
  change ‖cZeroFinitePhaseBlock F a k‖ ≤ 1
  rw [cZeroFinitePhaseBlock_apply]
  split_ifs <;> simp [norm_scalarPhase]

theorem cZeroFinitePhaseBlock_disjoint (F : ℕ → Finset ℕ)
    (hF : Pairwise fun n m => Disjoint (F n) (F m)) (a : ℕ → ℕ → 𝕜) :
    Pairwise fun n m => Disjoint (Function.support (cZeroFinitePhaseBlock (F n) (a n)))
      (Function.support (cZeroFinitePhaseBlock (F m) (a m))) := by
  classical
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro k hn hm
  have hkn : k ∈ F n := by
    by_contra h
    exact hn (by simp [h])
  have hkm : k ∈ F m := by
    by_contra h
    exact hm (by simp [h])
  exact Finset.disjoint_left.mp (hF hnm) hkn hkm

def cZeroFiniteBlockInsertion (F : ℕ → Finset ℕ)
    (hF : Pairwise fun n m => Disjoint (F n) (F m)) (a : ℕ → ℕ → 𝕜) :
    cZero 𝕜 →L[𝕜] cZero 𝕜 :=
  disjointSynthesis (fun n => cZeroFinitePhaseBlock (F n) (a n))
    (fun n => norm_cZeroFinitePhaseBlock_le _ _) (cZeroFinitePhaseBlock_disjoint F hF a)

theorem norm_cZeroFiniteBlockInsertion_le (F : ℕ → Finset ℕ)
    (hF : Pairwise fun n m => Disjoint (F n) (F m)) (a : ℕ → ℕ → 𝕜) :
    ‖cZeroFiniteBlockInsertion F hF a‖ ≤ 1 := norm_disjointSynthesis_le _ _ _

@[simp] theorem cZeroFiniteBlockInsertion_unit (F : ℕ → Finset ℕ)
    (hF : Pairwise fun n m => Disjoint (F n) (F m)) (a : ℕ → ℕ → 𝕜) (n : ℕ) :
    cZeroFiniteBlockInsertion F hF a (cZeroUnit 𝕜 n) = cZeroFinitePhaseBlock (F n) (a n) :=
  disjointSynthesis_unit _ _ _ n

theorem cZero_operator_eq_of_units {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B : cZero 𝕜 →L[𝕜] X) (h : ∀ n, A (cZeroUnit 𝕜 n) = B (cZeroUnit 𝕜 n)) : A = B := by
  apply ContinuousLinearMap.ext
  intro a
  have hA := (cZero_hasSum_units a).map A A.continuous
  have hB := (cZero_hasSum_units a).map B B.continuous
  have heq : (fun n => A (a n • cZeroUnit 𝕜 n)) = fun n => B (a n • cZeroUnit 𝕜 n) := by
    funext n
    simp only [map_smul, h]
  exact hA.unique (by simpa only [Function.comp_def, heq] using hB)

end JLMS
