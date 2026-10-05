import JLMS.OrderedFiniteRows

/-!
# Normalized averages of finitely many paired differences

Choose common ordered rows from disjoint increasing coordinate families.
Assign coefficients ±1/(2N). The resulting normalized block is exactly the
average of the N half-differences used at a binary sign-tree level.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.decEq

def pairedFiniteRowIndex (e : ι → ℕ → ℕ) (n : ℕ) (p : ι × Fin 2) : ℕ :=
  e p.1 (2 * n + p.2.val)

theorem pairedFiniteRowIndex_injective (e : ι → ℕ → ℕ)
    (he : Function.Injective (fun p : ι × ℕ => e p.1 p.2)) (n : ℕ) :
    Function.Injective (pairedFiniteRowIndex e n) := by
  intro p q hpq
  have h := @he (p.1, 2 * n + p.2.val) (q.1, 2 * n + q.2.val) hpq
  have hi := congrArg Prod.fst h
  have hj := congrArg Prod.snd h
  change p.1 = q.1 at hi
  apply Prod.ext hi
  apply Fin.ext
  dsimp at hj
  omega

theorem pairedFiniteRowIndex_strictMono (e : ι → ℕ → ℕ)
    (hs : ∀ i, StrictMono (e i)) (p : ι × Fin 2) :
    StrictMono (fun n => pairedFiniteRowIndex e n p) := by
  intro n m hnm
  apply hs p.1
  dsimp
  omega

theorem exists_paired_average_block (e : ι → ℕ → ℕ)
    (he : Function.Injective (fun p : ι × ℕ => e p.1 p.2))
    (hs : ∀ i, StrictMono (e i)) (f : ℕ → (X →L[𝕜] 𝕜)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ b : NormalizedBlockSystem 𝕜,
      ∀ n, b.applyDual f n = ((1 / (2 * (Fintype.card ι : ℝ)) : ℝ) : 𝕜) •
        ∑ i, (f (e i (2 * q n + 1)) - f (e i (2 * q n))) := by
  obtain ⟨q, hq, ho⟩ := exists_strictMono_ordered_rows (pairedFiniteRowIndex e)
    (pairedFiniteRowIndex_strictMono e hs)
  let w : ℝ := 1 / (2 * (Fintype.card ι : ℝ))
  have hw : 0 < w := by dsimp [w]; positivity
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hwcast : (w : 𝕜) = ((1 / (2 * (Fintype.card ι : ℝ)) : ℝ) : 𝕜) := rfl
  let a (_ : ℕ) (p : ι × Fin 2) : 𝕜 := if p.2 = 0 then -(w : 𝕜) else (w : 𝕜)
  have ha (n : ℕ) : ∑ p, ‖a n p‖ = 1 := by
    simp only [a, Fintype.sum_prod_type, Fin.sum_univ_two,
      if_true, h10, if_false, norm_neg, RCLike.norm_ofReal, abs_of_pos hw]
    rw [Finset.sum_const, nsmul_eq_mul]
    dsimp [w]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  let h (n : ℕ) := pairedFiniteRowIndex e (q n)
  let b := NormalizedBlockSystem.ofFiniteRows h
    (fun n => pairedFiniteRowIndex_injective e he (q n)) ho a ha
  refine ⟨q, hq, b, ?_⟩
  intro n
  rw [← hwcast]
  rw [NormalizedBlockSystem.ofFiniteRows_applyDual]
  simp only [a, Fintype.sum_prod_type, Fin.sum_univ_two,
    if_true, h10, if_false, pairedFiniteRowIndex, h,
    Fin.val_zero, Fin.val_one, Nat.add_zero, neg_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end JLMS
