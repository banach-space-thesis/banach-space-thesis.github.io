import ThesisCommon.Analysis.OperatorAlgebraAutomaticBound

/-! Countably many exact orthogonal copies are constructed from a binary
splitting, in particular from a bounded linear isomorphism `E ≃ E × E`.
No uniform bound on the norms of the iterated embeddings is required. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_orthogonal_selfCopies_of_binary_split
    (L R Q S : E →L[𝕜] E)
    (hQL : Q.comp L = ContinuousLinearMap.id 𝕜 E)
    (hQR : Q.comp R = 0) (hSL : S.comp L = 0)
    (hSR : S.comp R = ContinuousLinearMap.id 𝕜 E) :
    ∃ J P : ℕ → E →L[𝕜] E,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  classical
  let J : ℕ → E →L[𝕜] E := Nat.rec L (fun _ T => R.comp T)
  let P : ℕ → E →L[𝕜] E := Nat.rec Q (fun _ T => T.comp S)
  have hJ0 : J 0 = L := rfl
  have hP0 : P 0 = Q := rfl
  have hJs (n : ℕ) : J (n + 1) = R.comp (J n) := rfl
  have hPs (n : ℕ) : P (n + 1) = (P n).comp S := rfl
  have hc (n m : ℕ) : (P n).comp (J m) = if n = m then ContinuousLinearMap.id 𝕜 E else 0 := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => simpa only [hP0, hJ0, if_pos rfl] using hQL
      | succ m =>
        rw [hP0, hJs, ← ContinuousLinearMap.comp_assoc, hQR]
        simp
    | succ n ih =>
      cases m with
      | zero =>
        rw [hPs, hJ0, ContinuousLinearMap.comp_assoc, hSL]
        simp
      | succ m =>
        rw [hPs, hJs]
        calc
          _ = (P n).comp ((S.comp R).comp (J m)) := by
            simp only [ContinuousLinearMap.comp_assoc]
          _ = (P n).comp (J m) := by rw [hSR, ContinuousLinearMap.id_comp]
          _ = _ := by simpa only [Nat.succ.injEq] using ih m
  exact ⟨J, P, fun n => by simpa using hc n n,
    fun n m hnm => by simpa only [if_neg hnm] using hc n m⟩

theorem exists_orthogonal_selfCopies_of_square_equiv (e : E ≃L[𝕜] E × E) :
    ∃ J P : ℕ → E →L[𝕜] E,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  let L := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E E)
  let R := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 E E)
  let Q := (ContinuousLinearMap.fst 𝕜 E E).comp e.toContinuousLinearMap
  let S := (ContinuousLinearMap.snd 𝕜 E E).comp e.toContinuousLinearMap
  apply exists_orthogonal_selfCopies_of_binary_split L R Q S
  all_goals
    apply ContinuousLinearMap.ext
    intro x
    simp [L, R, Q, S]

theorem exists_algebra_seminorm_bound_of_square_equiv [CompleteSpace E]
    (e : E ≃L[𝕜] E × E)
    (α : (E →L[𝕜] E) → ℝ) (hnonneg : ∀ T, 0 ≤ α T) (hzero : α 0 = 0)
    (hsmul : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T)
    (hmul : ∀ S T, α (S.comp T) ≤ α S * α T) :
    ∃ C : ℝ, 0 < C ∧ ∀ T, α T ≤ C * ‖T‖ := by
  obtain ⟨J, P, hdiag, hoff⟩ := exists_orthogonal_selfCopies_of_square_equiv e
  exact exists_algebra_seminorm_bound_of_orthogonal_selfCopies J P hdiag hoff
    α hnonneg hzero hsmul hmul

end ThesisCommon
