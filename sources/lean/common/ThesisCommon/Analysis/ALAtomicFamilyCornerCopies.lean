import ThesisCommon.Analysis.ALFiniteAtomicFamily

/-! Actual corner geometry for any family of atomic principal bands.
Finite families have weakly compact identity. Infinite families are
isometric to the scalar ell-one space on the same index set, whose
orthogonal self-copies have already been constructed. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon

theorem exists_orthogonal_cornerCopies_atomic_principalBand_family
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [HasSolidNorm E] [CompleteSpace E]
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (a : I → E) (ha : ∀ i, IsPositiveLatticeAtom (a i)) :
    ∃ Q : lp (fun i => principalBand (a i)) 1 →L[ℝ] lp (fun i => principalBand (a i)) 1,
      ∃ J P : ℕ → lp (fun i => principalBand (a i)) 1 →L[ℝ]
        lp (fun i => principalBand (a i)) 1,
        (∀ n, (P n).comp (J n) = Q) ∧
        (∀ n k, n ≠ k → (P n).comp (J k) = 0) ∧
        IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ _ - Q) := by
  classical
  cases finite_or_infinite I with
  | inl hfin =>
    letI := hfin
    refine ⟨0, fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
    · intro n
      simp
    · intro n k hnk
      simp
    · simpa only [sub_zero] using weaklyCompact_id_finite_atomic_principalBands hAL a ha
  | inr hinf =>
    letI := hinf
    let d : lp (fun i => principalBand (a i)) 1 ≃ₗᵢ[ℝ] lp (fun _ : I => ℝ) 1 :=
      lebesgueLpCoordinateEquiv (by simp : 0 < (1 : ℝ≥0∞).toReal)
        (fun i => positiveAtomPrincipalBandEquiv hAL (ha i))
    obtain ⟨J, P, hd, ho⟩ := exists_orthogonal_selfCopies_infinite_lp
      (𝕜 := ℝ) (E := ℝ) (Γ := I) 1 (by simp)
    obtain ⟨J', P', hd', ho'⟩ := exists_orthogonal_selfCopies_of_equiv
      d.toContinuousLinearEquiv J P hd ho
    refine ⟨ContinuousLinearMap.id ℝ _, J', P', hd', ho', ?_⟩
    rw [sub_self]
    exact weaklyCompact_zero

end ThesisCommon
