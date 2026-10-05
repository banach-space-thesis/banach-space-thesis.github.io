import ThesisCommon.Analysis.OperatorAlgebraSelfCopies
import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.SequenceCoordinates
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity
import ThesisCommon.Analysis.ALAtomicRepresentation
import ThesisCommon.WeakCompact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Concrete self-copy geometry for sequence spaces, the actual Lebesgue
interval spaces, and complete atomic real AL-lattices. No general measure
classification is assumed. The finite atomic case has weakly compact identity. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_orthogonal_selfCopies_of_equiv (e : E ≃L[𝕜] F)
    (J P : ℕ → F →L[𝕜] F)
    (hd : ∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 F)
    (ho : ∀ n m, n ≠ m → (P n).comp (J m) = 0) :
    ∃ J P : ℕ → E →L[𝕜] E,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  let J' n := e.symm.toContinuousLinearMap.comp ((J n).comp e.toContinuousLinearMap)
  let P' n := e.symm.toContinuousLinearMap.comp ((P n).comp e.toContinuousLinearMap)
  refine ⟨J', P', ?_, ?_⟩
  · intro n
    ext x
    change e.symm (P n (e (e.symm (J n (e x))))) = x
    rw [e.apply_symm_apply]
    change e.symm (((P n).comp (J n)) (e x)) = x
    rw [hd]
    exact e.symm_apply_apply x
  · intro n m hnm
    ext x
    change e.symm (P n (e (e.symm (J m (e x))))) = 0
    rw [e.apply_symm_apply]
    change e.symm (((P n).comp (J m)) (e x)) = 0
    rw [ho n m hnm]
    exact map_zero e.symm

theorem exists_orthogonal_selfCopies_of_sequence_equiv
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : E ≃L[𝕜] lp (fun _ : ℕ => E) p) :
    ∃ J P : ℕ → E →L[𝕜] E,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  let J n := e.symm.toContinuousLinearMap.comp (lp.singleContinuousLinearMap 𝕜 _ p n)
  let P n := (lpCoordinate p n).comp e.toContinuousLinearMap
  refine ⟨J, P, ?_, ?_⟩
  · intro n
    ext x
    simp [J, P]
  · intro n m hnm
    ext x
    simp [J, P, hnm]

theorem exists_orthogonal_selfCopies_infinite_lp {Γ : Type*} [Infinite Γ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) :
    ∃ J P : ℕ → lp (fun _ : Γ => E) p →L[𝕜] lp (fun _ : Γ => E) p,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_of_sequence_equiv
    (lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (X := E) p hp).toContinuousLinearEquiv

theorem exists_orthogonal_selfCopies_intervalLp (p : BanachExponent) (hp : p.val ≠ ∞) :
    ∃ J P : ℕ → IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_of_sequence_equiv
    (intervalLpFunctionSelfSimilarity 𝕜 p hp).toContinuousLinearEquiv

theorem weaklyCompact_id_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E) := by
  letI : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  refine ⟨toWeakSpace 𝕜 E '' Metric.closedBall 0 1,
    (isCompact_closedBall (0 : E) 1).image (toWeakSpaceCLM 𝕜 E).continuous, ?_⟩
  intro x hx
  exact ⟨x, by simpa using hx, rfl⟩

/-- The complete atomic AL case supplies the geometry itself. This theorem
does not extend the atomic hypothesis to arbitrary atomless measures. -/
theorem atomic_AL_weaklyCompact_id_or_selfCopies
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Lattice X]
    [IsOrderedAddMonoid X] [IsOrderedModule ℝ X] [HasSolidNorm X] [CompleteSpace X]
    (hAL : ∀ x y : X, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (hAtom : ∀ x : X, 0 ≤ x → x ≠ 0 → ∃ a : X, IsPositiveLatticeAtom a ∧ a ≤ x) :
    IsWeaklyCompactOperator (ContinuousLinearMap.id ℝ X) ∨
      ∃ J P : ℕ → X →L[ℝ] X,
        (∀ n, (P n).comp (J n) = ContinuousLinearMap.id ℝ X) ∧
        (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  classical
  let e := alAtomicEquiv hAL hAtom
  cases finite_or_infinite (NormalizedLatticeAtom X) with
  | inl hfin =>
    letI := hfin
    letI := Fintype.ofFinite (NormalizedLatticeAtom X)
    let A : X →ₗ[ℝ] (NormalizedLatticeAtom X → ℝ) :=
      { toFun := fun x => e x
        map_add' := by intros; rw [map_add]; rfl
        map_smul' := by intros; rw [map_smul]; rfl }
    letI : FiniteDimensional ℝ X := FiniteDimensional.of_injective A (by
      intro x y h
      apply e.injective
      exact lp.ext h)
    exact Or.inl weaklyCompact_id_of_finiteDimensional
  | inr hinf =>
    letI := hinf
    obtain ⟨J, P, hd, ho⟩ := exists_orthogonal_selfCopies_infinite_lp
      (𝕜 := ℝ) (E := ℝ) (Γ := NormalizedLatticeAtom X) 1 (by simp)
    exact Or.inr (exists_orthogonal_selfCopies_of_equiv e J P hd ho)

end ThesisCommon
