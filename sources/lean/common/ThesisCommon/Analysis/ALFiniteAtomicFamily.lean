import ThesisCommon.Analysis.ALAtomicPrincipalBand
import ThesisCommon.Analysis.OperatorAlgebraProductCopies

/-! The finite atomic remainder of a heterogeneous AL band sum has a
genuinely weakly compact identity. Finite dimensionality follows from the
constructed one-dimensional atomic bands and the injective coordinate map;
the index set is allowed to be empty. -/
noncomputable section
namespace ThesisCommon
open scoped ENNReal

theorem finiteDimensional_lp_of_finite_family
    {𝕜 I : Type*} [RCLike 𝕜] [Finite I] {F : I → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    [∀ i, FiniteDimensional 𝕜 (F i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FiniteDimensional 𝕜 (lp F p) := by
  classical
  letI := Fintype.ofFinite I
  let A : lp F p →ₗ[𝕜] (∀ i, F i) :=
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact FiniteDimensional.of_injective A (fun _ _ h => lp.ext h)

theorem weaklyCompact_id_finite_lp_family
    {𝕜 I : Type*} [RCLike 𝕜] [Finite I] {F : I → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    [∀ i, FiniteDimensional 𝕜 (F i)] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (lp F p)) := by
  letI := finiteDimensional_lp_of_finite_family (𝕜 := 𝕜) (F := F) p
  exact weaklyCompact_id_of_finiteDimensional

theorem weaklyCompact_id_finite_atomic_principalBands
    {E I : Type*} [Finite I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [HasSolidNorm E] [CompleteSpace E]
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (a : I → E) (ha : ∀ i, IsPositiveLatticeAtom (a i)) :
    IsWeaklyCompactOperator
      (ContinuousLinearMap.id ℝ (lp (fun i => principalBand (a i)) 1)) := by
  letI (i : I) : FiniteDimensional ℝ (principalBand (a i)) :=
    finiteDimensional_principalBand_of_positive_atom hAL (ha i)
  exact weaklyCompact_id_finite_lp_family 1

end ThesisCommon
