import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies

/-! Self-copies under finite products and the finite scalar-lp remainder.
Products use the actual maximum norm and bounded coordinate maps. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_orthogonal_selfCopies_prod
    (J P : ℕ → E →L[𝕜] E) (I Q : ℕ → F →L[𝕜] F)
    (hdE : ∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E)
    (hoE : ∀ n m, n ≠ m → (P n).comp (J m) = 0)
    (hdF : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 F)
    (hoF : ∀ n m, n ≠ m → (Q n).comp (I m) = 0) :
    ∃ J P : ℕ → (E × F) →L[𝕜] (E × F),
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  refine ⟨fun n => (J n).prodMap (I n), fun n => (P n).prodMap (Q n), ?_, ?_⟩
  · intro n
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun T : E →L[𝕜] E => T x.1) (hdE n)
    · exact congrArg (fun T : F →L[𝕜] F => T x.2) (hdF n)
  · intro n m hnm
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun T : E →L[𝕜] E => T x.1) (hoE n m hnm)
    · exact congrArg (fun T : F →L[𝕜] F => T x.2) (hoF n m hnm)

theorem weaklyCompact_id_finite_scalar_lp {Γ : Type*} [Finite Γ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (lp (fun _ : Γ => 𝕜) p)) := by
  classical
  letI := Fintype.ofFinite Γ
  let A : lp (fun _ : Γ => 𝕜) p →ₗ[𝕜] (Γ → 𝕜) :=
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  letI : FiniteDimensional 𝕜 (lp (fun _ : Γ => 𝕜) p) :=
    FiniteDimensional.of_injective A (fun _ _ h => lp.ext h)
  exact weaklyCompact_id_of_finiteDimensional

end ThesisCommon
