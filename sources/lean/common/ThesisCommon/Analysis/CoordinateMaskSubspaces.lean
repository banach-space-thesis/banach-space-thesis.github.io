import ThesisCommon.Analysis.CoordinateMasks
import ThesisCommon.Analysis.SequenceCoordinates

/-! Actual closed supported subspaces and restricted block compressions. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def lpSupportedSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    Submodule 𝕜 (lp (fun _ : Γ => X) p) where
  carrier := {x | ∀ γ ∉ A, x γ = 0}
  zero_mem' := by intro γ hγ; rfl
  add_mem' := by intro x y hx hy γ hγ; change x γ + y γ = 0; rw [hx γ hγ, hy γ hγ, add_zero]
  smul_mem' := by intro c x hx γ hγ; change c • x γ = 0; rw [hx γ hγ, smul_zero]

theorem lpSupportedSubmodule_isClosed (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    IsClosed (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A : Set (lp (fun _ : Γ => X) p)) := by
  change IsClosed {x : lp (fun _ : Γ => X) p | ∀ γ, γ ∉ A → lpCoordinate (𝕜 := 𝕜) p γ x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_eq (lpCoordinate (𝕜 := 𝕜) (X := X) p γ).continuous continuous_const

def lpProjectionTo (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set Γ) :
    lp (fun _ : Γ => X) p →L[𝕜] lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A :=
  (lpCoordinateProjection p A).codRestrict (lpSupportedSubmodule p A)
    (fun x γ hγ => by simp [hγ])

def lpBlockCompression (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (A : Set Γ) :
    lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A →L[𝕜] lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A :=
  (lpProjectionTo p A).comp (P.comp (lpSupportedSubmodule p A).subtypeL)

section CZero
variable [TopologicalSpace Γ] [DiscreteTopology Γ]

def cZeroSupportedSubmodule (A : Set Γ) : Submodule 𝕜 C₀(Γ, X) where
  carrier := {x | ∀ γ ∉ A, x γ = 0}
  zero_mem' := by intro γ hγ; rfl
  add_mem' := by intro x y hx hy γ hγ; change x γ + y γ = 0; rw [hx γ hγ, hy γ hγ, add_zero]
  smul_mem' := by intro c x hx γ hγ; change c • x γ = 0; rw [hx γ hγ, smul_zero]

omit [DiscreteTopology Γ] in
theorem cZeroSupportedSubmodule_isClosed (A : Set Γ) :
    IsClosed (cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) A : Set C₀(Γ, X)) := by
  change IsClosed {x : C₀(Γ, X) | ∀ γ, γ ∉ A → cZeroCoordinate (𝕜 := 𝕜) γ x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_eq (cZeroCoordinate (𝕜 := 𝕜) (X := X) γ).continuous continuous_const

def cZeroProjectionTo (A : Set Γ) :
    C₀(Γ, X) →L[𝕜] cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) A :=
  (cZeroCoordinateProjection A).codRestrict (cZeroSupportedSubmodule A)
    (fun x γ hγ => by simp [hγ])

def cZeroBlockCompression (P : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (A : Set Γ) :
    cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) A →L[𝕜] cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) A :=
  (cZeroProjectionTo A).comp (P.comp (cZeroSupportedSubmodule A).subtypeL)

end CZero
end ThesisCommon
