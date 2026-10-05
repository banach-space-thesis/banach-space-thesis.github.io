import ThesisCommon.Analysis.FinitePowerSumAbsorption
import JLMS.OrdinalSpaceFinitePower
import PFP.MainStatements

/-! The finite-multiple coefficient reduction from Corollary 4.10.
These are genuine isomorphisms for arbitrary ordinals and index universes. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon
variable {𝕜 Γ : Type*} [RCLike 𝕜] [Infinite Γ]

def lpOrdinalFiniteMultipleEquiv (α : Ordinal) (hα : Ordinal.omega0 ≤ α)
    (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) :
    lp (fun _ : Γ => OrdinalContinuous 𝕜 (α * ((n + 1 : ℕ) : Ordinal))) p ≃L[𝕜]
      lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p :=
  (lpMapEquiv p (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) α hα n)).trans
    (lpFinitePowerAbsorptionEquiv (n + 1) (Nat.succ_pos n) p hp)

def cZeroOrdinalFiniteMultipleEquiv [TopologicalSpace Γ] [DiscreteTopology Γ]
    (α : Ordinal) (hα : Ordinal.omega0 ≤ α) (n : ℕ) :
    C₀(Γ, OrdinalContinuous 𝕜 (α * ((n + 1 : ℕ) : Ordinal))) ≃L[𝕜]
      C₀(Γ, OrdinalContinuous 𝕜 α) :=
  (cZeroMapEquiv (ι := Γ) (JLMS.ordinalSpaceFinitePower (𝕜 := 𝕜) α hα n)).trans
    (cZeroFinitePowerAbsorptionEquiv (n + 1) (Nat.succ_pos n))

end PFP
