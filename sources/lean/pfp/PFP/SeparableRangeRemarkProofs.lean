import PFP.GeneralSumStatements
import ThesisCommon.Analysis.SeparableRangeFactorizationTransfer

/-! Exact separable-range replacements stated in Remarks 4.5 and 4.31.
The large-cardinal regime and the nonuniform cofinality condition remain
explicit. No WCG, separability, or total-dual assumption on X is added. -/
noncomputable section
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def Remark_4_5_ellOne : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ →
    (∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S)) →
      FactorisationTransfer 𝕜 Γ X (lp (fun _ : Γ => X) 1)

def Remark_4_5_general (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → ∀ hs : b.HasSymmetricNorm,
    ¬ b.EquivalentEllOne → (∀ S : X →L[𝕜] E, IsSeparable (Set.range S)) →
      FactorisationTransfer 𝕜 Γ X (UncountableSchauderSum b hs.1 X)

def Remark_4_5 (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Remark_4_5_ellOne 𝕜 Γ X ∧ Remark_4_5_general 𝕜 Γ E X b

theorem remark_4_5_ellOne : Remark_4_5_ellOne 𝕜 Γ X := by
  intro hΓ hsep
  constructor
  · intro hX
    have h := ellOne_hasUPFP_of_separable_scalar_ranges hsep hΓ hX
    exact ⟨h.hasPFP, h⟩
  · intro hX hcof
    exact ellOne_hasPFP_of_separable_scalar_ranges hsep hΓ hcof hX

theorem remark_4_5_general (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Remark_4_5_general 𝕜 Γ E X b := by
  intro hΓ hs _ hsep
  constructor
  · intro hX
    have h := UncountableSchauderSum.hasUPFP_of_separable_scalar_ranges hs hsep hΓ hX
    exact ⟨h.hasPFP, h⟩
  · intro hX hcof
    exact UncountableSchauderSum.hasPFP_of_separable_scalar_ranges hs hsep hΓ hcof hX

theorem remark_4_5 (b : NormalizedSchauderFamily 𝕜 Γ E) : Remark_4_5 𝕜 Γ E X b :=
  ⟨remark_4_5_ellOne 𝕜 Γ X, remark_4_5_general 𝕜 Γ E X b⟩

/-- Remark 4.31 repeats the two replacements and explains their outgoing
coordinate proof. The support conclusion is proved in the shared module. -/
def Remark_4_31 (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop := Remark_4_5 𝕜 Γ E X b

theorem remark_4_31 (b : NormalizedSchauderFamily 𝕜 Γ E) : Remark_4_31 𝕜 Γ E X b :=
  remark_4_5 𝕜 Γ E X b

end PFP
