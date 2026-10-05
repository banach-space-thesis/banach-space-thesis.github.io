import ThesisCommon.Analysis.QuasiReflexiveDefinitions

/-! Exact general Banach-space targets from Appendix B.

These Prop declarations are specifications; their proofs are in the three
separate Appendix proof modules. JamesStatements supplies B.4 on the actual
James sequence space; its cited structural results remain separate proof
obligations rather than fields assumed in an abstract space.
-/
noncomputable section
set_option synthInstance.maxSize 1024
namespace PFP
open ThesisCommon

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma B.1, `lem:complemented-copy-implies-hyperplanes`.
The complemented subspace has its inherited norm and an actual continuous
linear retraction. Both printed conclusions are retained. -/
def Lemma_B_1 [CompleteSpace X] : Prop :=
  ¬ FiniteDimensional 𝕜 X →
    (∃ E : Submodule 𝕜 X,
      E.ClosedComplemented ∧ IsIsomorphicToScalarExtension 𝕜 E) →
    IsIsomorphicToScalarExtension 𝕜 X ∧ IsIsomorphicToEveryHyperplane 𝕜 X

/-- Lemma B.2, `lem:qref-one-dual-and-summands`.
The second conclusion quantifies all closed complementary subspaces of X and
asserts the actual quotient-space isomorphism, not just a dimension equality.
The product uses the usual max norm; `≃L` supplies a continuous linear map and
continuous inverse on the genuine quotient topologies. -/
def Lemma_B_2 [CompleteSpace X] : Prop :=
  IsQuasiReflexiveOfOrderOne 𝕜 X →
    IsQuasiReflexiveOfOrderOne 𝕜 (StrongDual 𝕜 X) ∧
      ∀ Y Z : Submodule 𝕜 X,
        ∀ (hY : IsClosed (Y : Set X)) (hZ : IsClosed (Z : Set X)), IsCompl Y Z →
          letI : CompleteSpace Y := hY.completeSpace_coe
          letI : CompleteSpace Z := hZ.completeSpace_coe
          Nonempty (ResiduumSpace 𝕜 X ≃L[𝕜]
            (ResiduumSpace 𝕜 Y × ResiduumSpace 𝕜 Z))

/-- Proposition B.3, `prop:qref-primary-dual`.
Quasi-reflexivity and all three original hypotheses occur explicitly; the
conclusion is primariness of the actual continuous dual. -/
def Proposition_B_3 [CompleteSpace X] : Prop :=
  IsQuasiReflexiveOfOrderOne 𝕜 X →
    IsPrimary 𝕜 X →
    IsIsomorphicToEveryHyperplane 𝕜 X →
    IsIsomorphicToEveryHyperplane 𝕜 (StrongDual 𝕜 X) →
      IsPrimary 𝕜 (StrongDual 𝕜 X)

end PFP
