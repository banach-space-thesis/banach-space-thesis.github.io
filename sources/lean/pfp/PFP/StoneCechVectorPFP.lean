import ThesisCommon.Analysis.FreeNatUltrafilterSeparablePFP

/-! Remark 5.2, with the scope of the cited theorem made explicit.

The compact space `FreeNatUltrafilter` is the actual free-ultrafilter model
of the Stone--Čech remainder ω*. The manuscript prints the transfer for
arbitrary Banach coefficients, whereas Drewnowski (1989), Theorem 5 and
Corollary 6, assumes separability. The printed formula is retained below as
an unproved target. Only the separately named separable version is proved.
The uniform transfer even preserves each supplied factorization constant.
-/
noncomputable section
namespace PFP
open ThesisCommon

def Remark_5_2_asPrinted (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : Prop :=
  (HasPFP 𝕜 X → HasPFP 𝕜 C(FreeNatUltrafilter, X)) ∧
    (HasUPFP 𝕜 X → HasUPFP 𝕜 C(FreeNatUltrafilter, X))

def Remark_5_2_separable (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] : Prop := Remark_5_2_asPrinted 𝕜 X

theorem remark_5_2_separable (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] : Remark_5_2_separable 𝕜 X :=
  ⟨freeNatUltrafilter_hasPFP_of_separable, freeNatUltrafilter_hasUPFP_of_separable⟩

theorem remark_5_2_separable_same_constant (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (C : ℝ) (hX : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜 C(FreeNatUltrafilter, X) C :=
  freeNatUltrafilter_hasCPFP_of_separable hX

end PFP
