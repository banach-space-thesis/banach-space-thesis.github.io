import Posets.QuotientStatements

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

section BoundedPoset
variable (P : Type) [PartialOrder P] [Countable P] [Infinite P]
variable (X : BoundedExtension P → Type)
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t)

/-- Lemma 6.17, including the actual block formula for the right inverse. -/
def Lemma_6_17 : Prop :=
  FewOperators 𝕜 X ι →
  let Y := DependentCZeroSum 𝕜 (fun p : P => X (middle p))
  ∃ C : Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P),
    (C : Set _) = oppositeIncidenceOperators 𝕜 P ∧
    ∃ ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y), Isometry ρ ∧
      ∀ T : C, ∀ s t,
        operatorBlock 𝕜 (fun p : P => X (middle p)) (fun p : P => X (middle p)) (ρ T) s t =
          scalarMatrix 𝕜 T.val s t • ι (middle t) (middle s)

/-- Lemma 6.21. The map extracts precisely the scalar in each block;
off-order entries vanish because its range is the opposite incidence algebra. -/
def Lemma_6_21 : Prop :=
  FewOperators 𝕜 X ι →
  let Y := DependentCZeroSum 𝕜 (fun p : P => X (middle p))
  ∃ C : Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P),
    (C : Set _) = oppositeIncidenceOperators 𝕜 P ∧
    ∃ θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
      ‖θ.toContinuousLinearMap‖ = 1 ∧
      (∀ T, θ T = 0 ↔ HasSeparableRange 𝕜 Y Y T) ∧
      ∀ T : Y →L[𝕜] Y, ∀ s t,
        HasSeparableRange 𝕜 (X (middle t)) (X (middle s))
          (operatorBlock 𝕜 (fun p : P => X (middle p)) (fun p : P => X (middle p)) T s t -
            scalarMatrix 𝕜 (θ T).val s t • ι (middle t) (middle s))
end BoundedPoset

/-- Corollary 6.19: the full equivalence for every block of the actual c₀ sums. -/
def Corollary_6_19 (X Z : ℕ → Type)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace 𝕜 (X n)] [∀ n, CompleteSpace (X n)]
    [∀ n, NormedAddCommGroup (Z n)] [∀ n, NormedSpace 𝕜 (Z n)] [∀ n, CompleteSpace (Z n)]
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) : Prop :=
  HasSeparableRange 𝕜 (DependentCZeroSum 𝕜 X) (DependentCZeroSum 𝕜 Z) T ↔
    ∀ n m, HasSeparableRange 𝕜 (X m) (Z n) (operatorBlock 𝕜 X Z T n m)

end Posets
