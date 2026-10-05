import Posets.QuotientSection

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets

/-- Proposition 6.22, including the harmless empty-index case. -/
theorem proposition_6_22_proof (𝕜 : Type) [RCLike 𝕜] (P : Type) [PartialOrder P]
    [Countable P] (X : BoundedExtension P → Type)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] (ι : ∀ s t, X s →L[𝕜] X t) : Proposition_6_22 𝕜 P X ι := by
  intro h
  cases isEmpty_or_nonempty P with
  | inr hn =>
    letI := hn
    refine ⟨oppositeIncidenceSubalgebra 𝕜 P, rfl, scalarQuotientHom h,
      incidenceLiftHom (middleFewOperators h), ?_⟩
    exact ⟨(scalarQuotientMap_rightInverse h).surjective,
      scalarQuotientMap_eq_zero_iff h, scalarQuotientMap_rightInverse h⟩
  | inl he =>
    letI := he
    let Y := DependentCZeroSum 𝕜 (fun p : P => X (middle p))
    let C := oppositeIncidenceSubalgebra 𝕜 P
    haveI : Subsingleton Y := ⟨fun x y => by
      apply Subtype.ext
      apply lp.ext
      funext p
      exact isEmptyElim p⟩
    haveI : Subsingleton (CZeroOn 𝕜 P) := ⟨fun x y => by
      ext p
      exact isEmptyElim p.val⟩
    let θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C :=
      { toContinuousLinearMap := 0, map_mul' := fun _ _ => by simp }
    let ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y) :=
      { toContinuousLinearMap := 0, map_mul' := fun _ _ => by simp }
    refine ⟨C, rfl, θ, ρ, ?_⟩
    refine ⟨fun c => ⟨0, Subsingleton.elim _ _⟩, ?_, fun c => Subsingleton.elim _ _⟩
    intro T
    have hz : T = 0 := Subsingleton.elim _ _
    rw [hz]
    exact ⟨fun _ => JFA.hasSeparableRange_zero, fun _ => Subsingleton.elim _ _⟩

end Posets
