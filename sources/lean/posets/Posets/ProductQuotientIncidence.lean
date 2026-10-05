import Posets.ProductQuotientTransport
import Posets.FiniteStrongSplit
import Posets.QuotientSection

/-! Represented finite and countable incidence factors in the product theorem. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets

variable {𝕜 C : Type} [RCLike 𝕜]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]

theorem exists_productFiniteIncidence_strongSplit
    {P : Type} [Fintype P] [PartialOrder P] [Nonempty P]
    {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] {ι : ∀ s t, X s →L[𝕜] X t}
    (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)
    (hc : RepresentedBy 𝕜 C (P → 𝕜) (oppositeFiniteIncidenceOperators 𝕜 P)) :
    ∃ θ : BoundedHom 𝕜 ((∀ p, X p) →L[𝕜] (∀ p, X p)) C,
    ∃ ρ : BoundedHom 𝕜 C ((∀ p, X p) →L[𝕜] (∀ p, X p)),
      StrongSplit 𝕜 (∀ p, X p) C θ ρ ∧ Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  obtain ⟨S, hS, θ, ρ, hsplit, hρ, hθ⟩ := proposition_6_6_proof 𝕜 P X ι h hcommon
  obtain ⟨c, hc'⟩ := representedBy_subalgebra_coordinates S (by rwa [hS])
  exact product_strongSplit_coordinates c hc' θ ρ hsplit hρ hθ.le

theorem exists_productFiniteIncidenceSum_strongSplit
    {P : Type} [Fintype P] [PartialOrder P] [Nonempty P]
    {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] {ι : ∀ s t, X s →L[𝕜] X t}
    (h : FewOperators 𝕜 X ι) (hcommon : CommonSubspace 𝕜 X ι)
    (hc : RepresentedBy 𝕜 C (P → 𝕜) (oppositeFiniteIncidenceOperators 𝕜 P)) :
    ∃ θ : BoundedHom 𝕜 (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) C,
    ∃ ρ : BoundedHom 𝕜 C (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 X) C θ ρ ∧ Isometry ρ ∧
        ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  obtain ⟨θ, ρ, hsplit, hρ, hθ⟩ := exists_productFiniteIncidence_strongSplit h hcommon hc
  let e := (finiteCZeroSumEquiv (𝕜 := 𝕜) X).symm
  let c := LinearIsometryEquiv.refl 𝕜 C
  have hc' : ∀ a b, c (a * b) = c a * c b := fun _ _ => rfl
  refine ⟨transportQuotient e c hc' θ, transportSection e c hc' ρ,
    strongSplit_transport e c hc' θ ρ hsplit,
    isometry_transportSection e c hc' ρ hρ, ?_⟩
  rwa [norm_transportQuotient]

theorem exists_productCountableIncidence_strongSplit
    {P : Type} [PartialOrder P] [Countable P] [Nonempty P]
    {X : BoundedExtension P → Type}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    [∀ p, CompleteSpace (X p)] {ι : ∀ s t, X s →L[𝕜] X t}
    (h : FewOperators 𝕜 X ι)
    (hc : RepresentedBy 𝕜 C (CZeroOn 𝕜 P) (oppositeIncidenceOperators 𝕜 P)) :
    ∃ θ : BoundedHom 𝕜
      (DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
        DependentCZeroSum 𝕜 (fun p : P => X (middle p))) C,
    ∃ ρ : BoundedHom 𝕜 C
      (DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
        DependentCZeroSum 𝕜 (fun p : P => X (middle p))),
      StrongSplit 𝕜 (DependentCZeroSum 𝕜 (fun p : P => X (middle p))) C θ ρ ∧
        Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 := by
  obtain ⟨c, hc'⟩ := representedBy_subalgebra_coordinates (oppositeIncidenceSubalgebra 𝕜 P) hc
  apply product_strongSplit_coordinates c hc' (scalarQuotientHom h)
    (incidenceLiftHom (middleFewOperators h))
  · exact ⟨(scalarQuotientMap_rightInverse h).surjective,
      scalarQuotientMap_eq_zero_iff h, scalarQuotientMap_rightInverse h⟩
  · exact incidenceLift_isometry h
  · exact (norm_scalarQuotientMap h).le

end Posets
