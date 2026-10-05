import PEMS.ALMainFactorization
import PEMS.WeakCalkinComplementedReduction
import ThesisCommon.Analysis.LebesgueProductLpSelfCopies
import ThesisCommon.Analysis.OperatorAlgebraProductCopies

/-! The full algebra argument for an explicitly exhibited homogeneous model.
The model is an atomic ell-one space plus an arbitrary ell-one family of
actual Lebesgue probability products. Its self-copies and finite remainders
are constructed. Producing this model for every AL space is the separate
measure-classification step; no such representation is asserted here. -/
noncomputable section
open ThesisCommon MeasureTheory Set
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A concrete Banach-space version of the source decomposition. The outer
binary product uses the maximum norm, which is harmless for bounded isomorphisms. -/
abbrev LebesgueProductALModel (𝕜 : Type*) [RCLike 𝕜] (Γ I : Type*) (κ : I → Type*) :=
  lp (fun _ : Γ => 𝕜) 1 ×
    lp (fun i => Lp 𝕜 1 (Measure.infinitePi fun _ : κ i =>
      volume.restrict (Icc (0 : ℝ) 1))) 1

theorem exists_weakCalkinAlgebraNorm_upperBound_of_lebesgueProductModel
    {E Γ I : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (κ : I → Type*) [∀ i, Nonempty (κ i)]
    (e : E ≃L[𝕜] LebesgueProductALModel 𝕜 Γ I κ)
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  classical
  obtain ⟨J, P, hd, ho⟩ := exists_orthogonal_selfCopies_ellOne_lebesgueProducts (𝕜 := 𝕜) κ
  cases finite_or_infinite Γ with
  | inl hfin =>
    letI := hfin
    let d := e.trans (ContinuousLinearEquiv.prodComm 𝕜 _ _)
    exact exists_weakCalkinAlgebraNorm_upperBound_of_weaklyCompact_product d
      (weaklyCompact_id_finite_scalar_lp (𝕜 := 𝕜) (Γ := Γ) 1) J P hd ho m hm
  | inr hinf =>
    letI := hinf
    obtain ⟨J', P', hd', ho'⟩ := exists_orthogonal_selfCopies_infinite_lp
      (𝕜 := 𝕜) (E := 𝕜) (Γ := Γ) 1 (by simp)
    obtain ⟨J'', P'', hd'', ho''⟩ :=
      exists_orthogonal_selfCopies_prod J' P' J P hd' ho' hd ho
    obtain ⟨U, V, hdU, hoU⟩ := exists_orthogonal_selfCopies_of_equiv e J'' P'' hd'' ho''
    exact exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies U V hdU hoU m hm

theorem uniqueWeakCalkinAlgebraNorm_real_AL_of_lebesgueProductModel
    {E Γ I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (κ : I → Type*) [∀ i, Nonempty (κ i)] (hE : IsALSpace ℝ E)
    (e : E ≃L[ℝ] LebesgueProductALModel ℝ Γ I κ) :
    HasUniqueWeakCalkinAlgebraNorm ℝ E :=
  uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
    (fun T => weakEssentialNorm_eq_factorizationSup_real_AL T hE hE)
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_lebesgueProductModel κ e m hm)

theorem uniqueWeakCalkinAlgebraNorm_complex_AL_of_lebesgueProductModel
    {E Γ I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (κ : I → Type*) [∀ i, Nonempty (κ i)] (hE : IsALSpace ℂ E)
    (e : E ≃L[ℂ] LebesgueProductALModel ℂ Γ I κ) :
    HasUniqueWeakCalkinAlgebraNorm ℂ E :=
  uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
    (fun T => weakEssentialNorm_eq_factorizationSup_complex_AL T hE hE)
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_lebesgueProductModel κ e m hm)

end PEMS
