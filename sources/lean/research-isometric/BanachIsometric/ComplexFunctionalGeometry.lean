import BanachIsometric.ComplexHyperplaneRepresentation
import BanachIsometric.FunctionalStarBody
import BanachIsometric.ComplexScalarPolarization

/-!
# The original complex functional hypotheses supply the geometric inputs

Section equivalences remain real-linear. The complex linear coordinate map
only chooses the ambient Hermitian geometry and transports its subspaces.
The final reconstruction uses the original complex scalar multiplication.
-/

namespace BanachIsometric

open Set MeasureTheory
open scoped NNReal

noncomputable section

section RealSectionConversion

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The paper's scalar-cast condition gives ordinary real linearity on the
actual restricted submodules, without imposing complex linearity. -/
def RealSectionEquiv.toRealSubmoduleEquiv {E F : Submodule ℂ V}
    (T : RealSectionEquiv E F) : E.restrictScalars ℝ ≃ₗ[ℝ] F.restrictScalars ℝ :=
  { T.toAddEquiv with
    map_smul' := fun r x => by
      change T.toAddEquiv (r • x) = r • T.toAddEquiv x
      rw [← IsScalarTower.algebraMap_smul ℂ r x,
        ← IsScalarTower.algebraMap_smul ℂ r (T.toAddEquiv x)]
      exact T.map_real_smul r x }

end RealSectionConversion

section Pullback

variable {X W : Type*} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Injective complex ambient coordinates transport the hypothesis on every
`n`-dimensional section; the transported section maps need only be real-linear. -/
theorem RealEquivalentSections.pullback {n : ℕ} {p : X → ℝ}
    (hp : RealEquivalentSections n p) (j : W →ₗ[ℂ] X) (hj : Function.Injective j) :
    RealEquivalentSections n (fun w => p (j w)) := by
  intro E F hE hF
  let eE := Submodule.equivMapOfInjective j hj E
  let eF := Submodule.equivMapOfInjective j hj F
  letI : FiniteDimensional ℂ (E.map j) := Module.Finite.of_surjective eE.toLinearMap eE.surjective
  letI : FiniteDimensional ℂ (F.map j) := Module.Finite.of_surjective eF.toLinearMap eF.surjective
  have hEm : Module.rank ℂ (E.map j) = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank, ← eE.finrank_eq, Module.finrank_eq_of_rank_eq hE]
  have hFm : Module.rank ℂ (F.map j) = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank, ← eF.finrank_eq, Module.finrank_eq_of_rank_eq hF]
  obtain ⟨T, hT⟩ := hp (E.map j) (F.map j) hEm hFm
  let S : RealSectionEquiv E F :=
    { toAddEquiv := eE.toAddEquiv.trans (T.toAddEquiv.trans eF.symm.toAddEquiv)
      map_real_smul := by
        intro r x
        change eF.symm (T.toAddEquiv (eE ((r : ℂ) • x))) =
          (r : ℂ) • eF.symm (T.toAddEquiv (eE x))
        rw [eE.map_smul, T.map_real_smul, eF.symm.map_smul] }
  refine ⟨S, ?_⟩
  intro x
  have hval : j (S.toAddEquiv x : W) = (T.toAddEquiv (eE x) : X) := by
    have h := congrArg Subtype.val (eF.apply_symm_apply (T.toAddEquiv (eE x)))
    exact h
  change p (j (S.toAddEquiv x)) = p (j x)
  rw [hval]
  exact hT (eE x)

end Pullback

section StandardAmbient

variable {n : ℕ} {p : ComplexHermitianAmbient n → ℝ}

theorem IsDefiniteComplexHomogeneous.standardAmbient_positiveHomogeneous
    (hp : IsDefiniteComplexHomogeneous p) : IsDefinitePositiveHomogeneous p where
  nonneg := hp.nonneg
  eq_zero_iff := hp.eq_zero_iff
  smul_nonneg := fun t ht x => by
    rw [← IsScalarTower.algebraMap_smul ℂ t x, hp.smul]
    change ‖(t : ℂ)‖ * p x = t * p x
    rw [Complex.norm_real, Real.norm_of_nonneg ht]

theorem RealEquivalentSections.complexHyperplaneField
    (hp : RealEquivalentSections n p)
    (u v : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    RealSectionEquivalent p (complexHyperplaneField n u) (complexHyperplaneField n v) := by
  let E := complexNormalHyperplane u.val
  let F := complexNormalHyperplane v.val
  have hE : Module.rank ℂ E = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank]
    exact congrArg Nat.cast (complexNormalHyperplane_finrank n u)
  have hF : Module.rank ℂ F = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank]
    exact congrArg Nat.cast (complexNormalHyperplane_finrank n v)
  obtain ⟨T, hT⟩ := hp E F hE hF
  let e := T.toRealSubmoduleEquiv
  change RealSectionEquivalent p (E.restrictScalars ℝ) (F.restrictScalars ℝ)
  refine ⟨e, ?_⟩
  have he : ∀ x : E.restrictScalars ℝ, p (e x : ComplexHermitianAmbient n) = p x := hT
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p (e x : ComplexHermitianAmbient n) ≤ 1
    rw [he]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change p (e.symm y : ComplexHermitianAmbient n) ≤ 1
    rw [← he (e.symm y), e.apply_symm_apply]
    exact hy

theorem nonempty_complexFunctional_exactSectionPrincipalData
    (μ : Measure (EuclideanSpace ℝ (Fin (2 * n)))) [μ.IsAddHaarMeasure]
    (hp : IsDefiniteComplexHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : ComplexHermitianAmbient n) 1))
    (hsections : RealEquivalentSections n p)
    (u₀ : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    Nonempty (ExactSectionPrincipalData (2 * n) p (complexHyperplaneField n) u₀) :=
  nonempty_complexHyperplane_exactSectionPrincipalData n μ
    hp.standardAmbient_positiveHomogeneous hC u₀
    (fun u => hsections.complexHyperplaneField u₀ u)

end StandardAmbient

section Reconstruction

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
  [IsScalarTower ℝ ℂ X]

/-- Once the actual square of the gauge is a real quadratic form, complex
homogeneity supplies its `I`-invariance and positivity internally. -/
theorem hasHermitianSquare_of_realQuadratic {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) (q : QuadraticForm ℝ X)
    (hq : ∀ x, q x = p x ^ 2) : HasHermitianSquare p := by
  have hpos : q.PosDef := by
    intro x hx
    rw [hq]
    exact sq_pos_iff.mpr ((hp.eq_zero_iff x).not.mpr hx)
  have hI : ∀ x, q (Complex.I • x) = q x := by
    intro x
    rw [hq, hq, hp.smul, Complex.norm_I, one_mul]
  obtain ⟨h, hh, _⟩ := existsUnique_complexHermitian_of_realQuadratic q hpos hI
  exact ⟨h, fun x => (hh x).trans (congrArg Complex.ofReal (hq x))⟩

end Reconstruction

end

end BanachIsometric
