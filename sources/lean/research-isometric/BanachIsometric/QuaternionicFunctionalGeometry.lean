import BanachIsometric.QuaternionicHyperplaneGeometry
import BanachIsometric.QuaternionicStatements
import BanachIsometric.FunctionalStarBody

/-! Original quaternionic functional hypotheses supply the actual real
geometric data. All scalar coordinate maps preserve the right action through
Hᵐᵒᵖ; section equivalences retain only the stipulated real linearity. -/

namespace BanachIsometric.Quaternionic

open Set MeasureTheory
open scoped Quaternion NNReal

noncomputable section

attribute [local instance] RestrictScalars.moduleOrig

section CanonicalReal

variable {U W : Type*} [AddCommGroup U] [Module Hᵐᵒᵖ U]
    [AddCommGroup W] [Module Hᵐᵒᵖ W]

def canonicalRealEquiv (f : U ≃ₗ[Hᵐᵒᵖ] W) :
    RestrictScalars ℝ Hᵐᵒᵖ U ≃ₗ[ℝ] RestrictScalars ℝ Hᵐᵒᵖ W :=
  { f.toAddEquiv with map_smul' := fun r x => f.map_smul (algebraMap ℝ Hᵐᵒᵖ r) x }

variable [Module ℝ U] [IsScalarTower ℝ Hᵐᵒᵖ U]

def domainRealEquiv (f : U ≃ₗ[Hᵐᵒᵖ] W) : U ≃ₗ[ℝ] RestrictScalars ℝ Hᵐᵒᵖ W :=
  { f.toAddEquiv with
    map_smul' := by
      intro r x
      change f (r • x) = (algebraMap ℝ Hᵐᵒᵖ r) • f x
      rw [← algebraMap_smul Hᵐᵒᵖ r x, f.map_smul] }

def realSubmoduleCanonicalEquiv (Y : Submodule Hᵐᵒᵖ U) :
    Y.restrictScalars ℝ ≃ₗ[ℝ] RestrictScalars ℝ Hᵐᵒᵖ Y :=
  { AddEquiv.refl Y with
    map_smul' := by
      intro r x
      apply Subtype.ext
      change r • (x : U) = (algebraMap ℝ Hᵐᵒᵖ r) • (x : U)
      exact (algebraMap_smul Hᵐᵒᵖ r (x : U)).symm }

end CanonicalReal

section Pullback

variable {X W : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X]
    [AddCommGroup W] [Module Hᵐᵒᵖ W]

theorem IsDefiniteHomogeneous.pullback {p : X → ℝ} (hp : IsDefiniteHomogeneous p)
    (j : W →ₗ[Hᵐᵒᵖ] X) (hj : Function.Injective j) :
    IsDefiniteHomogeneous (fun w => p (j w)) where
  nonneg w := hp.nonneg (j w)
  eq_zero_iff w := by
    rw [hp.eq_zero_iff]
    exact ⟨fun h => hj (h.trans j.map_zero.symm), fun h => by rw [h, j.map_zero]⟩
  right_mul w a := by
    change p (j (MulOpposite.op a • w)) = p (j w) * ‖a‖
    rw [j.map_smul]
    exact hp.right_mul (j w) a

theorem RealEquivalentSections.pullback [FiniteDimensional Hᵐᵒᵖ W] {n : ℕ} {p : X → ℝ}
    (hp : RealEquivalentSections n p) (j : W →ₗ[Hᵐᵒᵖ] X) (hj : Function.Injective j) :
    RealEquivalentSections n (fun w => p (j w)) := by
  intro E F hE hF
  let eE := Submodule.equivMapOfInjective j hj E
  let eF := Submodule.equivMapOfInjective j hj F
  letI : FiniteDimensional Hᵐᵒᵖ (E.map j) := Module.Finite.of_surjective eE.toLinearMap eE.surjective
  letI : FiniteDimensional Hᵐᵒᵖ (F.map j) := Module.Finite.of_surjective eF.toLinearMap eF.surjective
  have hEm : Module.rank Hᵐᵒᵖ (E.map j) = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank, ← eE.finrank_eq, Module.finrank_eq_of_rank_eq hE]
  have hFm : Module.rank Hᵐᵒᵖ (F.map j) = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank, ← eF.finrank_eq, Module.finrank_eq_of_rank_eq hF]
  obtain ⟨T, hT⟩ := hp (E.map j) (F.map j) hEm hFm
  let S := (canonicalRealEquiv eE).trans (T.trans (canonicalRealEquiv eF).symm)
  refine ⟨S, ?_⟩
  intro x
  have hval : j ((RestrictScalars.addEquiv ℝ Hᵐᵒᵖ F (S x)).val) =
      (RestrictScalars.addEquiv ℝ Hᵐᵒᵖ (F.map j) (T (eE x))).val :=
    congrArg Subtype.val (eF.apply_symm_apply (T (eE x)))
  change p (j ((RestrictScalars.addEquiv ℝ Hᵐᵒᵖ F (S x)).val)) =
    p (j ((RestrictScalars.addEquiv ℝ Hᵐᵒᵖ E x).val))
  rw [hval]
  exact hT (eE x)

end Pullback

section RealHomogeneity

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X]

theorem IsDefiniteHomogeneous.restrictReal {p : X → ℝ} (hp : IsDefiniteHomogeneous p) :
    AlgebraicPositiveHomogeneous (fun x : RestrictScalars ℝ Hᵐᵒᵖ X =>
      p (RestrictScalars.addEquiv ℝ Hᵐᵒᵖ X x)) where
  nonneg x := hp.nonneg x
  eq_zero_iff x := hp.eq_zero_iff x
  smul_nonneg t ht x := by
    change p (rightMul (x : X) (t : H)) = t * p x
    rw [hp.right_mul, Quaternion.norm_coe, Real.norm_of_nonneg ht, mul_comm]

end RealHomogeneity

section StandardAmbient

variable {n : ℕ} {p : HermitianAmbient n → ℝ}

theorem IsDefiniteHomogeneous.standardAmbient_positiveHomogeneous
    (hp : IsDefiniteHomogeneous p) : IsDefinitePositiveHomogeneous p where
  nonneg := hp.nonneg
  eq_zero_iff := hp.eq_zero_iff
  smul_nonneg t ht x := by
    rw [← rightMul_real x t, hp.right_mul, Quaternion.norm_coe, Real.norm_of_nonneg ht, mul_comm]

theorem RealEquivalentSections.hyperplaneField (hp : RealEquivalentSections n p)
    (u v : Metric.sphere (0 : HermitianAmbient n) 1) :
    RealSectionEquivalent p (hyperplaneField n u) (hyperplaneField n v) := by
  let E := scalarNormalHyperplane (n + 1) u.val
  let F := scalarNormalHyperplane (n + 1) v.val
  have hE : Module.rank Hᵐᵒᵖ E = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank]
    exact congrArg Nat.cast (scalarNormalHyperplane_finrank n u.val
      (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property))
  have hF : Module.rank Hᵐᵒᵖ F = (n : Cardinal) := by
    rw [← Module.finrank_eq_rank]
    exact congrArg Nat.cast (scalarNormalHyperplane_finrank n v.val
      (by simpa only [Metric.mem_sphere, dist_zero_right] using v.property))
  obtain ⟨T, hT⟩ := hp E F hE hF
  let e := (realSubmoduleCanonicalEquiv E).trans (T.trans (realSubmoduleCanonicalEquiv F).symm)
  change RealSectionEquivalent p (E.restrictScalars ℝ) (F.restrictScalars ℝ)
  refine ⟨e, ?_⟩
  have he : ∀ x : E.restrictScalars ℝ, p (e x : HermitianAmbient n) = p x := hT
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p (e x : HermitianAmbient n) ≤ 1
    rw [he]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change p (e.symm y : HermitianAmbient n) ≤ 1
    rw [← he (e.symm y), e.apply_symm_apply]
    exact hy

theorem nonempty_functional_exactSectionPrincipalData
    (μ : Measure (EuclideanSpace ℝ (Fin (4 * n)))) [μ.IsAddHaarMeasure]
    (hp : IsDefiniteHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : HermitianAmbient n) 1))
    (hSections : RealEquivalentSections n p) (u₀ : Metric.sphere (0 : HermitianAmbient n) 1) :
    Nonempty (ExactSectionPrincipalData (4 * n) p (hyperplaneField n) u₀) :=
  nonempty_hyperplane_exactSectionPrincipalData n μ hp.standardAmbient_positiveHomogeneous
    hSphere u₀ (fun u => hSections.hyperplaneField u₀ u)

end StandardAmbient

section Reconstruction

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X] [IsScalarTower ℝ Hᵐᵒᵖ X]

theorem hasHermitianSquare_of_realQuadratic {p : X → ℝ} (hp : IsDefiniteHomogeneous p)
    (q : QuadraticForm ℝ X) (hq : ∀ x, q x = p x ^ 2) : HasHermitianSquare p := by
  have hpos : q.PosDef := by
    intro x hx
    rw [hq]
    exact sq_pos_iff.mpr ((hp.eq_zero_iff x).not.mpr hx)
  have hscale : ∀ x a, q (rightMul x a) = q x * ‖a‖ ^ 2 := by
    intro x a
    rw [hq, hq, hp.right_mul, mul_pow]
  obtain ⟨h, hh, _⟩ := existsUnique_of_quadraticForm q hpos hscale
  exact ⟨h, (fun x => (hh.1 x).trans (congrArg (fun r : ℝ => (r : H)) (hq x))), hh.2⟩

end Reconstruction

end
end BanachIsometric.Quaternionic
