import BanachIsometric.Functional
import BanachIsometric.StarBodyCompact

/-!
# Theorem A's local regularity really produces star bodies

The auxiliary coordinates in the statement are arbitrary real Euclidean
coordinates. Positive homogeneity first makes the gauge globally Lipschitz;
bounded real-linear coordinate changes then transfer this regularity to
complex-linear Euclidean coordinates. Thus the geometry can use a Hermitian
auxiliary structure without strengthening the paper's regularity hypothesis.
-/

namespace BanachIsometric

open scoped NNReal

/-- The algebraic gauge conditions, with no ambient norm or topology. -/
structure AlgebraicPositiveHomogeneous {W : Type*} [AddCommGroup W] [Module ℝ W]
    (p : W → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  eq_zero_iff : ∀ x, p x = 0 ↔ x = 0
  smul_nonneg : ∀ t : ℝ, 0 ≤ t → ∀ x, p (t • x) = t * p x

theorem AlgebraicPositiveHomogeneous.pullback
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p : W → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f) :
    IsDefinitePositiveHomogeneous (fun v => p (f v)) where
  nonneg := fun v => hp.nonneg (f v)
  eq_zero_iff := fun v => by
    rw [hp.eq_zero_iff]
    constructor
    · intro h
      exact hf (h.trans f.map_zero.symm)
    · rintro rfl
      exact f.map_zero
  smul_nonneg := fun t ht v => by rw [f.map_smul, hp.smul_nonneg t ht]

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

attribute [local instance] RestrictScalars.moduleOrig

theorem IsDefiniteComplexHomogeneous.onSubmodule {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) (Y : Submodule ℂ X) :
    IsDefiniteComplexHomogeneous (fun y : Y => p (y : X)) where
  nonneg := fun y => hp.nonneg y
  eq_zero_iff := fun y => by
    rw [hp.eq_zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  smul := fun a y => hp.smul a y

theorem IsDefiniteComplexHomogeneous.restrictReal {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) :
    AlgebraicPositiveHomogeneous
      (fun x : RestrictScalars ℝ ℂ X => p (RestrictScalars.addEquiv ℝ ℂ X x)) where
  nonneg := fun x => hp.nonneg x
  eq_zero_iff := fun x => hp.eq_zero_iff x
  smul_nonneg := fun t ht x => by
    change p ((t : ℂ) • (x : X)) = t * p (x : X)
    rw [hp.smul, Complex.norm_real, Real.norm_of_nonneg ht]

private theorem realFiniteEuclidean (n : ℕ) :
    FiniteDimensional ℝ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) := by
  letI : Module.Finite ℂ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
    (inferInstance : Module.Finite ℂ (EuclideanSpace ℂ (Fin (n + 1))))
  exact Module.Finite.trans ℂ (RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))))

/-- Real Euclidean coordinates pull the algebraic gauge back to a positive
homogeneous function on an ordinary real normed space. -/
theorem coordinateGauge_positiveHomogeneous {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) (n : ℕ) (Y : Submodule ℂ X)
    (e : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y) :
    IsDefinitePositiveHomogeneous
      (fun v => p ((RestrictScalars.addEquiv ℝ ℂ Y) (e v) : X)) :=
  (hp.onSubmodule Y).restrictReal.pullback e.toLinearMap e.injective

/-- The paper's arbitrary auxiliary Euclidean regularity permits a complex
Hermitian choice of coordinates, without any extra assumption on `p` or `X`.
In those coordinates the gauge is globally Lipschitz, not just on the sphere. -/
theorem exists_complex_regular_coordinates {p : X → ℝ} (hp : IsDefiniteComplexHomogeneous p)
    {n : ℕ} (hsphere : ComplexSphereLipschitz n p)
    (Y : Submodule ℂ X) (hY : Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal)) :
    ∃ f : EuclideanSpace ℂ (Fin (n + 1)) ≃ₗ[ℂ] Y,
      ∃ L : ℝ≥0, LipschitzWith L (fun v => p (f v : X)) := by
  obtain ⟨e, C, hC⟩ := hsphere Y hY
  letI := realFiniteEuclidean n
  have hpE := coordinateGauge_positiveHomogeneous hp n Y e
  obtain ⟨L, hL⟩ := hpE.exists_lipschitzWith hC
  letI : Module.Finite ℂ Y := Module.finite_of_rank_eq_nat hY
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Module.finrank ℂ Y := by
    rw [Module.finrank_eq_of_rank_eq hY]
    simp
  let f := LinearEquiv.ofFinrankEq (EuclideanSpace ℂ (Fin (n + 1))) Y hdim
  let fr : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y :=
    { f.toAddEquiv with map_smul' := fun r x => f.map_smul (r : ℂ) x }
  let T : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) →L[ℝ]
      RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
    LinearMap.toContinuousLinearMap (fr.trans e.symm).toLinearMap
  refine ⟨f, L * ‖T‖₊, ?_⟩
  simpa [T, fr, Function.comp_def, RestrictScalars.addEquiv] using hL.comp T.lipschitz

/-- The unit gauge sublevel in the original real auxiliary coordinates is
compact, contains a neighbourhood of zero, and is regular closed. These are
proved consequences of Theorem A's hypotheses, without convexity. -/
theorem functional_coordinate_body_geometry {p : X → ℝ}
    (hp : IsDefiniteComplexHomogeneous p) {n : ℕ}
    (hsphere : ComplexSphereLipschitz n p) (Y : Submodule ℂ X)
    (hY : Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal)) :
    ∃ e : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y,
      let K := {v | p ((RestrictScalars.addEquiv ℝ ℂ Y) (e v) : X) ≤ 1}
      IsCompact K ∧ (0 : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) ∈ interior K ∧
        closure (interior K) = K := by
  obtain ⟨e, C, hC⟩ := hsphere Y hY
  letI := realFiniteEuclidean n
  have hpE := coordinateGauge_positiveHomogeneous hp n Y e
  obtain ⟨L, hL⟩ := hpE.exists_lipschitzWith hC
  exact ⟨e, hpE.isCompact_sublevel hC, hpE.zero_mem_interior_sublevel hC.continuousOn,
    (hpE.sublevel_eq_closure_interior hL.continuous).symm⟩

end BanachIsometric
