import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# The complex functional statement (Theorem A)

This file states the functional theorem without assuming a norm, topology,
convexity, or the triangle inequality on the ambient complex vector space.
`ComplexFunctionalStatement` is a proposition, not a claimed proof.
-/

namespace BanachIsometric

universe u

open scoped NNReal

variable {X : Type u} [AddCommGroup X] [Module ℂ X]

/-- Nonnegative, definite, complex absolutely homogeneous functions. -/
structure IsDefiniteComplexHomogeneous (p : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  eq_zero_iff : ∀ x, p x = 0 ↔ x = 0
  smul : ∀ (a : ℂ) x, p (a • x) = ‖a‖ * p x

/-- An additive bijection which is linear for real scalars. Encoding real
scalars as complex scalars avoids choosing any topology or scalar restriction
on the ambient algebraic vector space. -/
structure RealSectionEquiv (E F : Submodule ℂ X) extends E ≃+ F where
  map_real_smul : ∀ (r : ℝ) x, toAddEquiv ((r : ℂ) • x) = (r : ℂ) • toAddEquiv x

/-- The scalar-cast encoding is ordinary real linearity on the restricted
scalar modules. -/
def RealSectionEquiv.toRealLinearEquiv {E F : Submodule ℂ X}
    (T : RealSectionEquiv E F) :
    RestrictScalars ℝ ℂ E ≃ₗ[ℝ] RestrictScalars ℝ ℂ F :=
  { T.toAddEquiv with map_smul' := T.map_real_smul }

/-- The converse conversion makes explicit that no complex-linearity has been
imposed on the section equivalences. -/
def RealSectionEquiv.ofRealLinearEquiv {E F : Submodule ℂ X}
    (T : RestrictScalars ℝ ℂ E ≃ₗ[ℝ] RestrictScalars ℝ ℂ F) :
    RealSectionEquiv E F :=
  { T.toAddEquiv with map_real_smul := T.map_smul }

theorem nonempty_realSectionEquiv_iff (E F : Submodule ℂ X) :
    Nonempty (RealSectionEquiv E F) ↔
      Nonempty (RestrictScalars ℝ ℂ E ≃ₗ[ℝ] RestrictScalars ℝ ℂ F) :=
  ⟨fun ⟨T⟩ ↦ ⟨T.toRealLinearEquiv⟩, fun ⟨T⟩ ↦ ⟨.ofRealLinearEquiv T⟩⟩

/-- The section maps in Theorem A need only be real-linear. -/
def RealEquivalentSections (n : ℕ) (p : X → ℝ) : Prop :=
  ∀ E F : Submodule ℂ X,
    Module.rank ℂ E = (n : Cardinal) → Module.rank ℂ F = (n : Cardinal) →
    ∃ T : RealSectionEquiv E F, ∀ x : E, p (T.toAddEquiv x : X) = p (x : X)

/-- Local sphere regularity in some auxiliary real Euclidean coordinates on
every `(n+1)`-dimensional complex subspace. The coordinate map is real-linear,
so the auxiliary Euclidean structure need not respect complex scalars.
There is no norm on `X` here. -/
def ComplexSphereLipschitz (n : ℕ) (p : X → ℝ) : Prop :=
  ∀ Y : Submodule ℂ X, Module.rank ℂ Y = ((n + 1 : ℕ) : Cardinal) →
    ∃ e : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y,
      ∃ C : ℝ≥0, LipschitzOnWith C
        (fun v ↦ p ((RestrictScalars.addEquiv ℝ ℂ Y) (e v) : X)) (Metric.sphere 0 1)

/-- A positive-definite complex Hermitian form, linear in its second argument.
The first argument's conjugate-linearity follows from Hermitian symmetry. -/
structure PositiveHermitianForm (X : Type u) [AddCommGroup X] [Module ℂ X] where
  form : X → X → ℂ
  conj_symm : ∀ x y, star (form x y) = form y x
  add_right : ∀ x y z, form x (y + z) = form x y + form x z
  smul_right : ∀ x y (a : ℂ), form x (a • y) = a * form x y
  self_im : ∀ x, (form x x).im = 0
  self_nonneg : ∀ x, 0 ≤ (form x x).re
  self_pos : ∀ x, x ≠ 0 → 0 < (form x x).re

/-- The given function, rather than an unrelated norm, is squared by the form. -/
def HasHermitianSquare (p : X → ℝ) : Prop :=
  ∃ h : PositiveHermitianForm X, ∀ x, h.form x x = ((p x ^ 2 : ℝ) : ℂ)

/-- The complete complex assertion of Theorem A. This declaration specifies
the theorem to be proved; it does not assume or prove that assertion. -/
def ComplexFunctionalStatement : Prop :=
  ∀ (n : ℕ) (p : X → ℝ), 2 ≤ n → (n : Cardinal) < Module.rank ℂ X →
    IsDefiniteComplexHomogeneous p → ComplexSphereLipschitz n p →
    RealEquivalentSections n p → HasHermitianSquare p

section Norm

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Norms satisfy the exact algebraic hypotheses in Theorem A. -/
theorem norm_isDefiniteComplexHomogeneous :
    IsDefiniteComplexHomogeneous (norm : V → ℝ) where
  nonneg := norm_nonneg
  eq_zero_iff := fun _ ↦ norm_eq_zero
  smul := fun _ _ ↦ norm_smul _ _

/-- In Euclidean coordinates any linear map into a normed space is Lipschitz.
This is the automatic regularity required when Theorem A is applied to norms. -/
theorem norm_complexSphereLipschitz (n : ℕ) :
    ComplexSphereLipschitz n (norm : V → ℝ) := by
  intro Y hY
  letI : Module.Finite ℂ Y := Module.finite_of_rank_eq_nat hY
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) =
      Module.finrank ℂ Y := by
    rw [Module.finrank_eq_of_rank_eq hY]
    simp
  let e := LinearEquiv.ofFinrankEq (EuclideanSpace ℂ (Fin (n + 1))) Y hdim
  let er : RestrictScalars ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1))) ≃ₗ[ℝ]
      RestrictScalars ℝ ℂ Y :=
    { e.toAddEquiv with map_smul' := fun r x ↦ e.map_smul (r : ℂ) x }
  let f : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] V :=
    LinearMap.toContinuousLinearMap (Y.subtype.comp e.toLinearMap)
  refine ⟨er, ‖f‖₊, ?_⟩
  have hf : LipschitzWith ‖f‖₊ f := f.lipschitz
  simpa [f, er, RestrictScalars.addEquiv, Function.comp_def] using
    (lipschitzWith_one_norm.comp hf).lipschitzOnWith

/-- A compatible inner product gives precisely the paper's Hermitian-square
conclusion for the existing norm. -/
theorem norm_hasHermitianSquare {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] : HasHermitianSquare (norm : W → ℝ) := by
  refine ⟨{
    form := inner ℂ
    conj_symm := fun x y ↦ inner_conj_symm (𝕜 := ℂ) y x
    add_right := fun x y z ↦ inner_add_right (𝕜 := ℂ) x y z
    smul_right := fun x y a ↦ inner_smul_right (𝕜 := ℂ) x y a
    self_im := fun x ↦ inner_self_im (𝕜 := ℂ) x
    self_nonneg := fun x ↦ inner_self_nonneg (𝕜 := ℂ) (x := x)
    self_pos := fun _ hx ↦ (re_inner_self_pos (𝕜 := ℂ)).mpr hx
  }, ?_⟩
  intro x
  simpa only [Complex.ofReal_pow] using inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x

/-- Reconstruct the compatible inner product from the explicitly stated
Hermitian form. This construction retains the given norm and needs no
completeness assumption. -/
noncomputable def PositiveHermitianForm.toInnerProductSpace
    (h : PositiveHermitianForm V)
    (hn : ∀ x, h.form x x = ((‖x‖ ^ 2 : ℝ) : ℂ)) : InnerProductSpace ℂ V where
  inner := h.form
  norm_sq_eq_re_inner x := by rw [hn]; rfl
  conj_inner_symm x y := h.conj_symm y x
  add_left x y z := by
    calc
      h.form (x + y) z = star (h.form z (x + y)) := (h.conj_symm z _).symm
      _ = star (h.form z x + h.form z y) := congrArg star (h.add_right z x y)
      _ = h.form x z + h.form y z := by rw [star_add, h.conj_symm, h.conj_symm]
  smul_left x y a := by
    calc
      h.form (a • x) y = star (h.form y (a • x)) := (h.conj_symm y _).symm
      _ = star (a * h.form y x) := congrArg star (h.smul_right y x a)
      _ = star a * h.form x y := by rw [star_mul, h.conj_symm, mul_comm]

/-- A semantic check: for a norm, the explicit Hermitian-form conclusion for
the existing complex scalar action and mathlib's inner-product structure are
equivalent. `InnerProductSpace` packages its own `NormedSpace` (and hence scalar
action), so the reverse implication first extracts the scalar-independent
parallelogram law under the supplied witness, then reconstructs an inner
product using the ORIGINAL `NormedSpace` outside that witness's local scope. -/
theorem norm_hasHermitianSquare_iff :
    HasHermitianSquare (norm : V → ℝ) ↔ Nonempty (InnerProductSpace ℂ V) := by
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h.toInnerProductSpace hn⟩
  · rintro ⟨h⟩
    have hpar : ∀ x y : V,
        ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
          2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
      letI := h
      exact parallelogram_law_with_norm ℂ
    letI : InnerProductSpace ℂ V := InnerProductSpace.ofNorm ℂ hpar
    exact norm_hasHermitianSquare

/-- The paper's metric section hypothesis supplies precisely the real-linear
norm-preserving equivalences in Theorem A, by Mazur--Ulam. -/
theorem metricSubspaceHomogeneity_realEquivalentSections {n : ℕ}
    (h : ∀ E F : Submodule ℂ V,
      Module.rank ℂ E = (n : Cardinal) → Module.rank ℂ F = (n : Cardinal) →
      Nonempty (E ≃ᵢ F)) :
    RealEquivalentSections n (norm : V → ℝ) := by
  intro E F hE hF
  obtain ⟨g⟩ := h E F hE hF
  let e :=
    (show RestrictScalars ℝ ℂ E ≃ᵢ RestrictScalars ℝ ℂ F from g).toRealLinearIsometryEquiv
  refine ⟨{
    toAddEquiv := e.toLinearEquiv.toAddEquiv
    map_real_smul := ?_
  }, ?_⟩
  · intro r x
    exact e.map_smul r x
  · intro x
    exact e.norm_map x

/-- The normed complex corollary follows from the functional theorem.
The functional theorem is an explicit premise: this is a proved reduction,
not a proof of its currently unproved geometric input. -/
theorem complexFunctionalStatement_implies_corollaryB
    (h : ComplexFunctionalStatement (X := V)) (n : ℕ) :
    2 ≤ n → (n : Cardinal) < Module.rank ℂ V →
      (∀ E F : Submodule ℂ V,
        Module.rank ℂ E = (n : Cardinal) → Module.rank ℂ F = (n : Cardinal) →
        Nonempty (E ≃ᵢ F)) → Nonempty (InnerProductSpace ℂ V) := by
  intro hn hdim hmetric
  apply norm_hasHermitianSquare_iff.mp
  exact h n norm hn hdim norm_isDefiniteComplexHomogeneous
    (norm_complexSphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections hmetric)

end Norm

end BanachIsometric
