import JLMS.AlgebraNormCompletion
import JLMS.FinitePowerAutomaticContinuity
import JLMS.OperatorConjugation

/-!
# Corollary 9.2: the printed norm-maximality equivalence

Maximality quantifies over every submultiplicative vector norm, without
assuming that the competing norm is continuous or complete. The graph norm
of an algebra homomorphism proves the converse to the existing completion
argument. This allows the finite-power automatic-continuity result to give
the norm-maximality equivalence itself.

This module adds declarations; it does not change the earlier results.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

/-- Maximality in the precise sense of Section 1.1 of the article. -/
def AlgebraNormIsMaximal (𝕜 : Type w) [RCLike 𝕜] (B : Type u)
    [NonUnitalNormedRing B] [NormedSpace 𝕜 B] : Prop :=
  ∀ n : B → ℝ, IsAlgebraNorm 𝕜 n →
    ∃ C : ℝ, 0 < C ∧ ∀ x, n x ≤ C * ‖x‖

section GraphNorm
variable {B : Type u} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  {A : Type v} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

/-- The graph norm is an algebra norm even for a discontinuous homomorphism. -/
theorem isAlgebraNorm_homGraphNorm (φ : B →ₙₐ[𝕜] A) :
    IsAlgebraNorm 𝕜 (fun x => ‖x‖ + ‖φ x‖) := by
  refine ⟨⟨fun x => add_nonneg (norm_nonneg x) (norm_nonneg _), ?_, ?_, ?_⟩, ?_⟩
  · intro x
    constructor
    · intro h
      apply norm_eq_zero.mp
      linarith [norm_nonneg x, norm_nonneg (φ x)]
    · rintro rfl
      simp
  · intro x y
    dsimp only
    rw [map_add]
    linarith [norm_add_le x y, norm_add_le (φ x) (φ y)]
  · intro c x
    dsimp only
    rw [map_smul, norm_smul, norm_smul, mul_add]
  · intro x y
    dsimp only
    rw [map_mul]
    nlinarith [norm_mul_le x y, norm_mul_le (φ x) (φ y),
      mul_nonneg (norm_nonneg x) (norm_nonneg (φ y)),
      mul_nonneg (norm_nonneg (φ x)) (norm_nonneg y)]

/-- A maximal algebra norm makes all outgoing algebra homomorphisms continuous. -/
theorem continuous_hom_of_algebraNormIsMaximal
    (hB : AlgebraNormIsMaximal 𝕜 B) (φ : B →ₙₐ[𝕜] A) : Continuous φ := by
  obtain ⟨C, _hC, hbound⟩ := hB _ (isAlgebraNorm_homGraphNorm φ)
  let L : B →ₗ[𝕜] A := {
    toFun := φ
    map_add' := φ.map_add
    map_smul' := φ.map_smul }
  exact (L.mkContinuous C (fun x =>
    (le_add_of_nonneg_left (norm_nonneg x)).trans (hbound x))).continuous

end GraphNorm

/-- The complete norm-maximality/automatic-continuity characterization.
The targets may be nonunital; no completeness is imposed on competing norms. -/
theorem algebraNormIsMaximal_iff_automaticContinuity
    {B : Type u} [NormedRing B] [NormedSpace 𝕜 B]
    [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] :
    AlgebraNormIsMaximal 𝕜 B ↔
      ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
        [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
        ∀ φ : B →ₙₐ[𝕜] A, Continuous φ := by
  constructor
  · intro h A _ _ _ _ _ φ
    exact continuous_hom_of_algebraNormIsMaximal h φ
  · intro h n hn
    exact algebraNorm_upper_bound_of_automaticContinuity h n hn

section Operators
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance printedMaximalOperatorGroup : NormedAddCommGroup (E →L[𝕜] E) := inferInstance
local instance printedMaximalOperatorSpace : NormedSpace 𝕜 (E →L[𝕜] E) := inferInstance

def printedOneCoordinateEquiv : E ≃L[𝕜] (Fin 1 → E) where
  toFun x _ := x
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    exact congrArg f (Subsingleton.elim 0 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi (fun _ => continuous_id)
  continuous_invFun := continuous_apply 0

/-- **Corollary 9.2**, including both directions and the maximality property itself. -/
theorem corollary_9_2 [CompleteSpace E] :
    AlgebraNormIsMaximal 𝕜 (E →L[𝕜] E) ↔
      ∀ n : ℕ, 1 ≤ n →
        AlgebraNormIsMaximal 𝕜 ((Fin n → E) →L[𝕜] (Fin n → E)) := by
  constructor
  · intro h n _hn
    apply algebraNormIsMaximal_iff_automaticContinuity.mpr
    intro A _ _ _ _ _ φ
    exact continuous_operator_hom_of_finitePower
      (fun ψ => continuous_hom_of_algebraNormIsMaximal h ψ) φ
  · intro h
    apply algebraNormIsMaximal_iff_automaticContinuity.mpr
    intro A _ _ _ _ _ φ
    apply continuous_operator_hom_of_conjugation (printedOneCoordinateEquiv (𝕜 := 𝕜) E) φ
    exact continuous_hom_of_algebraNormIsMaximal (h 1 le_rfl) _

end Operators
end JLMS
