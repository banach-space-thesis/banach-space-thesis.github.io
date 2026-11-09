import JLMS.MatrixAutomaticContinuity
import JLMS.CompetingNorms

/-!
# Proposition 9.1, including both implications

The proposition is stated with the finite product topology on matrices.
The paper allows any matrix norm between the maximum entry norm and the
sum of the entry norms. `printedMatrixNormEquiv` proves that every such
norm gives exactly this topology; thus this choice does not restrict the
printed statement. No unit is required in a target algebra or preserved
by a homomorphism.

The forward proof is the paper's diagonal-corner and matrix-unit argument,
already checked in `MatrixAutomaticContinuity`. The reverse proof takes
the matrix size to be one, as in the article.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]
variable {B : Type u} [NormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]

/-- Evaluation identifies the algebra of one-by-one matrices with B. -/
def printedMatrixOneEvaluation : Matrix (Fin 1) (Fin 1) B →ₙₐ[𝕜] B where
  toFun M := M 0 0
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]

/-- Proposition 9.1: both directions, with the printed quantifier n ≥ 1. -/
theorem printed_proposition_9_1 [CompleteSpace B] :
    (∀ (A : Type v) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : B →ₙₐ[𝕜] A, Continuous φ) ↔
    (∀ n : ℕ, 1 ≤ n →
      ∀ (A : Type v) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
        [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
        ∀ θ : Matrix (Fin n) (Fin n) B →ₙₐ[𝕜] A, Continuous θ) := by
  constructor
  · intro hB n _ A _ _ _ _ _ θ
    exact continuous_matrix_hom_of_corners (hB A) θ
  · intro hM A _ _ _ _ _ φ
    have hθ := hM 1 le_rfl A (φ.comp printedMatrixOneEvaluation)
    have hι : Continuous (fun b : B => (fun _ _ => b : Matrix (Fin 1) (Fin 1) B)) :=
      continuous_pi (fun _ => continuous_pi (fun _ => continuous_id))
    exact hθ.comp hι

local instance printedMatrixNormedGroup (n : ℕ) :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) B) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → B))

local instance printedMatrixNormedSpace (n : ℕ) :
    NormedSpace 𝕜 (Matrix (Fin n) (Fin n) B) :=
  inferInstanceAs (NormedSpace 𝕜 (Fin n → Fin n → B))

/-- The paper's maximum-entry lower bound, written without choosing a maximum. -/
def PrintedMatrixNormBounds {n : ℕ} (q : Matrix (Fin n) (Fin n) B → ℝ) : Prop :=
  (∀ M i j, ‖M i j‖ ≤ q M) ∧
    ∀ M, q M ≤ ∑ i, ∑ j, ‖M i j‖

/-- Every matrix norm allowed in Section 9 induces the finite product topology. -/
def printedMatrixNormEquiv {n : ℕ}
    (q : Matrix (Fin n) (Fin n) B → ℝ) (hq : IsVectorNorm 𝕜 q)
    (hb : PrintedMatrixNormBounds q) :
    WithVectorNorm 𝕜 q hq ≃L[𝕜] Matrix (Fin n) (Fin n) B := by
  let e : WithVectorNorm 𝕜 q hq ≃ₗ[𝕜] Matrix (Fin n) (Fin n) B :=
    LinearEquiv.refl 𝕜 _
  have hlower (M : WithVectorNorm 𝕜 q hq) : ‖e M‖ ≤ 1 * ‖M‖ := by
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr
    intro i
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr (fun j => hb.1 M i j)
  have hupper (M : Matrix (Fin n) (Fin n) B) :
      ‖e.symm M‖ ≤ ((n : ℝ) * n) * ‖M‖ := by
    change q M ≤ _
    calc
      q M ≤ ∑ i, ∑ j, ‖M i j‖ := hb.2 M
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖M‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  exact {
    __ := e
    continuous_toFun := (e.toLinearMap.mkContinuous 1 hlower).continuous
    continuous_invFun := (e.symm.toLinearMap.mkContinuous ((n : ℝ) * n) hupper).continuous
  }

/-- Continuity in an allowed printed matrix norm is exactly product-topology continuity. -/
theorem continuous_printedMatrixNorm_iff {n : ℕ}
    (q : Matrix (Fin n) (Fin n) B → ℝ) (hq : IsVectorNorm 𝕜 q)
    (hb : PrintedMatrixNormBounds q) {A : Type*} [TopologicalSpace A]
    (f : Matrix (Fin n) (Fin n) B → A) :
    Continuous (fun M : WithVectorNorm 𝕜 q hq => f M) ↔ Continuous f := by
  let e := printedMatrixNormEquiv q hq hb
  constructor
  · intro hf
    exact hf.comp e.symm.continuous
  · intro hf
    exact hf.comp e.continuous

/-- Proposition 9.1 for an arbitrary choice of the matrix norms permitted
in the paragraph preceding the proposition. The norm family is indexed
only by the positive matrix sizes appearing in the printed statement. -/
theorem printed_proposition_9_1_with_matrix_norms [CompleteSpace B]
    (q : ∀ n : ℕ, 1 ≤ n → Matrix (Fin n) (Fin n) B → ℝ)
    (hq : ∀ n hn, IsVectorNorm 𝕜 (q n hn))
    (hb : ∀ n hn, PrintedMatrixNormBounds (q n hn)) :
    (∀ (A : Type v) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : B →ₙₐ[𝕜] A, Continuous φ) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n),
      ∀ (A : Type v) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
        [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
        ∀ θ : Matrix (Fin n) (Fin n) B →ₙₐ[𝕜] A,
          Continuous (fun M : WithVectorNorm 𝕜 (q n hn) (hq n hn) => θ M)) := by
  constructor
  · intro hB n hn A _ _ _ _ _ θ
    apply (continuous_printedMatrixNorm_iff (q n hn) (hq n hn) (hb n hn) θ).mpr
    exact (printed_proposition_9_1.mp hB) n hn A θ
  · intro hM
    apply printed_proposition_9_1.mpr
    intro n hn A _ _ _ _ _ θ
    exact (continuous_printedMatrixNorm_iff (q n hn) (hq n hn) (hb n hn) θ).mp
      (hM n hn A θ)

end JLMS
