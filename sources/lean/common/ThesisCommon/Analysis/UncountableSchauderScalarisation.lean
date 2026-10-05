import ThesisCommon.Analysis.UncountableSchauderSumSupport
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Coordinatewise scalarisation of the actual arbitrary-index basis sum.
Solidity constructs the scalar vector, and its coordinates prove linearity.
Hahn–Banach then converts countable scalar operator support into countable
vector-valued operator support, as in manuscript Lemma 4.14.
-/
noncomputable section
namespace ThesisCommon
namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

private theorem scalarisation_exists (φ : Γ → X →L[𝕜] 𝕜)
    (hφ : ∀ γ, ‖φ γ‖ ≤ 1) (x : UncountableSchauderSum b hb X) :
    ∃ y : E, (∀ γ, b.coord γ y = φ γ (x γ)) ∧ ‖y‖ ≤ ‖x‖ := by
  apply b.exists_of_coord_domination hb (normVector x)
  intro γ
  rw [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖φ γ (x γ)‖ ≤ ‖φ γ‖ * ‖x γ‖ := (φ γ).le_opNorm _
    _ ≤ 1 * ‖x γ‖ := mul_le_mul_of_nonneg_right (hφ γ) (norm_nonneg _)
    _ = ‖x γ‖ := one_mul _

/-- The genuine scalar vector with coefficients φγ(xγ). -/
def scalarisationValue (φ : Γ → X →L[𝕜] 𝕜) (hφ : ∀ γ, ‖φ γ‖ ≤ 1)
    (x : UncountableSchauderSum b hb X) : E :=
  (scalarisation_exists φ hφ x).choose

@[simp] theorem coord_scalarisationValue (φ : Γ → X →L[𝕜] 𝕜)
    (hφ : ∀ γ, ‖φ γ‖ ≤ 1) (x : UncountableSchauderSum b hb X) (γ : Γ) :
    b.coord γ (scalarisationValue φ hφ x) = φ γ (x γ) :=
  (scalarisation_exists φ hφ x).choose_spec.1 γ

theorem norm_scalarisationValue_le (φ : Γ → X →L[𝕜] 𝕜)
    (hφ : ∀ γ, ‖φ γ‖ ≤ 1) (x : UncountableSchauderSum b hb X) :
    ‖scalarisationValue φ hφ x‖ ≤ ‖x‖ :=
  (scalarisation_exists φ hφ x).choose_spec.2

/-- Coordinate functionals in the dual unit ball give an actual contraction
from E(Γ,X) into the original scalar space E. -/
def scalarisation (φ : Γ → X →L[𝕜] 𝕜) (hφ : ∀ γ, ‖φ γ‖ ≤ 1) :
    UncountableSchauderSum b hb X →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := scalarisationValue φ hφ
      map_add' := by
        intro x y
        apply b.ext
        intro γ
        simp
      map_smul' := by
        intro c x
        apply b.ext
        intro γ
        simp }
    1 (fun x => by simpa using norm_scalarisationValue_le φ hφ x)

@[simp] theorem coord_scalarisation (φ : Γ → X →L[𝕜] 𝕜)
    (hφ : ∀ γ, ‖φ γ‖ ≤ 1) (x : UncountableSchauderSum b hb X) (γ : Γ) :
    b.coord γ (scalarisation φ hφ x) = φ γ (x γ) :=
  coord_scalarisationValue φ hφ x γ

theorem norm_scalarisation_le (φ : Γ → X →L[𝕜] 𝕜)
    (hφ : ∀ γ, ‖φ γ‖ ≤ 1) :
    ‖scalarisation (b := b) (hb := hb) φ hφ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Lemma 4.14. One normed witness is chosen at every active coordinate.
The scalar-support hypothesis applied to the resulting Hahn–Banach
scalarisation excludes all active coordinates outside one countable set.
No separability or nontriviality hypothesis on X is needed. -/
theorem operator_countable_support_of_scalar
    (hscalar : ∀ S : X →L[𝕜] E, ∃ Λ : Set Γ, Λ.Countable ∧
      ∀ x : X, ∀ γ ∉ Λ, b.coord γ (S x) = 0)
    (T : X →L[𝕜] UncountableSchauderSum b hb X) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hw : ∀ γ, ∃ x : X, (∃ y : X, T y γ ≠ 0) → T x γ ≠ 0 := by
    intro γ
    by_cases h : ∃ y : X, T y γ ≠ 0
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose x hx using hw
  choose φ hφ hφx using fun γ => exists_dual_vector'' 𝕜 (T (x γ) γ)
  obtain ⟨Λ, hΛ, hzero⟩ := hscalar ((scalarisation φ hφ).comp T)
  refine ⟨Λ, hΛ, ?_⟩
  intro y γ hγ
  by_contra hy
  have hn : T (x γ) γ ≠ 0 := hx γ ⟨y, hy⟩
  have hz := hzero (x γ) γ hγ
  simp only [ContinuousLinearMap.comp_apply, coord_scalarisation, hφx] at hz
  exact (norm_ne_zero_iff.mpr hn) (RCLike.ofReal_eq_zero.mp hz)

end UncountableSchauderSum
end ThesisCommon
