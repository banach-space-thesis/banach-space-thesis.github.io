import ThesisCommon.QuotientOperator

noncomputable section
namespace ThesisCommon

theorem submodule_mapQ_eq_zero_iff {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) (T : M →ₗ[R] N)
    (h : p ≤ q.comap T) : p.mapQ q T h = 0 ↔ ∀ x, T x ∈ q := by
  constructor
  · intro hz x
    have he := LinearMap.congr_fun hz (Submodule.Quotient.mk x)
    change (Submodule.Quotient.mk (T x) : N ⧸ q) = 0 at he
    exact (Submodule.Quotient.mk_eq_zero q).mp he
  · intro hz
    apply LinearMap.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x =>
      change (Submodule.Quotient.mk (T x) : N ⧸ q) = 0
      exact (Submodule.Quotient.mk_eq_zero q).mpr (hz x)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem quotientOperator_eq_zero_iff (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (T : E →L[𝕜] F) (h : p ≤ q.comap T.toLinearMap) :
    quotientOperator p q T h = 0 ↔ ∀ x, T x ∈ q := by
  constructor
  · intro hz x
    have he := congrArg (fun A : (E ⧸ p) →L[𝕜] (F ⧸ q) =>
      A (Submodule.Quotient.mk x)) hz
    change (Submodule.Quotient.mk (T x) : F ⧸ q) = 0 at he
    exact (Submodule.Quotient.mk_eq_zero q).mp he
  · intro hz
    apply ContinuousLinearMap.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x =>
      change (Submodule.Quotient.mk (T x) : F ⧸ q) = 0
      exact (Submodule.Quotient.mk_eq_zero q).mpr (hz x)

end ThesisCommon
