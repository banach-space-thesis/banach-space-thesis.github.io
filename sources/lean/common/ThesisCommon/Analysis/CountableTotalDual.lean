import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic

/-! Countable total sets in the actual bounded dual, as used in Section 4. -/
namespace ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A countable family of bounded scalar functionals separates zero from
every nonzero vector. No basis or separability conclusion is included. -/
def HasCountableTotalDual : Prop :=
  ∃ M : Set (X →L[𝕜] 𝕜), M.Countable ∧
    ∀ x : X, (∀ φ ∈ M, φ x = 0) → x = 0

end ThesisCommon
