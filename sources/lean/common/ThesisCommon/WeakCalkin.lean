import ThesisCommon.WeakCompact
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The actual quotient vector space B(E)/W(E). -/
abbrev WeakCalkin := (E →L[𝕜] E) ⧸ weaklyCompactSubmodule 𝕜 E E

def weakCalkinMk (T : E →L[𝕜] E) : WeakCalkin 𝕜 E := Submodule.Quotient.mk T

/-- An arbitrary algebra norm on quotient classes. The multiplication condition
is written on representatives [S][T]=[ST]. The checked left/right composition
lemmas guarantee that W(E) is a two-sided ideal. No completeness, continuity
relative to the original norm, or normalization of the identity is required. -/
def IsWeakCalkinAlgebraNorm (n : WeakCalkin 𝕜 E → ℝ) : Prop :=
  (∀ x, 0 ≤ n x) ∧
  (∀ x, n x = 0 ↔ x = 0) ∧
  (∀ x y, n (x + y) ≤ n x + n y) ∧
  (∀ a : 𝕜, ∀ x, n (a • x) = ‖a‖ * n x) ∧
  (∀ S T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E (S.comp T)) ≤
    n (weakCalkinMk 𝕜 E S) * n (weakCalkinMk 𝕜 E T))

/-- The candidate is an actual algebra norm on the quotient and is minimal.
Specifying its pullback avoids assuming its well-definedness as an extra input. -/
def IsMinimalWeakCalkinNorm (p : (E →L[𝕜] E) → ℝ) : Prop :=
  ∃ n : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E n ∧
    (∀ T, n (weakCalkinMk 𝕜 E T) = p T) ∧
    ∀ m, IsWeakCalkinAlgebraNorm 𝕜 E m →
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * n x ≤ m x

/-- Existence and equivalence of all algebra norms, including incomplete ones. -/
def HasUniqueWeakCalkinAlgebraNorm : Prop :=
  ∃ n : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E n ∧
    ∀ m, IsWeakCalkinAlgebraNorm 𝕜 E m →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * n x ≤ m x ∧ m x ≤ C * n x

/-- Bonsall minimality means exact equality for every dominated algebra norm. -/
def HasBonsallWeakCalkinMinimality (p : (E →L[𝕜] E) → ℝ) : Prop :=
  ∃ n : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E n ∧
    (∀ T, n (weakCalkinMk 𝕜 E T) = p T) ∧
    ∀ m, IsWeakCalkinAlgebraNorm 𝕜 E m → (∀ x, m x ≤ n x) → m = n

end ThesisCommon
