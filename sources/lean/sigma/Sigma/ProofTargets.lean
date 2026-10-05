import Sigma.MainStatements
import Sigma.FunctionSpaces
import ThesisCommon.Analysis.NormingSequence
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Concrete targets for the supporting results. Their checked proofs are in
the corresponding proof modules; none is assumed as an axiom. -/
noncomputable section
universe u
namespace SigmaNonprimarity
open ThesisCommon
open scoped BoundedContinuousFunction

/-- A closed vector sublattice of real ℓ∞, with its inherited norm. -/
def IsomorphicToSublatticeEllInfinity (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop :=
  ∃ S : Submodule ℝ (ℕ →ᵇ ℝ), IsClosed (S : Set (ℕ →ᵇ ℝ)) ∧
    (∀ f ∈ S, ∀ g ∈ S, f ⊔ g ∈ S ∧ f ⊓ g ∈ S) ∧ Nonempty (E ≃L[ℝ] S)

/-- Proposition 3.4, cited from de Hevia et al., Corollary 4.3.
The norming convention is the corrected one; see SourceChecks and the discrepancy record. -/
def Proposition_3_4 (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : Prop :=
  (∃ e : ℕ → E →L[ℝ] ℝ, IsNorming e) →
  (∃ Γ : Type u, Nonempty ((E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : Γ => ℝ) 1)) →
  (IsomorphicToBanachLattice E ↔ IsomorphicToSublatticeEllInfinity E) ∧
  (IsomorphicToSublatticeEllInfinity E ↔ ¬ DesiredProperty E)

/-- Definition 4.6; a positive lower bound is equivalent to the positive infimum here. -/
def Admissible (μ : ℕ → lp (fun _ : Point => ℝ) 1) : Prop :=
  (∀ n, ‖μ n‖ ≤ 1) ∧
  (∀ n k, μ n (k, false) = -μ n (k, true)) ∧
  (∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ |μ n (n, false)|)

/-- Verification of the infimum/positive-uniform-bound representation in Definition 4.6. -/
theorem positive_diagonal_iff (μ : ℕ → lp (fun _ : Point => ℝ) 1) :
    (∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ |μ n (n, false)|) ↔
      0 < ⨅ n, |μ n (n, false)| := by
  have hb : BddBelow (Set.range fun n => |μ n (n, false)|) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact abs_nonneg _⟩
  constructor
  · rintro ⟨b, hb0, h⟩
    exact hb0.trans_le (le_ciInf h)
  · intro h
    exact ⟨_, h, fun n => ciInf_le hb n⟩

/-- Evaluation of the countably additive ℓ1 part on any subset of the countable base. -/
def mass (μ : lp (fun _ : Point => ℝ) 1) (s : Set Point) : ℝ :=
  ∑' p : s, μ p

/-- Lemma 4.7: all nesting, infinitude, splitting and quantitative clauses.
The second-copy version is the same statement after relabelling the base. -/
def Lemma_4_7 : Prop :=
  ∀ (C : Set ℕ) (μ : ℕ → lp (fun _ : Point => ℝ) 1), C.Infinite → Admissible μ →
    ∃ (J₀ J₁ J₂ : Set ℕ) (Z : Set Point) (a δ : ℝ),
      J₂ ⊆ J₁ ∧ J₁ ⊆ J₀ ∧ J₀ ⊆ C ∧ J₂.Infinite ∧
      (J₁ \ J₂).Infinite ∧ (J₀ \ J₁).Infinite ∧ Splits J₁ Z ∧
      a ≥ (⨅ n, |μ n (n, false)|) ∧ 0 < δ ∧
      δ < (⨅ n, |μ n (n, false)|) / 11 ∧
      (∀ n ∈ J₂, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) - 2*a| < 3*δ) ∧
      (∀ n ∈ J₁ \ J₂, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) + 2*a| < 3*δ) ∧
      (∀ n ∈ J₀ \ J₁, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z)| < 3*δ)

end SigmaNonprimarity
