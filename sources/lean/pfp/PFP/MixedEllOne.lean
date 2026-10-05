import PFP.IteratedStatements
import ThesisCommon.Analysis.MixedEllOneFactorization

/-! Mixed X(ell_1) results in Section 3.2. The entries below evaluate the
actual product vectors and their scalar coordinates in the genuine sum.
All three clauses of 3.12 and the exact supremum in 3.13 are retained.
-/
noncomputable section
open scoped BigOperators
namespace PFP
open ThesisCommon SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Lemma 3.12, `lmm: ell1-iterated-interference`, including (a), (b), (c).
A finite set K indexes the source rows, and M i is their infinite reservoir. -/
def Lemma_3_12 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
  ∀ T : SchauderSum b hb (ScalarEllOne 𝕜) →L[𝕜] SchauderSum b hb (ScalarEllOne 𝕜),
    (∀ i j ε, 0 < ε → {r | ∃ s, ε ≤ ‖ellOneEntry T i j r s‖}.Finite) ∧
    (∀ i j ε, 0 < ε →
      {t : ℕ × ℕ | ε ≤ ‖ellOneEntry T t.1 t.2 i j‖}.Finite) ∧
    (∀ (r : ℕ) (A : Set ℕ), A.Infinite → ∀ ε : ℝ, 0 < ε →
      ∀ (K : Finset ℕ) (M : ℕ → Set ℕ), (∀ i ∈ K, (M i).Infinite) →
      ∃ s ∈ A, ∀ i ∈ K, {m ∈ M i | ‖ellOneEntry T r s i m‖ ≤ ε}.Infinite)

theorem lemma_3_12 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) :
    Lemma_3_12 b hb := by
  intro hs hnot T
  refine ⟨fun i j ε hε => ellOne_finite_interfering_rows hs hnot T i j hε,
    fun i j ε hε => ellOne_finite_interfering_targets T i j hε, ?_⟩
  intro r A hA ε hε K M hM
  obtain ⟨s, hsA, hs⟩ := (ellOne_simultaneous_small_rows T r (fun _ => ε)
    (fun _ => hε) K M hA hM).nonempty
  refine ⟨s, hsA, ?_⟩
  intro i hi
  exact Set.Infinite.mono (fun _ hm => ⟨hm.1, hm.2.le⟩) (hs i hi)

/-- Lemma 3.13, `lmm: ell1-small-operator`. Positive source indices r,i
become r+1,i+1, so the denominator is 2^(r+i+2). The supremum is of actual
summable columns; its boundedness is proved separately, not assumed. -/
def Lemma_3_13 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) : Prop :=
  ∀ (T : SchauderSum b hb (ScalarEllOne 𝕜) →L[𝕜]
      SchauderSum b hb (ScalarEllOne 𝕜)) (ε : ℝ),
    (∀ r i, (⨆ j : ℕ, ∑' s, ‖ellOneEntry T r s i j‖) ≤
      ε / (2 : ℝ) ^ (r + i + 2)) → ‖T‖ ≤ ε

/-- The proof needs only one-unconditionality of the outer norm, so it
also proves the source statement under its stronger standing hypotheses. -/
theorem lemma_3_13 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) :
    Lemma_3_13 b hb := by
  intro T ε hT
  exact norm_le_of_ellOne_column_sums T hT

/-- Lemma 3.14, `lmm: ell1-iterated-true-diagonal`.
Strictly increasing m i enumerates an infinite set M_i. The asymmetric
budget depends on the target inner index s, not the source inner index j.
All three positive indices are shifted, giving exponent r+i+s+3. -/
def Lemma_3_14 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
  ∀ (T : SchauderSum b hb (ScalarEllOne 𝕜) →L[𝕜]
      SchauderSum b hb (ScalarEllOne 𝕜)) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ), StrictMono n ∧ (∀ i, StrictMono (m i)) ∧
      ∀ r s i j, (r, s) ≠ (i, j) →
        ‖ellOneEntry T (n r) (m r s) (n i) (m i j)‖ ≤
          ε / (2 : ℝ) ^ (r + i + s + 3)

theorem lemma_3_14 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) :
    Lemma_3_14 b hb := by
  intro hs hnot T ε hε
  exact ellOne_asymmetric_selection hs hnot T hε

/-- The full original mixed X(ell_1) theorem, with every analytic and
asymmetric-selection input discharged on the actual space. -/
theorem theorem_3_15 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) :
    Theorem_3_15 b hb := by
  intro hs hnot
  exact SchauderSum.ellOne_hasCPlusPFP_two hs hnot

end PFP
