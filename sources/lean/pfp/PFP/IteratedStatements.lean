import PFP.MainStatements
import ThesisCommon.Analysis.IteratedSchauderSum
import ThesisCommon.Analysis.SupportingTree
import ThesisCommon.Analysis.NatTreeEmbedding
import ThesisCommon.Analysis.SchauderSumOperators
import ThesisCommon.Analysis.SupportingSubtree
import ThesisCommon.Analysis.IteratedSchauderWeaklyNull

/-! Genuine iterated-sum and mixed-sum targets from Section 3. The spaces
are actual vector-valued sequences with the manuscript's norm; their Banach
structure and the series-definition correspondence are proved in the library.
-/
noncomputable section
universe u v
namespace PFP
open ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

/-- Definition 3.5, at the root: infinitely many first-level nodes support T.
Support is defined by the backward induction on genuine finite terminal tuples. -/
def SupportedOperator (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) : Prop :=
  InfinitelySupported (tail.length + 1) (fun t => (1 / 2 : ℝ) ≤
    ‖iteratedBasisCoordinate first tail t (T (iteratedBasisVector first tail t))‖)

/-- Lemma 3.6, `lmm: infinitely-support`, on the actual iterated sum. -/
def Lemma_3_6 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Prop :=
  ∀ T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier,
    SupportedOperator first tail T ∨
      SupportedOperator first tail (ContinuousLinearMap.id 𝕜 _ - T)

theorem lemma_3_6 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Lemma_3_6 first tail := by
  intro T
  apply infinitelySupported_or
  intro t
  let z := iteratedBasisCoordinate first tail t (T (iteratedBasisVector first tail t))
  have heq : iteratedBasisCoordinate first tail t
      ((ContinuousLinearMap.id 𝕜 (iteratedSchauderSum first tail).Carrier - T)
        (iteratedBasisVector first tail t)) = 1 - z := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
      iteratedBasisCoordinate_vector_self]
    rfl
  rw [heq]
  change (1 / 2 : ℝ) ≤ ‖z‖ ∨ (1 / 2 : ℝ) ≤ ‖1 - z‖
  have hn := norm_add_le z (1 - z)
  rw [add_sub_cancel, norm_one] at hn
  by_cases hz : (1 / 2 : ℝ) ≤ ‖z‖
  · exact Or.inl hz
  · right; linarith

/-- First step of Lemma 3.7: construct a full subtree with the diagonal
bound. Off-diagonal estimates and its isometric identification remain separate. -/
theorem supporting_tree (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) (h : SupportedOperator first tail T) :
    ∃ f : NatTreeEmbedding (tail.length + 1), ∀ t,
      (1 / 2 : ℝ) ≤ ‖iteratedBasisCoordinate first tail (f.map t)
        (T (iteratedBasisVector first tail (f.map t)))‖ :=
  InfinitelySupported.exists_tree h

/-- The actual norm-closed span of the terminal vectors selected by a tree embedding. -/
def SelectedTreeSpan (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) (f : NatTreeEmbedding (tail.length + 1)) :
    Submodule 𝕜 (iteratedSchauderSum first tail).Carrier :=
  (Submodule.span 𝕜 (Set.range (fun t => iteratedBasisVector first tail (f.map t)))).topologicalClosure

/-- Lemma 3.7, `lem:CKL-tree-selection`. The full selected subtree, actual
closed span, isometric equivalence, diagonal bound, and enumeration estimate
are retained. Positive paper indices j,k become j+1,k+1, giving exponent j+k+3. -/
def Lemma_3_7 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Prop :=
  (∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne) →
  ∀ (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) (η : ℝ), 0 < η →
    SupportedOperator first tail T →
    ∃ f : NatTreeEmbedding (tail.length + 1),
      Nonempty ((iteratedSchauderSum first tail).Carrier ≃ₗᵢ[𝕜] SelectedTreeSpan first tail f) ∧
      (∀ t, (1 / 2 : ℝ) ≤ ‖iteratedBasisCoordinate first tail (f.map t)
        (T (iteratedBasisVector first tail (f.map t)))‖) ∧
      ∃ e : ℕ ≃ (Fin (tail.length + 1) → ℕ), ∀ j k, j ≠ k →
        ‖iteratedBasisCoordinate first tail (f.map (e j))
          (T (iteratedBasisVector first tail (f.map (e k))))‖ < η / (2 : ℝ) ^ (j + k + 3)

/-- Theorem 3.8, `th: Cassaza-Kottman-Lin`, for every nonempty finite list
of the original factor spaces. The last factor is used directly, as printed. -/
def Theorem_3_8 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Prop :=
  (∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne) →
    HasCPlusPFP 𝕜 (iteratedSchauderSum first tail).Carrier 2

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Theorem 3.15, `th: l_1-iterated`: the actual X(ℓ₁) has 2⁺-PFP. -/
def Theorem_3_15 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
    HasCPlusPFP 𝕜 (SchauderSum b hb (ScalarEllOne 𝕜)) 2

/-- Theorem 3.26, `th: l_inf-iterated`: the actual X(ℓ∞) has 2⁺-PFP.
The inner space is the bounded scalar product, without a Schauder-basis assumption. -/
def Theorem_3_26 (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional) : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
    HasCPlusPFP 𝕜 (SchauderSum b hb (ScalarEllInfinity 𝕜)) 2

end PFP
