import PFP.IteratedStatements
import ThesisCommon.Analysis.IteratedTreeSelection
import ThesisCommon.Analysis.IteratedFactorization

noncomputable section
universe u v
namespace PFP
open ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

/-- Full CKL tree selection: original Lemma 3.7 on the actual spaces. -/
theorem lemma_3_7 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Lemma_3_7 first tail := by
  intro h T η hη hs
  obtain ⟨f, hd, he⟩ := iterated_tree_selection first tail h T hη hs
  exact ⟨f, iterated_tree_span_isometric first tail (fun F hF => (h F hF).1) f,
    hd, natTupleEnumeration tail.length, he⟩

/-- Full Theorem 3.8 with all tree-selection and analytic inputs discharged. -/
theorem theorem_3_8 (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : Theorem_3_8 first tail := by
  intro h ε hε T
  rcases lemma_3_6 first tail T with hs | hs
  · exact Or.inl (iterated_supported_factorization first tail h T hs hε)
  · exact Or.inr (iterated_supported_factorization first tail h _ hs hε)

end PFP
