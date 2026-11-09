import JLMS.PrintedSectionFive
import JLMS.DisjointConstruction

/-!
# The printed statement of Lemma 6.1

Proposition 5.2 supplies the initial finite pieces, and the existing diagonal
recursion supplies the neighborhoods. No initial-piece, representation or
diagonal-selection hypothesis is added. The disjointness conclusion is stated
for the union of the actual neighborhood collections, as printed in (a).
-/

noncomputable section
namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma 6.1, with the original standing hypotheses and both printed conclusions. -/
theorem printed_lemma_6_1 [CompleteSpace X]
    (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X) (hT : essentialNorm T = 1)
    (δ θ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hθ : 0 < θ)
    (hmargin : 2 * (δ + 2 * θ) < 1) :
    ∃ ystar : ℕ → (X →L[𝕜] 𝕜), ∃ A : ℕ → Finset K,
      ∃ V : ∀ j, NeighborhoodFamily (fun k : ↥(A j) => (k : K)),
        (∀ j, ‖ystar j‖ ≤ 1) ∧
        (∀ j, (A j : Set K) ⊆ printedAtomicSupport (𝕜 := 𝕜) hK (banachAdjoint T (ystar j))) ∧
        (⋃ j, Set.range (V j).sets).Pairwise Disjoint ∧
        ∀ j, δ + θ <
          ‖printedAtomicRestriction (𝕜 := 𝕜) hK (A j : Set K) (banachAdjoint T (ystar j))‖ := by
  obtain ⟨xstar, F, hxstar, hsupport, hF, hlarge⟩ :=
    printed_proposition_5_2 hK T hT δ θ hδ hδhalf hθ hmargin
  have hlarge' (j : ℕ) : (δ + θ) + θ <
      ‖printedAtomicRestriction (𝕜 := 𝕜) hK (F j : Set K) (banachAdjoint T (xstar j))‖ := by
    have h := hlarge j
    linarith
  obtain ⟨ystar, A, V, hystar, hsupp, hdisj, hmass⟩ :=
    separatedAtomicWitnesses_of_large_pieces (printedAtomicDualModel (𝕜 := 𝕜) hK) hK T
      (δ + θ) θ hθ xstar F hxstar hsupport hF hlarge'
  refine ⟨ystar, A, V, hystar, hsupp, ?_, hmass⟩
  intro U hU W hW hUW
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hU
  obtain ⟨k, rfl⟩ := hi
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hW
  obtain ⟨l, rfl⟩ := hj
  by_cases hij : i = j
  · subst j
    exact (V i).disjoint (fun hkl => hUW (congrArg (V i).sets hkl))
  · exact (hdisj hij).mono (Set.subset_iUnion (fun k => (V i).sets k) k)
      (Set.subset_iUnion (fun l => (V j).sets l) l)

end JLMS
