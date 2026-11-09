import JLMS.PrintedAtomicNotation
import JLMS.HalfAtomicPieces

/-!
# The printed statements of Proposition 5.2, Lemma 5.4 and Corollary 5.5

These wrappers retain the standing hypotheses at the start of Section 5,
including ‖T‖ₑ = 1 and the fixed δ, θ. The latter parameters are unused in
Lemma 5.4 and Corollary 5.5, exactly as in their printed conclusions.
Rudin's representation is proved and supplied internally. Sequence indices
use Lean's ℕ; this is the usual relabelling of the paper's positive indices.
-/

noncomputable section
namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Proposition 5.2 with its printed threshold δ + 2θ and the Section 5 context. -/
theorem printed_proposition_5_2 [CompleteSpace X]
    (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X) (hT : essentialNorm T = 1)
    (δ θ : ℝ) (hδ : 0 < δ) (_hδhalf : δ < 1 / 2) (hθ : 0 < θ)
    (hmargin : 2 * (δ + 2 * θ) < 1) :
    ∃ xstar : ℕ → (X →L[𝕜] 𝕜), ∃ F : ℕ → Finset K,
      (∀ j, ‖xstar j‖ ≤ 1) ∧
      (∀ j, (F j : Set K) ⊆ printedAtomicSupport (𝕜 := 𝕜) hK (banachAdjoint T (xstar j))) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      ∀ j, δ + 2 * θ <
        ‖printedAtomicRestriction (𝕜 := 𝕜) hK (F j : Set K) (banachAdjoint T (xstar j))‖ := by
  apply exists_disjoint_large_dual_atoms_of_primal (printedAtomicDualModel (𝕜 := 𝕜) hK) hK T
  · linarith
  · simpa only [hT] using hmargin

/-- Lemma 5.4: one neighborhood collection has arbitrarily late weights below ε. -/
theorem printed_lemma_5_4 [CompleteSpace X]
    (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X) (_hT : essentialNorm T = 1)
    (δ θ : ℝ) (_hδ : 0 < δ) (_hδhalf : δ < 1 / 2) (_hθ : 0 < θ)
    (_hmargin : 2 * (δ + 2 * θ) < 1)
    (xstar : ℕ → (X →L[𝕜] 𝕜)) (hxstar : ∀ j, ‖xstar j‖ ≤ 1)
    (F : ℕ → Finset K) (hF : Pairwise fun i j => Disjoint (F i) (F j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∀ J : ℕ, ∃ j : ℕ, J < j ∧
        ‖printedAtomicRestriction (𝕜 := 𝕜) hK (⋃ k, U.sets k) (banachAdjoint T (xstar j))‖ < ε := by
  let M := printedAtomicDualModel (𝕜 := 𝕜) hK
  have hbound (j : ℕ) : ‖atomicAdjoint M T (xstar j)‖ ≤ ‖T‖ := by
    rw [atomicAdjoint_apply, M.representation.norm_map]
    exact ((banachAdjoint T).le_opNorm (xstar j)).trans (by
      simpa only [norm_banachAdjoint, mul_one] using
        mul_le_mul_of_nonneg_left (hxstar j) (norm_nonneg (banachAdjoint T)))
  obtain ⟨n, U, hU⟩ := exists_neighborhood_arbitrarily_late_small_weight hK
    (fun j => atomicAdjoint M T (xstar j)) F hF ‖T‖ hbound hε
  refine ⟨n, U, ?_⟩
  intro J
  obtain ⟨j, hJj, hsmall⟩ := hU J
  refine ⟨j, hJj, ?_⟩
  simpa only [printedAtomicRestriction, atomicRestriction_norm, atomicAdjoint_apply] using hsmall

/-- Corollary 5.5, with an actual strictly increasing subsequence of the given functionals. -/
theorem printed_corollary_5_5 [CompleteSpace X]
    (hK : IsScattered K) (T : CZero 𝕜 K →L[𝕜] X) (_hT : essentialNorm T = 1)
    (δ θ : ℝ) (_hδ : 0 < δ) (_hδhalf : δ < 1 / 2) (_hθ : 0 < θ)
    (_hmargin : 2 * (δ + 2 * θ) < 1)
    (xstar : ℕ → (X →L[𝕜] 𝕜)) (hxstar : ∀ j, ‖xstar j‖ ≤ 1)
    (F : ℕ → Finset K) (hF : Pairwise fun i j => Disjoint (F i) (F j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ U : NeighborhoodFamily (fun k : ↥(F n) => (k : K)),
      ∃ s : ℕ → ℕ, StrictMono s ∧
        ∀ j, ‖printedAtomicRestriction (𝕜 := 𝕜) hK (⋃ k, U.sets k)
          (banachAdjoint T (xstar (s j)))‖ < ε :=
  exists_neighborhood_subsequence_small_dual_weight (printedAtomicDualModel (𝕜 := 𝕜) hK) T
    hK xstar hxstar F hF hε

end JLMS
