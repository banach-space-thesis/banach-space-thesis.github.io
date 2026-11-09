import JLMS.PrintedAtomicNotation
import JLMS.AtomicApplications
import JLMS.MainFactorizations

/-!
# The printed statements of Proposition 7.1 and Corollary 7.3

The atomic restriction and support are supplied by the proved Rudin
representation. Proposition 7.1 retains the normalization inherited from
the opening of Section 5. Its statement places no positivity assumption
on θ; a nonnegative auxiliary threshold handles that case as well.
Corollary 7.3 explicitly quantifies over arbitrary noncompact operators
and both of the printed alternatives on the codomain.
-/

noncomputable section
namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

local instance printedSevenDualGroup : NormedAddCommGroup (X →L[𝕜] 𝕜) := inferInstance
local instance printedSevenDualSpace : NormedSpace 𝕜 (X →L[𝕜] 𝕜) := inferInstance
local instance printedSevenCZeroDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) :=
  inferInstance
local instance printedSevenCZeroDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) :=
  inferInstance

/-- Proposition 7.1, with conditions (a) and (b) of Proposition 5.2 expanded.
Sequences indexed by ℕ enumerate the printed sequence beginning at 1. -/
theorem printed_proposition_7_1 (hK : IsScattered K)
    (T : CZero 𝕜 K →L[𝕜] X) (_hT : essentialNorm T = 1)
    (δ θ : ℝ) (hδ : 0 < δ) (hδT : δ < dualEssentialNorm T)
    (hθ : δ + 2 * θ < dualEssentialNorm T) :
    ∃ xStar : ℕ → (X →L[𝕜] 𝕜), ∃ F : ℕ → Finset K,
      (∀ j, ‖xStar j‖ ≤ 1) ∧
      (∀ j, (F j : Set K) ⊆ printedAtomicSupport (𝕜 := 𝕜) hK (banachAdjoint T (xStar j))) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      ∀ j, δ + 2 * θ <
        ‖printedAtomicRestriction (𝕜 := 𝕜) hK (F j : Set K) (banachAdjoint T (xStar j))‖ := by
  have hpositive : 0 < dualEssentialNorm T := hδ.trans hδT
  obtain ⟨xStar, F, hunit, hsupp, hdisj, hmass⟩ :=
    exists_disjoint_large_dual_atoms (printedAtomicDualModel (𝕜 := 𝕜) hK) T
      (le_max_right (δ + 2 * θ) 0) (max_lt hθ hpositive)
  exact ⟨xStar, F, hunit, hsupp, hdisj,
    fun j => (le_max_left (δ + 2 * θ) 0).trans_lt (hmass j)⟩

/-- Corollary 7.3: the strict additive-ε factorization estimate, for the
full disjunction of codomain hypotheses printed in the paper. -/
theorem printed_corollary_7_3 (hK : IsScattered K)
    (hX : ¬ ContainsEllOne 𝕜 X ∨ DualBallWeakStarSeqCompact 𝕜 X)
    (T : CZero 𝕜 K →L[𝕜] X) (hT : ¬ IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 1 / dualEssentialNorm T + ε := by
  obtain ⟨U₀, V₀, hfactor, _⟩ := theorem_1_6 hK hX T hT 1 zero_lt_one
  have hd : 0 < dualEssentialNorm T :=
    dualEssentialNorm_pos_of_cZero_factorization T U₀ V₀ hfactor
  have hsharp := sharpFactorizations_of_disjointFunctions
    disjointFunctionsSharp factorizationFromDisjointFunctions hK hX T
  let δ : ℝ := 1 / (1 / dualEssentialNorm T + ε)
  have hden : 0 < 1 / dualEssentialNorm T + ε := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδT : δ < dualEssentialNorm T := by
    apply (div_lt_iff₀ hden).mpr
    have hcancel := one_div_mul_cancel (ne_of_gt hd)
    nlinarith
  obtain ⟨U, V, hUV, hnorm⟩ := hsharp δ hδ hδT
  exact ⟨U, V, hUV, by simpa [δ] using hnorm⟩

end JLMS
