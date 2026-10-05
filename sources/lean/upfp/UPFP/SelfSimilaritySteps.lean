import UPFP.MainStatements
import ThesisCommon.Analysis.SelfSimilarSmallBlocks
import ThesisCommon.Analysis.SelfSimilarBackwardSelection
import ThesisCommon.Analysis.SelfSimilarUpperTriangular

/-! Self-similarity estimates from the supplied UPFP manuscript.
Infinite inner coordinate sets are represented by injective enumerations.
The common proofs use the source's disjoint-block signed averaging and Jensen
argument, in its equivalent vector-norm form. These are supporting lemmas,
not yet the full self-similarity branches of the main theorems.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Lemma 3.7, infinity case. The inner set may be constant on the selected
infinite outer set; allowing it to depend on the outer index follows at once. -/
theorem lemma_3_7_infinity (p : BanachExponent) (hp : p.val ≠ ∞) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] EllInfinitySum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) ^ (1 / p.val.toReal) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), {m : ℕ | ‖((lpRestrict p.val a).comp
      ((lpCoordinate ∞ m).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite :=
  infinity_lp_forward_reduction p.val hp T hε hlarge

/-- Lemma 3.7, c₀ case, on the actual null-sequence target. -/
theorem lemma_3_7_cZero (p : BanachExponent) (hp : p.val ≠ ∞) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] CZeroSum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) ^ (1 / p.val.toReal) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), {m : ℕ | ‖((lpRestrict p.val a).comp
      ((cZeroCoordinate m).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite :=
  cZero_lp_forward_reduction p.val hp T hε hlarge

/-- Lemma 4.8, infinity case. Both retained coordinate sets are infinite. -/
theorem lemma_4_8_infinity (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : EllInfinitySum Y →L[𝕜] SequenceSum p X) {ε : ℝ} (hε : 0 < ε) :
    ∃ a e : ℕ ↪ ℕ, (Set.range a).Infinite ∧ (Set.range e).Infinite ∧
      ‖((lpRestrict p.val a).comp T).comp (lpExtend ∞ e)‖ < ε := by
  obtain ⟨a, e, h⟩ := infinity_to_lp_backward_reduction p.val hp T hε
  exact ⟨a, e, Set.infinite_range_of_injective a.injective,
    Set.infinite_range_of_injective e.injective, h⟩

/-- Lemma 4.8, c₀ case, preserving the actual null-sequence membership. -/
theorem lemma_4_8_cZero (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : CZeroSum Y →L[𝕜] SequenceSum p X) {ε : ℝ} (hε : 0 < ε) :
    ∃ a e : ℕ ↪ ℕ, (Set.range a).Infinite ∧ (Set.range e).Infinite ∧
      ‖((lpRestrict p.val a).comp T).comp (cZeroExtend e)‖ < ε := by
  obtain ⟨a, e, h⟩ := cZero_to_lp_backward_reduction p.val hp T hε
  exact ⟨a, e, Set.infinite_range_of_injective a.injective,
    Set.infinite_range_of_injective e.injective, h⟩

/-- Proposition 3.8, infinity case; inner sets are injectively enumerated. -/
theorem proposition_3_8_infinity (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : EllInfinitySum (SequenceSum p X) →L[𝕜] EllInfinitySum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpRestrict p.val (a j)).comp ((lpCoordinate ∞ (e j)).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => SequenceSum p X) ∞ (e i))‖) < ε :=
  infinity_lp_upper_triangular p.val hp T hε

/-- Proposition 3.8, c₀ case. -/
theorem proposition_3_8_cZero (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : CZeroSum (SequenceSum p X) →L[𝕜] CZeroSum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpRestrict p.val (a j)).comp ((cZeroCoordinate (e j)).comp T)).comp
        (cZeroSingleCLM (e i))‖) < ε :=
  cZero_lp_upper_triangular p.val hp T hε

/-- Proposition 4.9, infinity case, controlling the entire future tail. -/
theorem proposition_4_9_infinity (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : EllInfinitySum (SequenceSum p X) →L[𝕜] EllInfinitySum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict p.val (a k)).comp ((lpCoordinate ∞ (e k)).comp T)).comp
        (lpExtend ∞ (coordinateTail e k))‖ < ε :=
  infinity_lp_backward_selection p.val hp T (fun _ => ε) (fun _ => hε)

/-- Proposition 4.9, c₀ case. -/
theorem proposition_4_9_cZero (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : CZeroSum (SequenceSum p X) →L[𝕜] CZeroSum (SequenceSum p X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a : ℕ → (ℕ ↪ ℕ)), StrictMono e ∧ ∀ k,
      ‖((lpRestrict p.val (a k)).comp ((cZeroCoordinate (e k)).comp T)).comp
        (cZeroExtend (coordinateTail e k))‖ < ε :=
  cZero_lp_backward_selection p.val hp T (fun _ => ε) (fun _ => hε)

end UPFP
