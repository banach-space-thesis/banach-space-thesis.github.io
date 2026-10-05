import UPFP.MainStatements
import ThesisCommon.Analysis.CotypeForward
import ThesisCommon.Analysis.CotypeBackward
import ThesisCommon.Analysis.CotypeLowerTriangular
import ThesisCommon.Analysis.CotypeUpperTriangular
import ThesisCommon.Analysis.CotypePreservation
import ThesisCommon.Analysis.SequencePrimariness

/-! Complete cotype selection lemmas from Sections 3 and 4.
Includes the full finite-cotype branch of Theorem 1.2. The full main proof
combines it with self-similarity in UPFP.PreservationTheorem.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace UPFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Lemma 3.4, ℓ∞ case. The finite sum is realized as lp over Fin n. -/
theorem lemma_3_4_infinity {q C : ℝ} (h : HasRademacherCotype X q C) {n : ℕ}
    (T : lp (fun _ : Fin n => X) ∞ →L[𝕜] EllInfinitySum X) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * C * ‖T‖ < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i : Fin n, {m : ℕ | ‖((lpCoordinate ∞ m).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => X) ∞ i)‖ < ε}.Infinite :=
  h.infinity_forward_reduction T hε hlarge

/-- Lemma 3.4, c₀ case, with exactly the same quantitative threshold. -/
theorem lemma_3_4_cZero {q C : ℝ} (h : HasRademacherCotype X q C) {n : ℕ}
    (T : lp (fun _ : Fin n => X) ∞ →L[𝕜] CZeroSum X) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 2 * C * ‖T‖ < (n : ℝ) ^ (1 / q) * ε) :
    ∃ i : Fin n, {m : ℕ | ‖((cZeroCoordinate m).comp T).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => X) ∞ i)‖ < ε}.Infinite :=
  h.cZero_forward_reduction T hε hlarge

/-- Lemma 4.6, ℓ∞ case, including an explicit infinite subset of coordinates.
Its injective enumeration realizes the paper's J_M on the full ℓ∞ space. -/
theorem lemma_4_6_infinity (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : Set ℕ) (e : ℕ ↪ ℕ), M.Infinite ∧ Set.range e = M ∧
      ‖T.comp (lpExtend ∞ e)‖ < ε := by
  obtain ⟨e, he⟩ := h.infinity_backward_reduction T hε
  exact ⟨Set.range e, e, Set.infinite_range_of_injective e.injective, rfl, he⟩

/-- Lemma 4.6, c₀ case, with actual null sequences and zero extension. -/
theorem lemma_4_6_cZero (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : Set ℕ) (e : ℕ ↪ ℕ), M.Infinite ∧ Set.range e = M ∧
      ‖T.comp (cZeroExtend e)‖ < ε := by
  obtain ⟨e, he⟩ := h.cZero_backward_reduction T hε
  exact ⟨Set.range e, e, Set.infinite_range_of_injective e.injective, rfl, he⟩

/-- Proposition 3.5, ℓ∞ case. Increasing enumeration identifies the sum over
the preceding points of M with the finite range 0,...,j-1. -/
theorem proposition_3_5_infinity (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((lpCoordinate ∞ (e j)).comp T).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ (e i))‖) < ε :=
  h.infinity_upper_triangular T hε

/-- Proposition 3.5, c₀ case, using bounded single-coordinate insertions. -/
theorem proposition_3_5_cZero (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ j,
      (∑ i ∈ Finset.range j, ‖((cZeroCoordinate (e j)).comp T).comp
        (cZeroSingleCLM (e i))‖) < ε := h.cZero_upper_triangular T hε

/-- Proposition 4.7, ℓ∞ case. The range of the increasing injection is the
paper's infinite M. IsLpLowerPart specifies the actual finite-prefix action;
its matrix_formula theorem proves the displayed finite lower matrix sum. -/
theorem proposition_4_7_infinity (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : EllInfinitySum X →L[𝕜] EllInfinitySum X), StrictMono e ∧
      ‖((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e) - L‖ < ε ∧
      IsLpLowerPart (((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e)) L :=
  h.infinity_lower_triangular T hε

/-- Proposition 4.7, c₀ case. Vanishing row norms ensure that the subtracted
tail operator maps into actual null sequences, as the paper requires. -/
theorem proposition_4_7_cZero (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : CZeroSum X →L[𝕜] CZeroSum X), StrictMono e ∧
      ‖((cZeroRestrict e).comp T).comp (cZeroExtend e) - L‖ < ε ∧
      IsCZeroLowerPart (((cZeroRestrict e).comp T).comp (cZeroExtend e)) L :=
  h.cZero_lower_triangular T hε

/-- Proposition 5.3, ℓ∞ case, with the actual diagonal part of the final
compression. The increasing enumeration represents the paper's infinite M. -/
theorem proposition_5_3_infinity (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ‖((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e) -
        lpDiagonalPart (((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e))‖ < ε :=
  h.infinity_diagonal_reduction T hε

/-- Proposition 5.3, c₀ case, with actual null sequences throughout. -/
theorem proposition_5_3_cZero (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧
      ‖((cZeroRestrict e).comp T).comp (cZeroExtend e) -
        cZeroDiagonalPart (((cZeroRestrict e).comp T).comp (cZeroExtend e))‖ < ε :=
  h.cZero_diagonal_reduction T hε

/-- Both UPFP conclusions of Theorem 1.2 under its finite-cotype hypothesis.
This is a proved branch, not the entire Theorem 1.2: neither primariness nor
the alternative self-similarity hypothesis is asserted by this declaration. -/
theorem theorem_1_2_finiteCotype_upfp [CompleteSpace X]
    (hX : HasUPFP 𝕜 X) (hcotype : HasFiniteCotype X) :
    HasUPFP 𝕜 (CZeroSum X) ∧ HasUPFP 𝕜 (EllInfinitySum X) :=
  ⟨hX.cZero_of_finiteCotype hcotype, hX.infinity_of_finiteCotype hcotype⟩

/-- All four conclusions of Theorem 1.2 under its finite-cotype alternative.
The separate finite-p self-similarity alternative is not an assumption or
conclusion of this branch. It is proved in UPFP.PreservationTheorem. -/
theorem theorem_1_2_finiteCotype [CompleteSpace X]
    (hX : HasUPFP 𝕜 X) (hcotype : HasFiniteCotype X) :
    (HasUPFP 𝕜 (CZeroSum X) ∧ HasUPFP 𝕜 (EllInfinitySum X)) ∧
      (IsPrimary 𝕜 (CZeroSum X) ∧ IsPrimary 𝕜 (EllInfinitySum X)) := by
  obtain ⟨hzero, hinfty⟩ := theorem_1_2_finiteCotype_upfp hX hcotype
  exact ⟨⟨hzero, hinfty⟩, hzero.cZero_isPrimary, hinfty.infinity_isPrimary⟩

end UPFP

