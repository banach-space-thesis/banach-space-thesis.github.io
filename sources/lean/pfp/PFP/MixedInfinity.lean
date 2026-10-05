import PFP.IteratedStatements
import ThesisCommon.Analysis.MixedInfinityFactorization

/-! The mixed X(ell_infinity) section on the actual vector-valued sum.
No Schauder basis or global matrix representation of the inner space is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace PFP
open ThesisCommon SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable (b : NormalizedSchauderBasis 𝕜 X) (hb : b.IsOneUnconditional)

/-- Lemma 3.22, `lmm: preliminary-l-infinity-iterated`, all three clauses. -/
def Lemma_3_22 : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
  ∀ T : SchauderSum b hb (ScalarEllInfinity 𝕜) →L[𝕜] SchauderSum b hb (ScalarEllInfinity 𝕜),
    (∀ i j (ε : ℝ), 0 < ε → {p : ℕ × ℕ | ε < ‖infinityEntry T i j p.1 p.2‖}.Finite) ∧
    (∀ r (M : Set ℕ), M.Infinite → ∀ ε : ℝ, 0 < ε → ∀ K : Finset ℕ,
      ∀ L : ℕ → Set ℕ, (∀ i ∈ K, (L i).Infinite) → ∀ N : ℕ,
      ∃ s ∈ M, N < s ∧ ∀ i ∈ K, (L i \ {j | ε < ‖infinityEntry T i j r s‖}).Infinite) ∧
    (∀ r s, Tendsto (fun i => ⨆ j : ℕ, ‖infinityEntry T i j r s‖) atTop (𝓝 0))

theorem lemma_3_22 : Lemma_3_22 b hb := by
  intro hs hnot T
  refine ⟨?_, ?_, infinity_target_row_tendsto_zero T⟩
  · intro i j ε hε
    apply (infinity_finite_interfering_sources hs hnot T i j hε).subset
    intro p hp
    change ε ≤ ‖infinityEntry T i j p.1 p.2‖
    exact le_of_lt hp
  · intro r M hM ε hε K L hL N
    have h := infinity_simultaneous_small_rows T r (fun _ => ε) (fun _ => hε) K L
      (infinite_above hM N) hL
    obtain ⟨s, ⟨hs, hN⟩, hgood⟩ := h.nonempty
    refine ⟨s, hs, hN, ?_⟩
    intro i hi
    exact (hgood i hi).mono (fun j hj => ⟨hj.1, not_lt.mpr hj.2.le⟩)

/-- Lemma 3.23, `lmm: l_inf_cross-interaction`. Positive row indices are
shifted by one; absolute summability gives the sum its intended meaning. -/
def Lemma_3_23 : Prop :=
  b.HasSymmetricNorm → ¬ b.EquivalentEllOne →
  ∀ T : SchauderSum b hb (ScalarEllInfinity 𝕜) →L[𝕜] SchauderSum b hb (ScalarEllInfinity 𝕜),
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ),
      StrictMono n ∧ (∀ i, StrictMono (m i)) ∧ ∀ i j,
      Summable (fun p : ℕ × ℕ => if p = (i, j) then 0 else
        ‖infinityEntry T (n i) (m i j) (n p.1) (m p.1 p.2)‖) ∧
      (∑' p : ℕ × ℕ, if p = (i, j) then 0 else
        ‖infinityEntry T (n i) (m i j) (n p.1) (m p.1 p.2)‖) < ε / (2 : ℝ) ^ (i + 1)

theorem lemma_3_23 : Lemma_3_23 b hb := by
  intro hs hnot T ε hε
  exact infinity_small_cross_interaction hs hnot T hε

/-- Lemma 3.24, `lmm: preliminary-l-infty-iterated`, including the exact
operator-norm bound on the absolutely convergent weighted matrix series. -/
def Lemma_3_24 : Prop :=
  ∀ T : SchauderSum b hb (ScalarEllInfinity 𝕜) →L[𝕜] SchauderSum b hb (ScalarEllInfinity 𝕜),
    ∀ (x : SchauderSum b hb (ScalarEllInfinity 𝕜)) (i j : ℕ),
      Summable (fun p : ℕ × ℕ => ‖x p.1 p.2 * infinityEntry T i j p.1 p.2‖) ∧
      (∑' p : ℕ × ℕ, ‖x p.1 p.2 * infinityEntry T i j p.1 p.2‖) ≤ ‖T‖ * ‖x‖

theorem lemma_3_24 : Lemma_3_24 b hb := infinity_weighted_entries_bound

/-- Proposition 3.25, `prop: l_inf-iterated-almost-basis-operators`.
One common inner support works in every outer row and output coordinate. -/
def Proposition_3_25 : Prop :=
  ∀ T : SchauderSum b hb (ScalarEllInfinity 𝕜) →L[𝕜] SchauderSum b hb (ScalarEllInfinity 𝕜),
    ∃ M : Set ℕ, M.Infinite ∧ ∀ x : SchauderSum b hb (ScalarEllInfinity 𝕜),
      (∀ r, Function.support (x r : ℕ → 𝕜) ⊆ M) → ∀ i j,
      Summable (fun p : ℕ × ℕ => x p.1 p.2 * infinityEntry T i j p.1 p.2) ∧
      T x i j = ∑' p : ℕ × ℕ, x p.1 p.2 * infinityEntry T i j p.1 p.2

theorem proposition_3_25 : Proposition_3_25 b hb := by
  intro T
  obtain ⟨M, _, hM, hrep⟩ := SchauderSum.infinity_matrix_restriction T
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  refine ⟨M, hM, ?_⟩
  intro x hx i j
  have hz (r s : ℕ) (hs : s ∉ M) : x r s = 0 := by
    by_contra h
    exact hs (hx r h)
  exact ⟨(hrep x hz i j).summable, (hrep x hz i j).tsum_eq.symm⟩

/-- Full Theorem 3.26 on the genuine mixed sum, after the common support
restriction, checked reservoir selection, and sharp Neumann correction. -/
theorem theorem_3_26 : Theorem_3_26 b hb := by
  intro hs hnot
  exact SchauderSum.infinity_hasCPlusPFP_two hs hnot

end PFP
