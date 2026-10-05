import PFP.MainStatements
import ThesisCommon.Analysis.InfinityFactorization

/-! The scalar ell_infinity section. All spaces are actual bounded sequences.
Matrix representation is proved only after selecting an infinite support.
-/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Lemma 3.17, `lmm: Lind-preliminary-1`, both clauses. The finite maximum
uses NNReal.sup, whose empty value is zero. It is not a summability assumption. -/
def Lemma_3_17 : Prop :=
  ∀ (x : ℕ → ScalarEllInfinity 𝕜) (K : ℝ), 0 < K →
    HasBoundedFiniteSums (𝕜 := 𝕜) x K →
    (∀ m, Tendsto (fun n => x n m) atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ M : Set ℕ, M.Infinite → ∀ N : ℕ,
      ∃ n ∈ M, N < n ∧ (M \ {m | ε < ‖x n m‖}).Infinite)

theorem lemma_3_17 : Lemma_3_17 (𝕜 := 𝕜) := by
  intro x K hK hx
  refine ⟨bounded_finite_sums_coordinate_tendsto_zero hK.le hx, ?_⟩
  intro ε hε M hM N
  obtain ⟨n, hn, hN, hs⟩ := bounded_finite_sums_small_future hK.le hx hε hM N
  refine ⟨n, hn, hN, ?_⟩
  convert hs using 1
  ext m
  simp

/-- Lemma 3.18, `lmm: l_inf-separate-interference`. Strict increase records
the subsequence produced by the source recursion. Absolute summability is
included to give the infinite off-diagonal sum its genuine meaning. -/
def Lemma_3_18 : Prop :=
  ∀ (x : ℕ → ScalarEllInfinity 𝕜) (K : ℝ), 0 < K →
    HasBoundedFiniteSums (𝕜 := 𝕜) x K → ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k,
      Summable (fun j => if j = k then 0 else ‖x (n j) (n k)‖) ∧
      (∑' j, if j = k then 0 else ‖x (n j) (n k)‖) < ε

theorem lemma_3_18 : Lemma_3_18 (𝕜 := 𝕜) := by
  intro x K hK hx ε hε
  obtain ⟨f, hf, _, hs⟩ := bounded_finite_sums_small_off_diagonal hK.le hx
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hε
  exact ⟨f, hf, hs⟩

/-- Proposition 3.19, `prop: l_inf-almost-basis-operators`. The equality
holds for every output coordinate, including those outside M, and every
bounded vector supported in M. Convergence is explicit as well. -/
def Proposition_3_19 : Prop :=
  ∀ T : ScalarEllInfinity 𝕜 →L[𝕜] ScalarEllInfinity 𝕜,
    ∃ M : Set ℕ, M.Infinite ∧ ∀ m (x : ScalarEllInfinity 𝕜),
      Function.support (x : ℕ → 𝕜) ⊆ M →
      Summable (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) ∧
        T x m = ∑' n, x n * T (lp.single ∞ n (1 : 𝕜)) m

theorem proposition_3_19 : Proposition_3_19 (𝕜 := 𝕜) := by
  intro T
  obtain ⟨M, _, hM, hT⟩ := infinity_matrix_restriction T
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  refine ⟨M, hM, ?_⟩
  intro m x hx
  have hzero (n : ℕ) (hn : n ∉ M) : x n = 0 := by
    by_contra hh
    exact hn (hx hh)
  exact ⟨(hT m x hzero).summable, (hT m x hzero).tsum_eq.symm⟩

/-- Full Theorem 3.21, using the source's basis-style proof rather than
assuming weak-star continuity of the original operator. -/
theorem theorem_3_21 : Theorem_3_21 𝕜 := infinity_hasCPlusPFP_two

end PFP
