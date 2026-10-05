import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.RCLikeL1FiniteCutApproximation
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Sequences

/-! The constructive cutoff part of source Lemma 5.1. A lower bound for every
finite localization yields normalized inputs with disjoint finite-measure
output witnesses. The construction is valid over either scalar field and on
arbitrary measure spaces; the main theorem supplies its numerical hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem disjointOutputWitness_step (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ Θ, MeasurableSet Θ → ν Θ < ∞ → c ≤ alphaTheta T Θ)
    {I : Type*} (F : Finset I) (f : I → LOne 𝕜 μ) (B : I → Set Y)
    (hB : ∀ i ∈ F, MeasurableSet (B i)) (hfin : ∀ i ∈ F, ν (B i) < ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : LOne 𝕜 μ, ∃ A C : Set Y, ∃ hA : MeasurableSet A,
      ∃ hC : MeasurableSet C,
      ‖g‖ = 1 ∧ ν A < ∞ ∧ c - ε < ‖lpCut A hA (T g)‖ ∧
      ∀ i ∈ F, ‖lpCut C hC (T (f i))‖ ≤ ε ∧ Disjoint (B i \ C) A := by
  classical
  let Θ := ⋃ i ∈ F, B i
  have hΘ : MeasurableSet Θ := MeasurableSet.biUnion (Finset.countable_toSet F) hB
  have hΘfin : ν Θ < ∞ := (measure_biUnion_finset_le F B).trans_lt
    (ENNReal.sum_lt_top.mpr hfin)
  obtain ⟨δ, hδ, hδcut⟩ := finite_rclike_lOneCut_small_measure F (fun i => T (f i)) hε
  let r : ℝ := c - min ε (c / 2)
  have hr : 0 ≤ r := by dsimp [r]; have := min_le_right ε (c / 2); linarith
  have hrc : r < c := sub_lt_self _ (lt_min hε (by linarith))
  have hεr : c - ε ≤ r := sub_le_sub_left (min_le_left _ _) _
  have hrsup : r < smallSetSup T Θ δ :=
    hrc.trans_le ((hlower Θ hΘ hΘfin).trans (alphaTheta_le_smallSetSup T Θ hΘ hδ))
  obtain ⟨q, ⟨C, hC, hCΘ, hCδ, rfl⟩, hq⟩ := exists_lt_of_lt_csSup
    (s := {q : ℝ | ∃ C, MeasurableSet C ∧ C ⊆ Θ ∧
      ν C < ENNReal.ofReal δ ∧ q = cutOperatorNorm T (Θᶜ ∪ C)})
    ⟨_, ∅, MeasurableSet.empty, empty_subset _, by simpa using ENNReal.ofReal_pos.mpr hδ,
      rfl⟩ hrsup
  let G := Θᶜ ∪ C
  have hG : MeasurableSet G := hΘ.compl.union hC
  let U := (lpCutL G hG).comp T
  have hrU : (⟨r, hr⟩ : ℝ≥0) < ‖U‖₊ := by
    exact_mod_cast (show r < ‖U‖ by simpa [U, G, cutOperatorNorm_eq _ _ hG] using hq)
  obtain ⟨g, hg, hUg⟩ := U.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hrU
  have hg1 : ‖g‖ = 1 := congrArg (fun q : ℝ≥0 => (q : ℝ)) hg
  have hgcut : c - ε < ‖lpCut G hG (T g)‖ := hεr.trans_lt (by exact_mod_cast hUg)
  obtain ⟨D, hD, hDfin, hDcut⟩ := rclike_lOneCut_exists_finite_measure (T g)
    (sub_pos.mpr hgcut)
  refine ⟨g, G \ Dᶜ, C, hG.diff hD.compl, hC, hg1,
    (measure_mono (by intro y hy; exact not_not.mp hy.2)).trans_lt hDfin, ?_, ?_⟩
  · have hh := norm_rclike_lOneCut_sub_le_diff G Dᶜ hG hD.compl (T g)
    linarith
  · intro i hi
    refine ⟨hδcut i hi C hC hCδ.le, Set.disjoint_left.mpr ?_⟩
    intro y hy hyA
    have hyΘ : y ∈ Θ := mem_iUnion₂.mpr ⟨i, hi, hy.1⟩
    rcases hyA.1 with hyG | hyG
    · exact hyG hyΘ
    · exact hy.2 hyG

theorem exists_almost_disjointOutputWitness (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ Θ, MeasurableSet Θ → ν Θ < ∞ → c ≤ alphaTheta T Θ) :
    ∃ f : ℕ → LOne 𝕜 μ, ∃ B C : ℕ → Set Y,
      ∃ hB : ∀ n, MeasurableSet (B n), ∃ hC : ∀ n, MeasurableSet (C n),
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (B n) < ∞) ∧
      (∀ n, c - (1 / 2 : ℝ) ^ (n + 1) < ‖lpCut (B n) (hB n) (T (f n))‖) ∧
      ∀ i j, i < j → ‖lpCut (C j) (hC j) (T (f i))‖ ≤ (1 / 2 : ℝ) ^ (j + 1) ∧
        Disjoint (B i \ C j) (B j) := by
  classical
  let D := LOne 𝕜 μ × {A : Set Y // MeasurableSet A ∧ ν A < ∞}
  let E := D × {C : Set Y // MeasurableSet C}
  have hstep : ∀ n : ℕ, ∀ F : Finset D, ∃ a : E,
      ‖a.1.1‖ = 1 ∧
      c - (1 / 2 : ℝ) ^ (n + 1) < ‖lpCut a.1.2.1 a.1.2.2.1 (T a.1.1)‖ ∧
      ∀ d ∈ F, ‖lpCut a.2.1 a.2.2 (T d.1)‖ ≤ (1 / 2 : ℝ) ^ (n + 1) ∧
        Disjoint (d.2.1 \ a.2.1) a.1.2.1 := by
    intro n F
    obtain ⟨g, A, C, hA, hC, hg, hAfin, hgcut, hprev⟩ :=
      disjointOutputWitness_step T hc hlower F (fun d => d.1) (fun d => d.2.1)
        (fun d _ => d.2.2.1) (fun d _ => d.2.2.2) (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1))
    exact ⟨((g, ⟨A, hA, hAfin⟩), ⟨C, hC⟩), hg, hgcut, hprev⟩
  choose next hnext using hstep
  let F : ℕ → Finset D := Nat.rec ∅ (fun n F => insert (next n F).1 F)
  let a : ℕ → E := fun n => next n (F n)
  have hmem : ∀ n i, i < n → (a i).1 ∈ F n := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      change (a i).1 ∈ insert (a n).1 (F n)
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · exact Finset.mem_insert_of_mem (ih i h)
      · exact Finset.mem_insert_self _ _
  refine ⟨fun n => (a n).1.1, fun n => (a n).1.2.1, fun n => (a n).2.1,
    fun n => (a n).1.2.2.1, fun n => (a n).2.2,
    fun n => (hnext n (F n)).1, fun n => (a n).1.2.2.2,
    fun n => (hnext n (F n)).2.1, ?_⟩
  intro i j hij
  exact (hnext j (F j)).2.2 (a i).1 (hmem j i hij)

theorem exists_disjointOutputWitness_bounds (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ Θ, MeasurableSet Θ → ν Θ < ∞ → c ≤ alphaTheta T Θ) :
    ∃ f : ℕ → LOne 𝕜 μ, ∃ A : ℕ → Set Y,
      ∃ hA : ∀ n, MeasurableSet (A n),
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (A n) < ∞) ∧ Pairwise (Disjoint on A) ∧
      ∀ n, c - (1 / 2 : ℝ) ^ n ≤ ‖lpCut (A n) (hA n) (T (f n))‖ := by
  obtain ⟨f, B, C, hB, hC, hf, hBfin, hbig, hprev⟩ :=
    exists_almost_disjointOutputWitness T hc hlower
  let U : ℕ → Set Y := fun n => ⋃ j : ℕ, C (n + 1 + j)
  have hU : ∀ n, MeasurableSet (U n) := fun n => MeasurableSet.iUnion (fun j => hC _)
  let A : ℕ → Set Y := fun n => B n \ U n
  have hA : ∀ n, MeasurableSet (A n) := fun n => (hB n).diff (hU n)
  have hdisjlt : ∀ i j, i < j → Disjoint (A i) (A j) := by
    intro i j hij
    apply (hprev i j hij).2.mono _ (diff_subset : A j ⊆ B j)
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro hyC
    apply hy.2
    have heq : i + 1 + (j - (i + 1)) = j := by omega
    exact mem_iUnion.mpr ⟨j - (i + 1), by simpa only [heq] using hyC⟩
  have hdisj : Pairwise (Disjoint on A) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hdisjlt i j hij
    · exact (hdisjlt j i hij).symm
  have hgeom : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j) (2 : ℝ) := by
    convert hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1) using 1
    norm_num
  have htail : ∀ n : ℕ, HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (n + 1 + j + 1))
      ((1 / 2 : ℝ) ^ (n + 1)) := by
    intro n
    convert hgeom.mul_left ((1 / 2 : ℝ) ^ (n + 2)) using 1
    · funext j
      rw [← pow_add]
      congr 1
      omega
    · rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
      ring
  refine ⟨f, A, hA, hf, fun n => (measure_mono diff_subset).trans_lt (hBfin n), hdisj, ?_⟩
  intro n
  have hUbound : ‖lpCut (U n) (hU n) (T (f n))‖ ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    norm_rclike_lOneCut_iUnion_le_of_hasSum (fun j => C (n + 1 + j)) (fun j => hC _)
      (T (f n)) (htail n) (fun j => (hprev n (n + 1 + j) (by omega)).1)
  have hdiff := norm_rclike_lOneCut_sub_le_diff (B n) (U n) (hB n) (hU n) (T (f n))
  have hlarge := hbig n
  rw [pow_succ] at hlarge hUbound
  change c - (1 / 2 : ℝ) ^ n ≤ ‖lpCut (B n \ U n) (hA n) (T (f n))‖
  linarith

theorem exists_disjointOutputWitness_limit (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ Θ, MeasurableSet Θ → ν Θ < ∞ → c ≤ alphaTheta T Θ) :
    ∃ f : ℕ → LOne 𝕜 μ, ∃ A : ℕ → Set Y,
      ∃ hA : ∀ n, MeasurableSet (A n), ∃ l : ℝ,
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (A n) < ∞) ∧ Pairwise (Disjoint on A) ∧
      c ≤ l ∧ Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 l) := by
  obtain ⟨f, A, hA, hf, hfin, hdisj, hbound⟩ := exists_disjointOutputWitness_bounds T hc hlower
  have hbounded : ∀ n, ‖lpCut (A n) (hA n) (T (f n))‖ ∈ Icc (0 : ℝ) ‖T‖ := by
    intro n
    refine ⟨norm_nonneg _, (norm_lpCut_le _ _ _).trans ?_⟩
    simpa only [hf, mul_one] using T.le_opNorm (f n)
  obtain ⟨l, _, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hbounded
  have herror : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (φ n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).comp hφ.tendsto_atTop
  have hcl : c ≤ l := by
    apply le_of_tendsto_of_tendsto' (by simpa using tendsto_const_nhds.sub herror) hconv
    intro n
    simpa only [one_div, inv_pow, Function.comp_apply] using hbound (φ n)
  exact ⟨fun n => f (φ n), fun n => A (φ n), fun n => hA (φ n), l,
    fun n => hf (φ n), fun n => hfin (φ n),
    fun i j hij => hdisj (hφ.injective.ne hij), hcl, hconv⟩

end PEMS
