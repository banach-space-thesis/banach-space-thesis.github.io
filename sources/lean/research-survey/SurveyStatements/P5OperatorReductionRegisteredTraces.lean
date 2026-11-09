import SurveyStatements.P5OperatorReductionReservoir
import SurveyStatements.P5Support.LpHaarTraceLimit
import SurveyStatements.P5Support.LpHaarFiniteSplits

/-! Actual simultaneous dyadic traces after restricting any existing
absolute-level reservoir. All finite-additivity and measure bounds are
proved from the original operator coefficients and their scalar limits. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 I : Type*} [RCLike 𝕜] [Countable I]

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

structure RegisteredDyadicTrace (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (r : ℕ → ℕ) (M : ℝ) where
  value : LpHaarDyadicSetIndex → 𝕜
  bound : ∀ i, ‖value i‖ ≤ M *
    (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i)
  limit : ∀ i, Tendsto (fun n => lpHaarLevelTrace d (r n) (lpHaarDyadicSet i))
    atTop (𝓝 (value i))
  equal_sets : ∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → value i = value j
  additive : ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
    lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j →
      value k = value i + value j

theorem exists_registered_dyadic_traces
    (d : I → ∀ n, Fin (2 ^ n) → 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i n k, ‖d i n k‖ ≤ M)
    (r : ℕ → ℕ) (hr : StrictMono r) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ StrictMono (r ∘ s) ∧
      Nonempty (∀ i, RegisteredDyadicTrace (d i) (r ∘ s) M) := by
  have hv (n : ℕ) (i : I × LpHaarDyadicSetIndex) :
      ‖lpHaarLevelTrace (d i.1) (r n) (lpHaarDyadicSet i.2)‖ ≤ M := by
    have hb := lpHaarLevelTrace_norm_le (d i.1) hM (hd i.1) (r n)
      (lpHaarDyadicSet i.2) (lpHaarDyadicSet_measurable i.2)
    have hmass : (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i.2) ≤ 1 := by
      simpa using measureReal_mono
        (μ := volume.restrict (Icc (0 : ℝ) 1)) (subset_univ (lpHaarDyadicSet i.2))
    exact hb.trans (by nlinarith)
  obtain ⟨a, s, hs, _, ha⟩ := haar_countable_trace_cluster
    (fun n (i : I × LpHaarDyadicSetIndex) =>
      lpHaarLevelTrace (d i.1) (r n) (lpHaarDyadicSet i.2)) hv
  refine ⟨s, hs, hr.comp hs, ⟨fun i =>
    ⟨fun j => a (i, j), ?_, ?_, ?_, ?_⟩⟩⟩
  · intro j
    exact le_of_tendsto (ha (i, j)).norm (Eventually.of_forall (fun n =>
      lpHaarLevelTrace_norm_le (d i) hM (hd i) (r (s n))
        (lpHaarDyadicSet j) (lpHaarDyadicSet_measurable j)))
  · intro j
    exact ha (i, j)
  · intro j k hjk
    apply tendsto_nhds_unique (ha (i, j))
    simpa only [hjk] using ha (i, k)
  · intro j k l hjk hl
    apply tendsto_nhds_unique (ha (i, l))
    convert (ha (i, j)).add (ha (i, k)) using 1
    funext n
    rw [hl, lpHaarLevelTrace_union (d i) (r (s n)) _ _
      (lpHaarDyadicSet_measurable j) (lpHaarDyadicSet_measurable k) hjk]

def RegisteredDyadicTrace.restrict {d : ∀ n, Fin (2 ^ n) → 𝕜}
    {r : ℕ → ℕ} {M : ℝ} (a : RegisteredDyadicTrace d r M)
    (s : ℕ → ℕ) (hs : StrictMono s) : RegisteredDyadicTrace d (r ∘ s) M where
  value := a.value
  bound := a.bound
  limit := fun i => (a.limit i).comp hs.tendsto_atTop
  equal_sets := a.equal_sets
  additive := a.additive

theorem exists_registered_operator_traces (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : I → IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    {C : ℝ} (hC : 0 ≤ C) (hQ : ∀ i, ‖Q i‖ ≤ C)
    (r : ℕ → ℕ) (hr : StrictMono r) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ StrictMono (r ∘ s) ∧
      Nonempty (∀ i, RegisteredDyadicTrace
        (fun n k => lpHaarDyadicCoefficient 𝕜 p n k (Q i (lpHaarDyadic 𝕜 p n k)))
        (r ∘ s) (6 * C)) := by
  apply exists_registered_dyadic_traces _ (mul_nonneg (by norm_num) hC) _ r hr
  intro i n k
  exact (lpHaar_operator_diagonal_norm_le 𝕜 p hp (Q i) n k).trans
    (mul_le_mul_of_nonneg_left (hQ i) (by norm_num))

theorem lpHaarLevelTrace_mul (d : ∀ n, Fin (2 ^ n) → 𝕜) (c : 𝕜)
    (n : ℕ) (s : Set ℝ) :
    lpHaarLevelTrace (fun l k => c * d l k) n s = c * lpHaarLevelTrace d n s := by
  unfold lpHaarLevelTrace
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- There is one reservoir for a countable family even when its bounds
vary without a common finite upper bound. -/
theorem exists_registered_dyadic_traces_varying_bounds
    (d : I → ∀ n, Fin (2 ^ n) → 𝕜) (M : I → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hd : ∀ i n k, ‖d i n k‖ ≤ M i)
    (r : ℕ → ℕ) (hr : StrictMono r) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ StrictMono (r ∘ s) ∧
      Nonempty (∀ i, RegisteredDyadicTrace (d i) (r ∘ s) (M i)) := by
  let c (i : I) : 𝕜 := ((M i + 1 : ℝ) : 𝕜)
  have hcpos (i : I) : 0 < M i + 1 := by linarith [hM i]
  have hcnorm (i : I) : ‖c i‖ = M i + 1 := by
    simp only [c, RCLike.norm_ofReal, abs_of_pos (hcpos i)]
  have hcne (i : I) : c i ≠ 0 := by
    rw [← norm_ne_zero_iff, hcnorm]
    exact (hcpos i).ne'
  let e (i : I) (n : ℕ) (k : Fin (2 ^ n)) : 𝕜 := (c i)⁻¹ * d i n k
  have he (i : I) (n : ℕ) (k : Fin (2 ^ n)) : ‖e i n k‖ ≤ 1 := by
    dsimp only [e]
    rw [norm_mul, norm_inv, hcnorm]
    calc
      _ ≤ (M i + 1)⁻¹ * M i :=
        mul_le_mul_of_nonneg_left (hd i n k) (inv_nonneg.mpr (hcpos i).le)
      _ ≤ (M i + 1)⁻¹ * (M i + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (hcpos i).le)
      _ = 1 := inv_mul_cancel₀ (hcpos i).ne'
  obtain ⟨s, hs, hrs, ⟨a⟩⟩ := exists_registered_dyadic_traces e zero_le_one he r hr
  have htrace (i : I) (j : LpHaarDyadicSetIndex) :
      Tendsto (fun n => lpHaarLevelTrace (d i) (r (s n)) (lpHaarDyadicSet j)) atTop
        (𝓝 (c i * (a i).value j)) := by
    have h := ((a i).limit j).const_mul (c i)
    convert h using 1
    funext n
    dsimp only [Function.comp_apply]
    change lpHaarLevelTrace (d i) (r (s n)) (lpHaarDyadicSet j) =
      c i * lpHaarLevelTrace (fun l k => (c i)⁻¹ * d i l k) (r (s n)) (lpHaarDyadicSet j)
    rw [lpHaarLevelTrace_mul, ← mul_assoc, mul_inv_cancel₀ (hcne i), one_mul]
  refine ⟨s, hs, hrs, ⟨fun i =>
    ⟨fun j => c i * (a i).value j, ?_, htrace i, ?_, ?_⟩⟩⟩
  · intro j
    exact le_of_tendsto (htrace i j).norm (Eventually.of_forall (fun n =>
      lpHaarLevelTrace_norm_le (d i) (hM i) (hd i) (r (s n))
        (lpHaarDyadicSet j) (lpHaarDyadicSet_measurable j)))
  · intro j k hjk
    dsimp only
    rw [(a i).equal_sets j k hjk]
  · intro j k l hjk hl
    dsimp only
    rw [(a i).additive j k l hjk hl, mul_add]

theorem exists_universal_operator_trace_reservoir (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : I → IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      Nonempty (∀ i, RegisteredDyadicTrace
        (fun n k => lpHaarDyadicCoefficient 𝕜 p n k (Q i (lpHaarDyadic 𝕜 p n k)))
        r (6 * ‖Q i‖)) := by
  obtain ⟨r, hr, _, ha⟩ := exists_registered_dyadic_traces_varying_bounds
    (fun i n k => lpHaarDyadicCoefficient 𝕜 p n k (Q i (lpHaarDyadic 𝕜 p n k)))
    (fun i => 6 * ‖Q i‖) (fun i => mul_nonneg (by norm_num) (norm_nonneg _))
    (fun i => lpHaar_operator_diagonal_norm_le 𝕜 p hp (Q i))
    id (fun _ _ h => h)
  exact ⟨r, hr, ha⟩

instance countableLpHaarFiniteSplit : Countable LpHaarFiniteSplit := by
  let encode (S : LpHaarFiniteSplit) :
      Σ n : ℕ, Finset (Fin (2 ^ n)) × (Fin (2 ^ n) → Bool) :=
    ⟨S.level, (S.atoms, S.signs)⟩
  have hinj : Function.Injective encode := by
    intro S T h
    cases S
    cases T
    cases h
    rfl
  exact hinj.countable

end SurveyStatements.P5OperatorReduction
