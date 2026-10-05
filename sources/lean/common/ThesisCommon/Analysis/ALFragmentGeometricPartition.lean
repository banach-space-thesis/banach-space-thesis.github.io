import ThesisCommon.Analysis.ALFragmentFiniteSplitting
import ThesisCommon.Analysis.ALFragmentDisjointSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-! An atomless positive fragment has an actual countable disjoint partition
of prescribed geometric masses. The remainder tends to zero in norm. If the
original fragment is density homogeneous, all pieces have its density. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace ThesisCommon

theorem IsDensityHomogeneous.of_le {B : Type*} [SemilatticeInf B] [OrderBot B]
    [TopologicalSpace B] [ContinuousInf B] {a b : B}
    (ha : IsDensityHomogeneous a) (hb : b ≠ ⊥) (hba : b ≤ a) :
    IsDensityHomogeneous b := by
  refine ⟨hb, fun c hc hcb => ?_⟩
  exact (ha.2 c hc (hcb.trans hba)).trans (ha.2 b hb hba).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  {e : E} [Fact (0 ≤ e)]
include hAL

theorem exists_positiveFragment_geometric_partition
    (a : PositiveFragmentAlgebra e)
    (ha : NoPositiveAtomsBelow (positiveFragmentValue a)) :
    ∃ p : ℕ → PositiveFragmentAlgebra e,
      (∀ n, p n ≤ a) ∧ Pairwise (fun i j => Disjoint (p i) (p j)) ∧
      (∀ n, ‖positiveFragmentValue (p n)‖ = (1 / 2 : ℝ) ^ (n+1) *
        ‖positiveFragmentValue a‖) ∧
      HasSum (fun n => positiveFragmentValue (p n)) (positiveFragmentValue a) ∧
      ∀ n, ‖positiveFragmentValue a - ∑ i ∈ Finset.range n,
        positiveFragmentValue (p i)‖ = (1 / 2 : ℝ)^n * ‖positiveFragmentValue a‖ := by
  classical
  have hh : ∀ b : Iic a, ∃ c : PositiveFragmentAlgebra e, c ≤ b.val ∧
      ‖positiveFragmentValue c‖ = ‖positiveFragmentValue b.val‖ / 2 := by
    intro b
    apply exists_positiveFragment_le_of_norm hAL b.val (ha.mono b.property)
    · positivity
    · have := norm_nonneg (positiveFragmentValue b.val)
      linarith
  choose half hhalf hhalf_norm using hh
  let r : ℕ → Iic a := fun n => Nat.rec ⟨a, le_rfl⟩
    (fun _ b => ⟨half b, (hhalf b).trans b.property⟩) n
  let R : ℕ → PositiveFragmentAlgebra e := fun n => (r n).val
  have hR0 : R 0 = a := rfl
  have hRstep (n : ℕ) : R (n+1) ≤ R n := hhalf (r n)
  have hRhalf (n : ℕ) : ‖positiveFragmentValue (R (n+1))‖ =
      ‖positiveFragmentValue (R n)‖ / 2 := hhalf_norm (r n)
  have hRanti : Antitone R := antitone_nat_of_succ_le hRstep
  have hRnorm (n : ℕ) : ‖positiveFragmentValue (R n)‖ =
      (1/2 : ℝ)^n * ‖positiveFragmentValue a‖ := by
    induction n with
    | zero => simp [hR0]
    | succ n ih => rw [hRhalf, ih, pow_succ]; ring
  let p : ℕ → PositiveFragmentAlgebra e := fun n => R n \ R (n+1)
  have hpvalue (n : ℕ) : positiveFragmentValue (p n) =
      positiveFragmentValue (R n) - positiveFragmentValue (R (n+1)) := by
    change positiveFragmentValue (R n \ R (n+1)) = _
    rw [positiveFragmentValue_sdiff, inf_eq_right.mpr (hRstep n)]
  have hple (n : ℕ) : p n ≤ a := sdiff_le.trans (r n).property
  have hdlt {i j : ℕ} (hij : i < j) : Disjoint (p i) (p j) :=
    disjoint_sdiff_self_left.mono_right
      (sdiff_le.trans (hRanti (Nat.succ_le_of_lt hij)))
  have hd : Pairwise (fun i j => Disjoint (p i) (p j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hdlt hij
    · exact (hdlt hji).symm
  have hpnorm (n : ℕ) : ‖positiveFragmentValue (p n)‖ =
      (1/2 : ℝ)^(n+1) * ‖positiveFragmentValue a‖ := by
    have heq : positiveFragmentValue (p n) + positiveFragmentValue (R (n+1)) =
        positiveFragmentValue (R n) := by rw [hpvalue]; abel
    have hn := hAL _ _ (positiveFragmentValue_nonneg (p n))
      (positiveFragmentValue_nonneg (R (n+1)))
    rw [heq, hRnorm n, hRnorm (n+1), pow_succ] at hn
    rw [pow_succ]
    linarith
  have hpsum (n : ℕ) : (∑ i ∈ Finset.range n, positiveFragmentValue (p i)) =
      positiveFragmentValue a - positiveFragmentValue (R n) := by
    induction n with
    | zero => simp [hR0]
    | succ n ih => rw [Finset.sum_range_succ, ih, hpvalue]; abel
  have hRlim : Tendsto (fun n => positiveFragmentValue (R n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hRnorm]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_const
        ‖positiveFragmentValue a‖
  refine ⟨p, hple, hd, hpnorm, ?_, ?_⟩
  · apply (hasSum_iff_tendsto_nat_of_summable_norm
      (positiveFragment_summable_norm hAL p hd)).mpr
    simp_rw [hpsum]
    simpa using tendsto_const_nhds.sub hRlim
  · intro n
    rw [hpsum, sub_sub_cancel, hRnorm]

theorem exists_homogeneous_positiveFragment_geometric_partition
    (a : PositiveFragmentAlgebra e)
    (ha : NoPositiveAtomsBelow (positiveFragmentValue a)) (hh : IsDensityHomogeneous a) :
    ∃ p : ℕ → PositiveFragmentAlgebra e,
      (∀ n, p n ≤ a ∧ p n ≠ ⊥ ∧ IsDensityHomogeneous (p n) ∧
        principalDensity (p n) = principalDensity a) ∧
      Pairwise (fun i j => Disjoint (p i) (p j)) ∧
      (∀ n, ‖positiveFragmentValue (p n)‖ = (1/2 : ℝ)^(n+1) *
        ‖positiveFragmentValue a‖) ∧
      HasSum (fun n => positiveFragmentValue (p n)) (positiveFragmentValue a) ∧
      ∀ n, ‖positiveFragmentValue a - ∑ i ∈ Finset.range n,
        positiveFragmentValue (p i)‖ = (1/2 : ℝ)^n * ‖positiveFragmentValue a‖ := by
  obtain ⟨p, hple, hd, hpnorm, hsum, htail⟩ :=
    exists_positiveFragment_geometric_partition hAL a ha
  have hapos : 0 < ‖positiveFragmentValue a‖ := norm_pos_iff.mpr (by
    intro hz
    apply hh.1
    exact (positiveFragmentValue_injective e) (by simpa using hz))
  have hpne (n : ℕ) : p n ≠ ⊥ := by
    intro hz
    have hpos : 0 < ‖positiveFragmentValue (p n)‖ := by rw [hpnorm]; positivity
    simpa [hz] using hpos
  exact ⟨p, fun n => ⟨hple n, hpne n, hh.of_le (hpne n) (hple n),
    hh.2 _ (hpne n) (hple n)⟩, hd, hpnorm, hsum, htail⟩

end ThesisCommon
