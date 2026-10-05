import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.Analysis.L1IndicatorExt

/-! In the finite-input L1 setting, the constant-one function detects
equality of comparable positive operators. A directed positive supremum
therefore has an increasing sequence of members with the same supremum. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon

theorem exists_monotone_seq_ge_in_directed {A : Type*} [Preorder A]
    {s : Set A} (hdir : DirectedOn (· ≤ ·) s) (u : ℕ → A) (hu : ∀ n, u n ∈ s) :
    ∃ v : ℕ → A, Monotone v ∧ (∀ n, v n ∈ s) ∧ ∀ n, u n ≤ v n := by
  let w : ℕ → s := Nat.rec ⟨u 0, hu 0⟩ (fun n a =>
    ⟨(hdir a.val a.property (u (n + 1)) (hu (n + 1))).choose,
      (hdir a.val a.property (u (n + 1)) (hu (n + 1))).choose_spec.1⟩)
  refine ⟨fun n => (w n).val, monotone_nat_of_le_succ ?_, fun n => (w n).property, ?_⟩
  · intro n
    exact (hdir (w n).val (w n).property (u (n + 1)) (hu (n + 1))).choose_spec.2.1
  · intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact (hdir (w n).val (w n).property (u (n + 1)) (hu (n + 1))).choose_spec.2.2

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem lOneIndicator_le_one (a : Set X) (ha : MeasurableSet a) :
    lOneIndicator μ a ha ≤ lOneIndicator μ univ MeasurableSet.univ := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lOneIndicator_coe (μ := μ) a ha,
    lOneIndicator_coe (μ := μ) univ MeasurableSet.univ] with x hx hx'
  rw [hx, hx']
  by_cases hxa : x ∈ a <;> simp [hxa]

theorem positive_lOneOperator_eq_zero_of_one (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (hzero : S (lOneIndicator μ univ MeasurableSet.univ) = 0) : S = 0 := by
  apply lOne_continuousLinearMap_ext_indicators
  intro a ha
  have hupper := positive_operator_monotone hS (lOneIndicator_le_one a ha)
  rw [hzero] at hupper
  exact le_antisymm hupper (hS _ (lOneIndicator_nonneg a ha))

theorem lOneOperator_eq_of_le_of_one {S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hST : S ≤ T) (hone : S (lOneIndicator μ univ MeasurableSet.univ) =
      T (lOneIndicator μ univ MeasurableSet.univ)) : S = T := by
  have hzero := positive_lOneOperator_eq_zero_of_one (T - S) (sub_nonneg.mpr hST) (by
    rw [ContinuousLinearMap.sub_apply, hone, sub_self])
  exact (sub_eq_zero.mp hzero).symm

theorem lOneOperator_directed_countable_sup
    {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)} (hs : s.Nonempty) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hdir : DirectedOn (· ≤ ·) s) {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hS : IsLUB s S) :
    ∃ v : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν), Monotone v ∧ (∀ n, v n ∈ s) ∧ IsLUB (range v) S := by
  let one := lOneIndicator μ univ MeasurableSet.univ
  have hone : 0 ≤ one := lOneIndicator_nonneg _ _
  let c : Set (Lp ℝ 1 ν) := (fun T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν => T one) '' s
  have hcpos : ∀ x ∈ c, 0 ≤ x := by rintro _ ⟨T, hT, rfl⟩; exact hpos T hT one hone
  have hcdir : DirectedOn (· ≤ ·) c := by
    rintro _ ⟨T, hT, rfl⟩ _ ⟨U, hU, rfl⟩
    obtain ⟨V, hV, hTV, hUV⟩ := hdir T hT U hU
    exact ⟨V one, ⟨V, hV, rfl⟩, hTV one hone, hUV one hone⟩
  have hcLUB : IsLUB c (S one) := operator_isLUB_apply_of_directed
    (lOne_norm_add_of_nonneg ν) hs hpos hdir hS one hone
  have hcbdd : BddAbove (norm '' c) := by
    refine ⟨‖S one‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply norm_le_norm_of_abs_le_abs
    have hxS := hcLUB.1 hx
    simpa only [abs_of_nonneg (hcpos x hx), abs_of_nonneg ((hcpos x hx).trans hxS)] using hxS
  obtain ⟨z, hz, u, hu, _, huLUB⟩ := al_exists_isLUB_of_directed_norm_bdd
    (lOne_norm_add_of_nonneg ν) (hs.image _) hcpos hcdir hcbdd
  have hzS := hz.unique hcLUB
  rw [hzS] at huLUB
  choose T hT hTeq using hu
  obtain ⟨v, hvmono, hvmem, hTv⟩ := exists_monotone_seq_ge_in_directed hdir T hT
  let U := sSup (range v)
  have hU : IsLUB (range v) U := isLUB_csSup (range_nonempty v) ⟨S, by
    rintro _ ⟨n, rfl⟩; exact hS.1 (hvmem n)⟩
  have hUS : U ≤ S := hU.2 (by rintro _ ⟨n, rfl⟩; exact hS.1 (hvmem n))
  have hSUone : S one ≤ U one := by
    apply huLUB.2
    rintro _ ⟨n, rfl⟩
    rw [← hTeq n]
    exact ((hTv n).trans (hU.1 ⟨n, rfl⟩)) one hone
  have heq : U = S := lOneOperator_eq_of_le_of_one hUS (le_antisymm (hUS one hone) hSUone)
  exact ⟨v, hvmono, hvmem, heq ▸ hU⟩

end ThesisCommon
