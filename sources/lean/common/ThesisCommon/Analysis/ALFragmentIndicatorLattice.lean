import ThesisCommon.Analysis.ALMeasurableFragments
import ThesisCommon.LpCut

/-! Order, disjoint addition and measurable cuts for the actual fragment
indicator embedding into its finite Stone L1 space. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

omit [HasSolidNorm E] in
theorem alFragmentIndicator_coe (a : PositiveFragmentAlgebra e) :
    (alFragmentIndicator hAL e a : BooleanStonePoint (PositiveFragmentAlgebra e) → ℝ) =ᵐ[
      alFragmentMeasure hAL e] (booleanStoneSet a).indicator (fun _ => (1 : ℝ)) := by
  rw [alFragmentIndicator_eq_lOneIndicator]
  exact lOneIndicator_coe _ _

theorem alFragmentIndicator_nonneg (a : PositiveFragmentAlgebra e) :
    0 ≤ alFragmentIndicator hAL e a := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [alFragmentIndicator_coe hAL e a] with x hx
  rw [hx]
  exact indicator_nonneg (fun _ _ => zero_le_one) _

theorem alFragmentIndicator_bot : alFragmentIndicator hAL e ⊥ = 0 := by
  apply Lp.ext
  filter_upwards [alFragmentIndicator_coe hAL e ⊥,
    Lp.coeFn_zero ℝ 1 (alFragmentMeasure hAL e)] with x hx hz
  simp only [booleanStoneSet_bot, indicator_empty] at hx
  exact hx.trans hz.symm

theorem alFragmentIndicator_inf (a b : PositiveFragmentAlgebra e) :
    alFragmentIndicator hAL e (a ⊓ b) = alFragmentIndicator hAL e a ⊓ alFragmentIndicator hAL e b := by
  apply Lp.ext
  filter_upwards [alFragmentIndicator_coe hAL e (a ⊓ b),
    alFragmentIndicator_coe hAL e a, alFragmentIndicator_coe hAL e b,
    Lp.coeFn_inf (alFragmentIndicator hAL e a) (alFragmentIndicator hAL e b)] with x hab ha hb hi
  rw [hab, hi, Pi.inf_apply, ha, hb, booleanStoneSet_inf]
  by_cases hxa : x ∈ booleanStoneSet a <;> by_cases hxb : x ∈ booleanStoneSet b <;>
    simp [hxa, hxb]

theorem alFragmentIndicator_le_iff (a b : PositiveFragmentAlgebra e) :
    alFragmentIndicator hAL e a ≤ alFragmentIndicator hAL e b ↔ a ≤ b := by
  rw [← inf_eq_left, ← alFragmentIndicator_inf,
    (isometry_alFragmentIndicator hAL e).injective.eq_iff, inf_eq_left]

theorem alFragmentIndicator_sup_of_disjoint (a b : PositiveFragmentAlgebra e)
    (hab : Disjoint a b) :
    alFragmentIndicator hAL e (a ⊔ b) = alFragmentIndicator hAL e a + alFragmentIndicator hAL e b := by
  have hset : Disjoint (booleanStoneSet a) (booleanStoneSet b) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← booleanStoneSet_inf, hab.eq_bot, booleanStoneSet_bot]
  apply Lp.ext
  filter_upwards [alFragmentIndicator_coe hAL e (a ⊔ b), alFragmentIndicator_coe hAL e a,
    alFragmentIndicator_coe hAL e b,
    Lp.coeFn_add (alFragmentIndicator hAL e a) (alFragmentIndicator hAL e b)] with x hab' ha hb hadd
  rw [hab', hadd, Pi.add_apply, ha, hb, booleanStoneSet_sup]
  by_cases hxa : x ∈ booleanStoneSet a <;> by_cases hxb : x ∈ booleanStoneSet b
  · exact (Set.disjoint_left.mp hset hxa hxb).elim
  all_goals simp [hxa, hxb]

theorem alFragmentIndicator_stoneCut (a b : PositiveFragmentAlgebra e) :
    lpCut (booleanStoneSet b) (measurableSet_booleanStoneSet b) (alFragmentIndicator hAL e a) =
      alFragmentIndicator hAL e (a ⊓ b) := by
  apply Lp.ext
  filter_upwards [lpCut_coe (booleanStoneSet b) (measurableSet_booleanStoneSet b)
    (alFragmentIndicator hAL e a), alFragmentIndicator_coe hAL e a,
    alFragmentIndicator_coe hAL e (a ⊓ b)] with x hc ha hab
  rw [hc, hab, booleanStoneSet_inf]
  by_cases hxa : x ∈ booleanStoneSet a <;> by_cases hxb : x ∈ booleanStoneSet b <;>
    simp [hxa, hxb, ha]

end ThesisCommon
