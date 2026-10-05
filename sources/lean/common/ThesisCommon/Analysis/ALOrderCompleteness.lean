import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-! Order completeness from norm additivity on the positive cone.
This supplies the supremum construction needed for regular operators between
AL-spaces. The supremum is obtained as an actual norm limit in the given space. -/
noncomputable section
open Filter Set Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
include hAL

omit [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E] in
theorem al_norm_sub_of_le {x y : E} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖y - x‖ = ‖y‖ - ‖x‖ := by
  have h := hAL x (y - x) hx (sub_nonneg.mpr hxy)
  have hsum : x + (y - x) = y := by abel
  rw [hsum] at h
  linarith

omit [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E] in
theorem al_norm_sum {ι : Type*} (s : Finset ι) (u : ι → E)
    (hu : ∀ i ∈ s, 0 ≤ u i) : ‖∑ i ∈ s, u i‖ = ∑ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hs : ∀ j ∈ s, 0 ≤ u j := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert his, Finset.sum_insert his,
      hAL _ _ (hu i (Finset.mem_insert_self i s)) (Finset.sum_nonneg hs), ih hs]

omit [HasSolidNorm E] in
/-- A nonempty, upward directed, norm bounded family of positive elements in
a complete AL-lattice has a supremum. A sequence drawn from the family
converges in norm to this supremum and has the same supremum. -/
theorem al_exists_isLUB_of_directed_norm_bdd {s : Set E} (hs : s.Nonempty)
    (hpos : ∀ x ∈ s, 0 ≤ x) (hdir : DirectedOn (· ≤ ·) s)
    (hbounded : BddAbove (norm '' s)) :
    ∃ x : E, IsLUB s x ∧ ∃ u : ℕ → E, (∀ n, u n ∈ s) ∧
      Tendsto u atTop (𝓝 x) ∧ IsLUB (range u) x := by
  obtain ⟨r, hrmono, hrlim, hrmem⟩ := exists_seq_tendsto_sSup (hs.image norm) hbounded
  choose u humem hunorm using hrmem
  let C : ℝ := sSup (norm '' s)
  have hnormle : ∀ z ∈ s, ‖z‖ ≤ C := fun z hz => le_csSup hbounded ⟨z, hz, rfl⟩
  have hd (n m : ℕ) (hnm : n ≤ m) : dist (u n) (u m) ≤ 2 * (C - r n) := by
    obtain ⟨z, hz, hnz, hmz⟩ := hdir (u n) (humem n) (u m) (humem m)
    calc
      dist (u n) (u m) ≤ dist (u n) z + dist z (u m) := dist_triangle _ _ _
      _ = (‖z‖ - r n) + (‖z‖ - r m) := by
        rw [dist_eq_norm', dist_eq_norm, al_norm_sub_of_le hAL (hpos _ (humem n)) hnz,
          al_norm_sub_of_le hAL (hpos _ (humem m)) hmz, hunorm n, hunorm m]
      _ ≤ 2 * (C - r n) := by have := hnormle z hz; have := hrmono hnm; linarith
  have hzero : Tendsto (fun n => C - r n) atTop (𝓝 0) := by
    simpa [C] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).sub hrlim
  have hCauchy : CauchySeq u := cauchySeq_of_le_tendsto_0' (fun n => 2 * (C - r n)) hd
    (by simpa using hzero.const_mul 2)
  obtain ⟨x, hxlim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hupper : x ∈ upperBounds s := by
    intro y hy
    have hzexists (n : ℕ) := hdir y hy (u n) (humem n)
    choose z hzmem hyz huz using hzexists
    have hdist (n : ℕ) : dist (u n) (z n) ≤ C - r n := by
      rw [dist_eq_norm', al_norm_sub_of_le hAL (hpos _ (humem n)) (huz n), hunorm n]
      exact sub_le_sub_right (hnormle _ (hzmem n)) _
    have hzlim : Tendsto z atTop (𝓝 x) := hxlim.congr_dist
      (squeeze_zero (fun n => dist_nonneg) hdist hzero)
    exact ge_of_tendsto' hzlim hyz
  have hlub : IsLUB s x := ⟨hupper, fun y hy => le_of_tendsto' hxlim fun n => hy (humem n)⟩
  exact ⟨x, hlub, u, humem, hxlim, IsLUB.range_of_tendsto (fun n => hupper (humem n)) hxlim⟩

end ThesisCommon
