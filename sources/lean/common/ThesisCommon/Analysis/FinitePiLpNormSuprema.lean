import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Order.IsLUB

/-! Finite product norms commute with grouping coordinates, and bounds on
all independent finite choices extend to coordinatewise bounded suprema. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon

theorem piLp_norm_norms_eq_sigma (p : BanachExponent) (hp : 0 < p.val.toReal)
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {E : (i : ι) → κ i → Type*} [∀ i j, NormedAddCommGroup (E i j)]
    (v : ∀ i, PiLp p.val (E i)) :
    ‖WithLp.toLp p.val (fun i => ‖v i‖)‖ =
      ‖WithLp.toLp p.val (fun q : (i : ι) × κ i => v q.1 q.2)‖ := by
  rw [PiLp.norm_eq_sum hp,PiLp.norm_eq_sum hp]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change ‖‖v i‖‖ ^ p.val.toReal = _
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),PiLp.norm_eq_sum hp,one_div,
    Real.rpow_inv_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) hp.ne']
  rfl

theorem piLp_norm_ciSup_le (p : BanachExponent)
    {ι κ : Type*} [Fintype ι] [Nonempty κ]
    (f : ι → κ → ℝ) (hf : ∀ i, BddAbove (Set.range (f i))) {C : ℝ}
    (hb : ∀ k : ι → κ, ‖WithLp.toLp p.val (fun i => f i (k i))‖ ≤ C) :
    ‖WithLp.toLp p.val (fun i => ⨆ k, f i k)‖ ≤ C := by
  classical
  have hs (i : ι) := exists_seq_tendsto_sSup (Set.range_nonempty (f i)) (hf i)
  choose u _ hu hmem using hs
  choose k hk using hmem
  have ht : Tendsto (fun n => WithLp.toLp p.val (fun i => u i n)) atTop
      (𝓝 (WithLp.toLp p.val (fun i => ⨆ j, f i j))) :=
    (PiLp.continuous_toLp p.val (fun _ : ι => ℝ)).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr hu)
  apply le_of_tendsto ht.norm
  exact Filter.Eventually.of_forall (fun n => by
    have hh := hb (fun i => k i n)
    simpa only [hk] using hh)

end ThesisCommon
