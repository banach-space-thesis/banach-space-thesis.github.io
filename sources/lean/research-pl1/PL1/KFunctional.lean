import PL1.ResolventGeneratorGraph

/-!
# The actual graph K-functional and its resolvent bounds

The infimum ranges over the proved resolvent graph and uses the explicit sum
of its two L¹ norms. All estimates concern this actual infimum; monotonicity
is restricted to nonnegative time, the domain relevant to interpolation.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.KFunctional
open Noise Walsh ResolventGeneratorGraph

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

def cost (t : ℝ) (f : Lp K 1 haar) (z : graph K rates) : ℝ :=
  ‖f - z.val.1‖ + t * graphNorm K z.val

def value (t : ℝ) (f : Lp K 1 haar) : ℝ := sInf (Set.range (cost K rates t f))

theorem cost_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) (z : graph K rates) :
    0 ≤ cost K rates t f z :=
  add_nonneg (norm_nonneg _) (mul_nonneg ht (graphNorm_nonneg K z.val))

theorem cost_range_bddBelow {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) :
    BddBelow (Set.range (cost K rates t f)) :=
  ⟨0, by rintro _ ⟨z, rfl⟩; exact cost_nonneg K rates ht f z⟩

theorem le_value {t c : ℝ} (f : Lp K 1 haar)
    (hc : ∀ z : graph K rates, c ≤ cost K rates t f z) : c ≤ value K rates t f :=
  le_csInf (Set.range_nonempty _) (by rintro _ ⟨z, rfl⟩; exact hc z)

theorem value_nonneg {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) :
    0 ≤ value K rates t f := le_value K rates f (cost_nonneg K rates ht f)

theorem value_le_cost {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) (z : graph K rates) :
    value K rates t f ≤ cost K rates t f z :=
  csInf_le (cost_range_bddBelow K rates ht f) ⟨z, rfl⟩

theorem value_le_norm {t : ℝ} (ht : 0 ≤ t) (f : Lp K 1 haar) :
    value K rates t f ≤ ‖f‖ := by
  simpa only [cost, graphNorm, ZeroMemClass.coe_zero, Prod.fst_zero, Prod.snd_zero,
    sub_zero, norm_zero, add_zero, mul_zero] using value_le_cost K rates ht f 0

theorem value_eq_norm_of_one_le {t : ℝ} (ht : 1 ≤ t) (f : Lp K 1 haar) :
    value K rates t f = ‖f‖ := by
  apply le_antisymm (value_le_norm K rates (zero_le_one.trans ht) f)
  apply le_value K rates
  intro z
  have hnorm := norm_le_norm_sub_add f z.val.1
  have hgraph : ‖z.val.1‖ ≤ graphNorm K z.val :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right ht (graphNorm_nonneg K z.val)
  dsimp only [cost]
  linarith

theorem value_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (f : Lp K 1 haar) :
    value K rates s f ≤ value K rates t f := by
  apply le_value K rates
  intro z
  apply (value_le_cost K rates hs f z).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hst (graphNorm_nonneg K z.val))

theorem monotoneOn_value (f : Lp K 1 haar) :
    MonotoneOn (fun t => value K rates t f) (Set.Ici (0 : ℝ)) :=
  fun _ hs _ _ hst => value_mono K rates hs hst f

theorem value_div_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (f : Lp K 1 haar) :
    value K rates t f / t ≤ value K rates s f / s := by
  have ht : 0 < t := hs.trans_le hst
  apply (le_div_iff₀ hs).mpr
  apply le_value K rates
  intro z
  have hcost := div_le_div_of_nonneg_right (value_le_cost K rates ht.le f z) ht.le
  apply (mul_le_mul_of_nonneg_right hcost hs.le).trans
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ ht).mpr
  have h := mul_le_mul_of_nonneg_left hst (norm_nonneg (f - z.val.1))
  dsimp only [cost]
  nlinarith

theorem antitoneOn_value_div (f : Lp K 1 haar) :
    AntitoneOn (fun t => value K rates t f / t) (Set.Ioi (0 : ℝ)) :=
  fun _ hs _ _ hst => value_div_antitone K rates hs hst f

theorem norm_defect_le_two_cost (t : PositiveTime) (f : Lp K 1 haar) (z : graph K rates) :
    ‖f - resolventL1 K rates t f‖ ≤ 2 * cost K rates t f z := by
  have heq : f - resolventL1 K rates t f =
      ((f - z.val.1) - resolventL1 K rates t (f - z.val.1)) +
        (z.val.1 - resolventL1 K rates t z.val.1) := by rw [map_sub]; abel
  have htri := norm_add_le
    ((f - z.val.1) - resolventL1 K rates t (f - z.val.1))
    (z.val.1 - resolventL1 K rates t z.val.1)
  rw [← heq] at htri
  have hdiff := norm_sub_le (f - z.val.1) (resolventL1 K rates t (f - z.val.1))
  have hc := norm_resolvent_apply_le K rates t (f - z.val.1)
  have hg := norm_defect_le K rates t z.property
  have hnon1 := mul_nonneg t.property.le (norm_nonneg z.val.1)
  have hnon2 := mul_nonneg t.property.le (norm_nonneg z.val.2)
  dsimp only [cost, graphNorm]
  nlinarith

theorem half_norm_defect_le (t : PositiveTime) (f : Lp K 1 haar) :
    (1 / 2 : ℝ) * ‖f - resolventL1 K rates t f‖ ≤ value K rates t f := by
  apply le_value K rates
  intro z
  linarith [norm_defect_le_two_cost K rates t f z]

theorem value_le_defect (t : PositiveTime) (f : Lp K 1 haar) :
    value K rates t f ≤ 2 * ‖f - resolventL1 K rates t f‖ + (t : ℝ) * ‖f‖ := by
  let z : graph K rates := ⟨(resolventL1 K rates t f,
    (((t : ℝ)⁻¹ : ℝ) : K) • (f - resolventL1 K rates t f)), resolvent_pair_mem K rates t f⟩
  apply (value_le_cost K rates t.property.le f z).trans
  have hc := mul_le_mul_of_nonneg_left (norm_resolvent_apply_le K rates t f) t.property.le
  have he : (t : ℝ) * ((t : ℝ)⁻¹ * ‖f - resolventL1 K rates t f‖) =
      ‖f - resolventL1 K rates t f‖ := by rw [← mul_assoc, mul_inv_cancel₀ t.property.ne', one_mul]
  simp only [cost, z, graphNorm, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr t.property)]
  nlinarith

end PL1.KFunctional
