import PL1.NoiseSemigroup

/-!
# The actual resolvent graph associated to the generator

The submodule is defined by `R₁(f + g) = f`, using the genuine Haar L¹
resolvent. Its graph norm is explicitly the sum of the two L¹ norms, rather
than the maximum norm on the ambient product. Identification with the
infinitesimal semigroup generator is a separate theorem in NoiseGenerator.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PL1.ResolventGeneratorGraph
open Noise Walsh

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

def graph : Submodule K (Lp K 1 haar × Lp K 1 haar) where
  carrier := {z | resolventL1 K rates (dyadicTime 0) (z.1 + z.2) = z.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change resolventL1 K rates (dyadicTime 0) ((x.1 + y.1) + (x.2 + y.2)) = x.1 + y.1
    rw [show (x.1 + y.1) + (x.2 + y.2) = (x.1 + x.2) + (y.1 + y.2) by abel,
      map_add, hx, hy]
  smul_mem' := by
    intro c x hx
    change resolventL1 K rates (dyadicTime 0) (c • x.1 + c • x.2) = c • x.1
    rw [← smul_add, map_smul, hx]

@[simp] theorem mem_graph (f g : Lp K 1 haar) :
    (f, g) ∈ graph K rates ↔ resolventL1 K rates (dyadicTime 0) (f + g) = f := Iff.rfl

/-- This is the graph sum norm, not the ambient product norm. -/
def graphNorm (z : Lp K 1 haar × Lp K 1 haar) : ℝ := ‖z.1‖ + ‖z.2‖

theorem graphNorm_nonneg (z : Lp K 1 haar × Lp K 1 haar) : 0 ≤ graphNorm K z :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_resolvent_apply_le (t : PositiveTime) (f : Lp K 1 haar) :
    ‖resolventL1 K rates t f‖ ≤ ‖f‖ :=
  ((resolventL1 K rates t).le_opNorm f).trans
    (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_resolventL1_le_one K rates t) (norm_nonneg f))

theorem resolvent_one_eq_zero {f : Lp K 1 haar}
    (hf : resolventL1 K rates (dyadicTime 0) f = 0) : f = 0 := by
  have hz (t : PositiveTime) : resolventL1 K rates t f = 0 := by
    have h := DFunLike.congr_fun (resolventL1_identity K rates t (dyadicTime 0)) f
    have ht : ((t : ℝ) : K) ≠ 0 := by exact_mod_cast t.property.ne'
    have h1 : (dyadicTime 0 : ℝ) = 1 := rfl
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
      smul_apply, hf, map_zero, sub_zero, h1, div_one] at h
    exact (smul_eq_zero.mp h.symm).resolve_left ht
  have hzero : Tendsto (fun n => resolventL1 K rates (dyadicTime n) f) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp K 1 haar)) atTop (𝓝 0))
  exact tendsto_nhds_unique (dyadic_resolvent_strong K rates f) hzero

theorem resolvent_one_injective : Function.Injective (resolventL1 K rates (dyadicTime 0)) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply resolvent_one_eq_zero K rates
  rw [map_sub, hfg, sub_self]

theorem snd_unique {f g h : Lp K 1 haar}
    (hfg : (f, g) ∈ graph K rates) (hfh : (f, h) ∈ graph K rates) : g = h := by
  have he : f + g = f + h := resolvent_one_injective K rates (hfg.trans hfh.symm)
  exact add_left_cancel he

/-- The actual resolvent supplies a graph pair at every positive time. -/
theorem resolvent_pair_mem (t : PositiveTime) (f : Lp K 1 haar) :
    (resolventL1 K rates t f,
      (((t : ℝ)⁻¹ : ℝ) : K) • (f - resolventL1 K rates t f)) ∈ graph K rates := by
  have h := DFunLike.congr_fun (resolventL1_identity K rates (dyadicTime 0) t) f
  have h1 : (dyadicTime 0 : ℝ) = 1 := rfl
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, h1, one_div] at h
  change resolventL1 K rates (dyadicTime 0)
    (resolventL1 K rates t f + (((t : ℝ)⁻¹ : ℝ) : K) • (f - resolventL1 K rates t f)) =
    resolventL1 K rates t f
  rw [map_add, map_smul, ← h]
  abel

theorem defect_eq (t : PositiveTime) {f g : Lp K 1 haar}
    (hfg : (f, g) ∈ graph K rates) :
    f - resolventL1 K rates t f = ((t : ℝ) : K) • resolventL1 K rates t g := by
  have h := DFunLike.congr_fun (resolventL1_identity K rates t (dyadicTime 0)) (f + g)
  have h1 : (dyadicTime 0 : ℝ) = 1 := rfl
  change resolventL1 K rates (dyadicTime 0) (f + g) = f at hfg
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, hfg, add_sub_cancel_left, h1, div_one] at h
  exact h

theorem norm_defect_le (t : PositiveTime) {f g : Lp K 1 haar}
    (hfg : (f, g) ∈ graph K rates) :
    ‖f - resolventL1 K rates t f‖ ≤ (t : ℝ) * ‖g‖ := by
  rw [defect_eq K rates t hfg, norm_smul, RCLike.norm_ofReal, abs_of_pos t.property]
  exact mul_le_mul_of_nonneg_left (norm_resolvent_apply_le K rates t g) t.property.le

end PL1.ResolventGeneratorGraph
