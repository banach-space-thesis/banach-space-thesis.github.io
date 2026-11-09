import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Ring

/-! Joint Lipschitz control of straight interpolation on a compact source. -/

namespace BanachIsometric.SingularPrism

open scoped NNReal unitInterval

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]

theorem lipschitzWith_unitInterval_smul (f : X → E) {L B : ℝ≥0}
    (hf : LipschitzWith L f) (hB : ∀ x, ‖f x‖ ≤ B) :
    LipschitzWith (L + B) (fun z : unitInterval × X => (z.1 : ℝ) • f z.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨t, x⟩ ⟨u, y⟩
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact t.property.2
  have htu : ‖(t : ℝ) - u‖ ≤ dist (t, x) (u, y) := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have hxy : dist x y ≤ dist (t, x) (u, y) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hsplit : (t : ℝ) • f x - (u : ℝ) • f y =
      (t : ℝ) • (f x - f y) + ((t : ℝ) - u) • f y := by
    rw [smul_sub, sub_smul]
    abel
  rw [dist_eq_norm, hsplit]
  calc
    _ ≤ ‖(t : ℝ) • (f x - f y)‖ + ‖((t : ℝ) - u) • f y‖ := norm_add_le _ _
    _ = ‖(t : ℝ)‖ * dist (f x) (f y) + ‖(t : ℝ) - u‖ * ‖f y‖ := by
      rw [norm_smul, norm_smul, dist_eq_norm]
    _ ≤ 1 * ((L : ℝ) * dist (t, x) (u, y)) + dist (t, x) (u, y) * (B : ℝ) :=
      add_le_add
        (mul_le_mul ht ((hf.dist_le_mul x y).trans (mul_le_mul_of_nonneg_left hxy L.property))
          dist_nonneg zero_le_one)
        (mul_le_mul htu (hB y) (norm_nonneg _) dist_nonneg)
    _ = ((L + B : ℝ≥0) : ℝ) * dist (t, x) (u, y) := by
      push_cast
      ring

theorem exists_lipschitz_unitInterval_interpolation [CompactSpace X] (f g : X → E)
    {L M : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith M g) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun z : unitInterval × X => (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2) := by
  let v : X → E := fun x => g x - f x
  have hv : LipschitzWith (M + L) v := hg.sub hf
  obtain ⟨B, hB, hBound⟩ := (isCompact_range hv.continuous).isBounded.exists_pos_norm_le
  let Bnonneg : ℝ≥0 := ⟨B, hB.le⟩
  have hprod := lipschitzWith_unitInterval_smul v (B := Bnonneg) hv
    (fun x => hBound (v x) (Set.mem_range_self x))
  have hsum := (hf.comp (LipschitzWith.prod_snd : LipschitzWith 1
    (Prod.snd : unitInterval × X → X))).add hprod
  refine ⟨L * 1 + (M + L + Bnonneg), ?_⟩
  convert hsum using 1
  funext z
  change _ = f z.2 + (z.1 : ℝ) • (g z.2 - f z.2)
  rw [sub_smul, one_smul, smul_sub]
  abel

end BanachIsometric.SingularPrism
