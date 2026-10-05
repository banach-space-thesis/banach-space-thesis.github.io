import ThesisCommon.Analysis.CountableTotalDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! A separable normed space has an actual countable total subset of its
continuous dual. Choose a norming functional at each point of a countable
dense set; approximation and its norm bound prove separation. -/
noncomputable section
namespace ThesisCommon
open TopologicalSpace

theorem hasCountableTotalDual_of_separable (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X] :
    HasCountableTotalDual 𝕜 X := by
  classical
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense X
  choose φ hφ hφx using fun x : X => exists_dual_vector'' 𝕜 x
  refine ⟨φ '' D, hD.image φ, ?_⟩
  intro x hx
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  obtain ⟨y, hyD, hnear⟩ := hdense.exists_dist_lt x (by positivity : 0 < ‖x‖ / 4)
  have hzero : φ y x = 0 := hx _ ⟨y, hyD, rfl⟩
  have hy : ‖y‖ ≤ ‖y - x‖ := by
    calc
      ‖y‖ = ‖φ y (y - x)‖ := by
        rw [map_sub, hzero, sub_zero, hφx, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖φ y‖ * ‖y - x‖ := (φ y).le_opNorm _
      _ ≤ ‖y - x‖ := by
        simpa using mul_le_mul_of_nonneg_right (hφ y) (norm_nonneg (y - x))
  have ht := norm_add_le (x - y) y
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hnear
  rw [norm_sub_rev y x] at hy
  nlinarith

end ThesisCommon
