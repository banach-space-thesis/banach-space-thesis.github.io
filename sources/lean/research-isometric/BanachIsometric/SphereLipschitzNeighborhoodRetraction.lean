import BanachIsometric.LipschitzNeighborhoodRetraction
import BanachIsometric.LipschitzNormalization

/-! The actual norm unit sphere retracts from the open set of vectors
of norm greater than one half. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric NormedSpace
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereLipschitzNeighborhoodRetraction :
    LipschitzNeighborhoodRetraction (sphere (0 : E) 1) := by
  let U : Set E := {x | (1 / 2 : ℝ) < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hSub : sphere (0 : E) 1 ⊆ U := by
    intro x hx
    change (1 / 2 : ℝ) < ‖x‖
    rw [show ‖x‖ = 1 by simpa only [mem_sphere, dist_zero_right] using hx]
    norm_num
  have hLower (x : U) : (1 / 2 : ℝ) ≤ ‖x.val‖ := le_of_lt x.property
  have hNe (x : U) : x.val ≠ 0 := by
    intro hx
    have h := hLower x
    rw [hx, norm_zero] at h
    norm_num at h
  let ε : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hLip : LipschitzWith (2 * 1 / ε) (fun x : U => normalize x.val) :=
    lipschitzWith_normalize_of_lower_bound (LipschitzWith.subtype_val U)
      (by change (0 : ℝ) < 1 / 2; norm_num) hLower
  have hSphere (x : U) : normalize x.val ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right] using norm_normalize (hNe x)
  refine ⟨U, hU, hSub, ⟨fun x => ⟨normalize x.val, hSphere x⟩,
    (hLip.subtype_mk hSphere).continuous⟩, 2 * 1 / ε, hLip.subtype_mk hSphere, ?_⟩
  intro x
  apply Subtype.ext
  exact normalize_eq_self_of_norm_eq_one (by
    simpa only [mem_sphere, dist_zero_right] using x.property)

end BanachIsometric.SingularPrism
