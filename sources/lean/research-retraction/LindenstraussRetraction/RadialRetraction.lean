import LindenstraussRetraction.Statements
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Radial retraction onto the closed unit ball

The radial map has Lipschitz constant two in every real or complex normed space.
It proves the final implication in the manuscript's main theorem.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v

variable (𝕜 : Type v) [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The radial retraction, considered as a map into the ambient space. -/
def radialValue (x : X) : X :=
  (((max 1 ‖x‖)⁻¹ : ℝ) : 𝕜) • x

theorem radialValue_norm_le (x : X) : ‖radialValue 𝕜 x‖ ≤ 1 := by
  have hm : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [radialValue, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hm.le)]
  exact (inv_mul_le_one₀ hm).mpr (le_max_right _ _)

@[simp] theorem radialValue_of_norm_le {x : X} (hx : ‖x‖ ≤ 1) :
    radialValue 𝕜 x = x := by
  simp [radialValue, max_eq_left hx]

private theorem radialValue_sub (x y : X) :
    radialValue 𝕜 x - radialValue 𝕜 y =
      (((max 1 ‖x‖)⁻¹ : ℝ) : 𝕜) • (x - y) +
        ((((max 1 ‖x‖)⁻¹ * (max 1 ‖y‖ - max 1 ‖x‖) : ℝ) : 𝕜)) •
          radialValue 𝕜 y := by
  have hm : max 1 ‖x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hn : max 1 ‖y‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hc : (max 1 ‖x‖)⁻¹ * (max 1 ‖y‖ - max 1 ‖x‖) * (max 1 ‖y‖)⁻¹ =
      (max 1 ‖x‖)⁻¹ - (max 1 ‖y‖)⁻¹ := by
    field_simp [hm, hn]
  simp only [radialValue]
  rw [smul_sub, smul_smul,
    ← RCLike.ofReal_mul, hc, RCLike.ofReal_sub, sub_smul]
  abel

theorem radialValue_lipschitz : LipschitzWith 2 (radialValue 𝕜 : X → X) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hm : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hi : (max 1 ‖x‖)⁻¹ ≤ 1 := (inv_le_one₀ hm).mpr (le_max_left _ _)
  have hmax : |max 1 ‖y‖ - max 1 ‖x‖| ≤ ‖x - y‖ := by
    have h := ((LipschitzWith.const (1 : ℝ)).max
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : X → ℝ))).dist_le_mul y x
    simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev] using h
  have hrad := radialValue_norm_le 𝕜 y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  rw [radialValue_sub]
  calc
    ‖_ + _‖ ≤ ‖(((max 1 ‖x‖)⁻¹ : ℝ) : 𝕜) • (x - y)‖ +
        ‖((((max 1 ‖x‖)⁻¹ * (max 1 ‖y‖ - max 1 ‖x‖) : ℝ) : 𝕜)) •
          radialValue 𝕜 y‖ := norm_add_le _ _
    _ = (max 1 ‖x‖)⁻¹ * ‖x - y‖ +
        (max 1 ‖x‖)⁻¹ * |max 1 ‖y‖ - max 1 ‖x‖| * ‖radialValue 𝕜 y‖ := by
      simp only [norm_smul, RCLike.norm_ofReal, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hm.le)]
    _ ≤ (max 1 ‖x‖)⁻¹ * ‖x - y‖ + (max 1 ‖x‖)⁻¹ * ‖x - y‖ := by
      apply add_le_add_left
      calc
        _ ≤ (max 1 ‖x‖)⁻¹ * |max 1 ‖y‖ - max 1 ‖x‖| * 1 :=
          mul_le_mul_of_nonneg_left hrad
            (mul_nonneg (inv_nonneg.mpr hm.le) (abs_nonneg _))
        _ = (max 1 ‖x‖)⁻¹ * |max 1 ‖y‖ - max 1 ‖x‖| := mul_one _
        _ ≤ (max 1 ‖x‖)⁻¹ * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr hm.le)
    _ ≤ 2 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

/-- The radial retraction onto the closed unit ball. -/
def radialRetraction (x : X) : UnitBall X :=
  ⟨radialValue 𝕜 x, radialValue_norm_le 𝕜 x⟩

@[simp] theorem radialRetraction_coe (x : UnitBall X) : radialRetraction 𝕜 x.val = x := by
  apply Subtype.ext
  exact radialValue_of_norm_le 𝕜 x.property

theorem radialRetraction_lipschitz : LipschitzWith 2 (radialRetraction 𝕜 : X → UnitBall X) := by
  apply LipschitzWith.of_dist_le_mul
  exact (radialValue_lipschitz 𝕜).dist_le_mul

theorem radialRetraction_uniformContinuous :
    UniformContinuous (radialRetraction 𝕜 : X → UnitBall X) :=
  (radialRetraction_lipschitz 𝕜).uniformContinuous

theorem hasUniformBidualRetraction_implies_unitBall
    (h : HasUniformBidualRetraction 𝕜 X) : HasUniformUnitBallBidualRetraction 𝕜 X := by
  obtain ⟨r, hr, hri⟩ := h
  refine ⟨fun x => radialRetraction 𝕜 (r x.val),
    (radialRetraction_uniformContinuous 𝕜).comp
      (hr.comp uniformContinuous_subtype_val), ?_⟩
  intro x
  change radialRetraction 𝕜 (r (bidualEmbedding 𝕜 X x.val)) = x
  rw [hri, radialRetraction_coe]

theorem mainUnitBallStatement_implies_mainStatement
    (h : MainUnitBallStatement 𝕜) : MainStatement 𝕜 := by
  obtain ⟨X, hbasis, hball⟩ := h
  refine ⟨X, hbasis, hball, ?_, ?_⟩
  · exact fun hwhole => hball (hasUniformBidualRetraction_implies_unitBall 𝕜 hwhole)
  · exact fun hlip => hball (hasUniformBidualRetraction_implies_unitBall 𝕜
      (hasLipschitzBidualRetraction_implies_uniform 𝕜 X.Carrier hlip))

end LindenstraussRetraction
