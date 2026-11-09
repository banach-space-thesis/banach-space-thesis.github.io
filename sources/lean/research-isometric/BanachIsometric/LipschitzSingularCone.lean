import BanachIsometric.SimplexConeCoordinates
import BanachIsometric.RawLipschitzChains
import BanachIsometric.CompactLipschitzOperations

/-! The actual cone of a Lipschitz singular simplex is Lipschitz at the apex
as well as away from it. The estimate uses the weighted distance between the
normalized barycentric bases. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped NNReal Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def singularConeFun (n : ℕ) (f : Simplex n → V) (w : Simplex (n + 1)) : V :=
  if h : 0 < simplexConeRadius n w then
    simplexConeRadius n w • f (simplexConeBase n w h) else 0

theorem exists_lipschitz_singularConeFun (n : ℕ) {f : Simplex n → V} {L : ℝ≥0}
    (hf : LipschitzWith L f) : ∃ K : ℝ≥0, LipschitzWith K (singularConeFun n f) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_univ : IsCompact (univ : Set (Simplex n))).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  have hM (x : Simplex n) : ‖f x‖ ≤ M := (hM₀ x (mem_univ x)).trans (le_max_left _ _)
  refine ⟨2 * L + M, LipschitzWith.of_dist_le_mul ?_⟩
  have hR (w z : Simplex (n + 1)) : |simplexConeRadius n w - simplexConeRadius n z| ≤ dist w z := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (simplexConeRadius_lipschitz n).dist_le_mul w z
  have hApex (w z : Simplex (n + 1)) (hz : ¬ 0 < simplexConeRadius n z) :
      dist (singularConeFun n f w) (singularConeFun n f z) ≤ (↑(2 * L + M) : ℝ) * dist w z := by
    have hz0 := le_antisymm (le_of_not_gt hz) (simplexConeRadius_nonneg n z)
    by_cases hw : 0 < simplexConeRadius n w
    · rw [singularConeFun, dif_pos hw, singularConeFun, dif_neg hz, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hw.le]
      have hRw := hR w z
      rw [hz0, sub_zero, abs_of_nonneg hw.le] at hRw
      calc
        simplexConeRadius n w * ‖f (simplexConeBase n w hw)‖ ≤ dist w z * M :=
          mul_le_mul hRw (hM _) (norm_nonneg _) dist_nonneg
        _ ≤ _ := by push_cast; nlinarith [mul_nonneg L.coe_nonneg (dist_nonneg (x := w) (y := z))]
    · rw [singularConeFun, dif_neg hw, singularConeFun, dif_neg hz, dist_self]
      positivity
  intro w z
  by_cases hz : 0 < simplexConeRadius n z
  · by_cases hw : 0 < simplexConeRadius n w
    · let x := simplexConeBase n w hw
      let y := simplexConeBase n z hz
      let r := simplexConeRadius n w
      let s := simplexConeRadius n z
      have hr : 0 ≤ r := hw.le
      have he : r • f x - s • f y = r • (f x - f y) + (r - s) • f y := by
        rw [smul_sub, sub_smul]
        abel
      have hLip := hf.dist_le_mul x y
      rw [dist_eq_norm] at hLip
      rw [singularConeFun, dif_pos hw, singularConeFun, dif_pos hz, dist_eq_norm]
      change ‖r • f x - s • f y‖ ≤ _
      rw [he]
      calc
        ‖r • (f x - f y) + (r - s) • f y‖ ≤
            r * ‖f x - f y‖ + |r - s| * ‖f y‖ := by
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] using
            norm_add_le (r • (f x - f y)) ((r - s) • f y)
        _ ≤ (L : ℝ) * (r * dist x y) + (M : ℝ) * dist w z := by
          rw [mul_left_comm (L : ℝ), mul_comm (M : ℝ)]
          exact add_le_add (mul_le_mul_of_nonneg_left hLip hw.le)
            (mul_le_mul (hR w z) (hM y) (norm_nonneg _) dist_nonneg)
        _ ≤ _ := by
          push_cast
          have hscale := simplexConeBase_scaled_dist_le n w z hw hz
          change r * dist x y ≤ 2 * dist w z at hscale
          calc
            (L : ℝ) * (r * dist x y) + (M : ℝ) * dist w z ≤
                (L : ℝ) * (2 * dist w z) + (M : ℝ) * dist w z :=
              add_le_add_right (mul_le_mul_of_nonneg_left hscale L.coe_nonneg) _
            _ = _ := by ring
    · rw [dist_comm (singularConeFun n f w), dist_comm w z]
      exact hApex z w hw
  · exact hApex w z hz

def lipschitzSingularCone (n : ℕ) (σ : RawSingularSimplex V n) : RawSingularSimplex V (n + 1) := by
  classical
  exact if h : ∃ L : ℝ≥0, LipschitzWith L σ then
    ⟨singularConeFun n σ, (Classical.choose_spec
      (exists_lipschitz_singularConeFun n (Classical.choose_spec h))).continuous⟩
    else ContinuousMap.const _ 0

theorem lipschitzSingularCone_apply (n : ℕ) (σ : RawSingularSimplex V n)
    (h : ∃ L : ℝ≥0, LipschitzWith L σ) (w : Simplex (n + 1)) :
    lipschitzSingularCone n σ w = singularConeFun n σ w := by
  rw [lipschitzSingularCone, dif_pos h]
  rfl

theorem exists_lipschitz_lipschitzSingularCone (n : ℕ) (σ : RawSingularSimplex V n)
    (h : ∃ L : ℝ≥0, LipschitzWith L σ) : ∃ K : ℝ≥0, LipschitzWith K (lipschitzSingularCone n σ) := by
  have he : (lipschitzSingularCone n σ : Simplex (n + 1) → V) = singularConeFun n σ :=
    funext (lipschitzSingularCone_apply n σ h)
  rw [he]
  exact exists_lipschitz_singularConeFun n (Classical.choose_spec h)

def rawLipschitzCone (n : ℕ) : RawRationalChains V n →ₗ[ℚ] RawRationalChains V (n + 1) :=
  Finsupp.lmapDomain ℚ ℚ (lipschitzSingularCone n)

@[simp] theorem rawLipschitzCone_single (n : ℕ) (σ : RawSingularSimplex V n) (a : ℚ) :
    rawLipschitzCone n (Finsupp.single σ a) = Finsupp.single (lipschitzSingularCone n σ) a := by
  simp [rawLipschitzCone]

end BanachIsometric.SingularPrism
