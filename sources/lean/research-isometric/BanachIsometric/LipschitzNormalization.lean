import BanachIsometric.ExactFamilyTopology

/-!
# Lipschitz normalisation with an actual positive norm bound

Compactness supplies the lower bound for a nonvanishing Lipschitz family.
Applied to evaluated exact section maps, this proves that the paper's actual
normalised direction map is Lipschitz, not just continuous.
-/

namespace BanachIsometric

open NormedSpace Set
open scoped NNReal

section General

variable {X V : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lipschitzWith_normalize_of_lower_bound
    {f : X → V} {C ε : ℝ≥0} (hf : LipschitzWith C f) (hε : 0 < ε)
    (hlower : ∀ x, (ε : ℝ) ≤ ‖f x‖) :
    LipschitzWith (2 * C / ε) (fun x => normalize (f x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hεR : (0 : ℝ) < ε := hε
  have hfy : f y ≠ 0 := by
    intro hz
    have hy := hlower y
    rw [hz, norm_zero] at hy
    linarith
  have hg := norm_mul_normalize_sub_le (f x) (f y) hfy
  have hL : ‖f x - f y‖ ≤ (C : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hf.dist_le_mul x y
  rw [dist_eq_norm]
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hεR).mpr
  calc
    ‖normalize (f x) - normalize (f y)‖ * (ε : ℝ) =
        (ε : ℝ) * ‖normalize (f x) - normalize (f y)‖ := mul_comm _ _
    _ ≤ ‖f x‖ * ‖normalize (f x) - normalize (f y)‖ :=
      mul_le_mul_of_nonneg_right (hlower x) (norm_nonneg _)
    _ ≤ 2 * ‖f x - f y‖ := hg
    _ ≤ 2 * ((C : ℝ) * dist x y) := mul_le_mul_of_nonneg_left hL (by norm_num)
    _ = (2 * (C : ℝ)) * dist x y := by ring

theorem exists_lipschitz_normalize_of_compact [CompactSpace X]
    {f : X → V} {C : ℝ≥0} (hf : LipschitzWith C f) (hne : ∀ x, f x ≠ 0) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => normalize (f x)) := by
  classical
  by_cases hX : Nonempty X
  · letI := hX
    obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.norm.continuousOn
    let ε : ℝ≥0 := ‖f x₀‖₊
    have hε : 0 < ε := by exact_mod_cast norm_pos_iff.mpr (hne x₀)
    exact ⟨2 * C / ε, lipschitzWith_normalize_of_lower_bound hf hε
      (fun x => hmin (mem_univ x))⟩
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨0, LipschitzWith.of_dist_le_mul (fun x => isEmptyElim x)⟩

end General

namespace ExactTangentialFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)

theorem exists_lipschitz_direction (hg0 : g 0 = 0) {y : E} (hy : 0 < p y) :
    ∃ L : ℝ≥0, LipschitzWith L (A.direction hg0 hy) := by
  letI : CompactSpace (Metric.sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  obtain ⟨C, hC⟩ := A.maps_lipschitz
  obtain ⟨L, hL⟩ := exists_lipschitz_normalize_of_compact
    ((ContinuousLinearMap.apply ℝ V y).lipschitz.comp hC) (A.evaluation_ne_zero hg0 hy)
  refine ⟨L, LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
  simpa only [Subtype.dist_eq] using hL.dist_le_mul u v

end ExactTangentialFamily

end BanachIsometric
