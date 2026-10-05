import ThesisCommon.Analysis.UncountableSchauderBasis
import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual scalar ℓp unit family on an arbitrary index type. The expansion
is the finite-subset net; the failure of an ℓ₁ lower estimate uses only that
the index type is infinite.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ : Type*} [RCLike 𝕜]

def scalarLpSchauderFamily (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    NormalizedSchauderFamily 𝕜 Γ (lp (fun _ : Γ => 𝕜) p) where
  vector γ := lp.single p γ 1
  coord := lpCoordinate p
  biorthogonal i j := by simp [lpCoordinate_apply, lp.single_apply, Pi.single_apply]
  norm_vector i := by
    rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_one]
  expansion x := by
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using lp.hasSum_single hp x

theorem scalarLpSchauderFamily_oneUnconditional (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : (scalarLpSchauderFamily (𝕜 := 𝕜) (Γ := Γ) p hp).IsOneUnconditional := by
  let b := scalarLpSchauderFamily (𝕜 := 𝕜) (Γ := Γ) p hp
  refine ⟨le_rfl, ?_⟩
  intro F a c hac
  apply lp_norm_le_mul_of_pointwise _ _ zero_le_one
  intro i
  change ‖b.coord i (∑ n ∈ F, a n • b.vector n)‖ ≤
    1 * ‖b.coord i (∑ n ∈ F, c n • b.vector n)‖
  rw [b.coord_finite_sum, b.coord_finite_sum, one_mul]
  by_cases hi : i ∈ F
  · simpa only [if_pos hi] using hac i hi
  · simp [hi]

theorem scalarLpExtend_norm_arbitrary (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Γ ↪ Γ)
    (x : lp (fun _ : Γ => 𝕜) p) : ‖lpExtend (𝕜 := 𝕜) p f x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((lpExtend (𝕜 := 𝕜) p f).le_opNorm x).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p) f) (norm_nonneg x)))
  · have hh := (lpRestrict (𝕜 := 𝕜) p f).le_opNorm (lpExtend (𝕜 := 𝕜) p f x)
    have heq : lpRestrict (𝕜 := 𝕜) p f (lpExtend (𝕜 := 𝕜) p f x) = x := by
      apply lp.ext
      funext n
      exact lpExtend_apply_image (𝕜 := 𝕜) f x n
    rw [heq] at hh
    exact hh.trans (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p) f)
      (norm_nonneg (lpExtend (𝕜 := 𝕜) p f x))))

theorem lpExtend_single_arbitrary (p : ℝ≥0∞) [Fact (1 ≤ p)] (e : Γ ↪ Γ)
    (γ : Γ) (x : 𝕜) :
    lpExtend (𝕜 := 𝕜) p e (lp.single p γ x) = lp.single p (e γ) x := by
  apply lp.ext
  funext δ
  by_cases hδ : δ ∈ Set.range e
  · obtain ⟨η, rfl⟩ := hδ
    rw [lpExtend_apply_image]
    by_cases hηγ : η = γ
    · subst η; simp
    · have he : e η ≠ e γ := fun h => hηγ (e.injective h)
      simp [hηγ, he]
  · have hδγ : δ ≠ e γ := fun heq => hδ ⟨γ, heq.symm⟩
    simp [lpExtend, Function.extend_apply' _ _ _ hδ, hδγ]

theorem scalarLpSchauderFamily_symmetric (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : (scalarLpSchauderFamily (𝕜 := 𝕜) (Γ := Γ) p hp).HasSymmetricNorm := by
  refine ⟨scalarLpSchauderFamily_oneUnconditional p hp, ?_⟩
  intro σ F a
  change ‖∑ γ ∈ F, a γ • (lp.single p (σ γ) (1 : 𝕜) : lp (fun _ : Γ => 𝕜) p)‖ =
    ‖∑ γ ∈ F, a γ • (lp.single p γ (1 : 𝕜) : lp (fun _ : Γ => 𝕜) p)‖
  have h := scalarLpExtend_norm_arbitrary p σ.toEmbedding
    (∑ γ ∈ F, a γ • (lp.single p γ (1 : 𝕜) : lp (fun _ : Γ => 𝕜) p))
  simpa only [map_sum, map_smul, lpExtend_single_arbitrary, Equiv.toEmbedding_apply] using h

theorem scalarLp_norm_finite_units_arbitrary (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Finset Γ) : ‖∑ γ ∈ F, lp.single p γ (1 : 𝕜)‖ = (F.card : ℝ) ^ p.toReal⁻¹ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  apply (Real.eq_rpow_inv (norm_nonneg _) (Nat.cast_nonneg _) hp0.ne').mpr
  simpa using lp.norm_sum_single (E := fun _ : Γ => 𝕜) hp0 (fun _ => 1) F

theorem scalarLpSchauderFamily_not_equivalentEllOne [Infinite Γ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p) :
    ¬ (scalarLpSchauderFamily (𝕜 := 𝕜) (Γ := Γ) p hp).EquivalentEllOne := by
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  have hinv : p.toReal⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hpr
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (p.toReal⁻¹ - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hinv)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub] using h
  rintro ⟨c, hc, h⟩
  have hle : c ≤ 0 := by
    apply ge_of_tendsto ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    obtain ⟨F, hF⟩ := Finset.exists_card_eq (α := Γ) N
    have hh := h F (fun _ => 1)
    simp only [norm_one, Finset.sum_const, hF, nsmul_eq_mul, mul_one,
      one_smul, scalarLpSchauderFamily] at hh
    rw [scalarLp_norm_finite_units_arbitrary p hp, hF] at hh
    rw [Real.rpow_sub_one hNr.ne']
    exact (le_div_iff₀ hNr).mpr hh
  exact (not_le_of_gt hc) hle

end ThesisCommon
