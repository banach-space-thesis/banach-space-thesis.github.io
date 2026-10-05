import ThesisCommon.Analysis.GowersMaureyCodePrefixes
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.Order.Field

/-! Explicit distinct positive rational contractions approaching one.
They preserve the Gaussian-rational coordinate condition, unit coordinate
bounds and supports, and approximate in every fixed seminorm. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def codingContraction (n : ℕ) : ℚ := 1 - 1 / ((n : ℚ) + 2)

theorem codingContraction_pos (n : ℕ) : 0 < codingContraction n := by
  have hn : (0 : ℚ) ≤ n := by positivity
  have h : (1 : ℚ) / (n+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  dsimp only [codingContraction]
  linarith

theorem codingContraction_lt_one (n : ℕ) : codingContraction n < 1 := by
  have h : (0 : ℚ) < 1 / (n+2) := by positivity
  dsimp only [codingContraction]
  linarith

theorem codingContraction_injective : Function.Injective codingContraction := by
  intro m n h
  have hi : ((m : ℚ)+2)⁻¹ = ((n : ℚ)+2)⁻¹ := by
    dsimp only [codingContraction] at h
    simpa only [one_div] using (sub_right_inj.mp h)
  have he := inv_injective hi
  exact_mod_cast (add_right_cancel he)

theorem tendsto_codingContraction_real :
    Tendsto (fun n : ℕ => (codingContraction n : ℝ)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hden)
  simpa [codingContraction, one_div] using h

theorem tendsto_codingContraction_scalar :
    Tendsto (fun n : ℕ => (codingContraction n : 𝕜)) atTop (𝓝 1) := by
  have h := ((RCLike.continuous_ofReal : Continuous (fun r : ℝ => (r : 𝕜))).tendsto (1 : ℝ)).comp
    tendsto_codingContraction_real
  simpa only [Function.comp_def, RCLike.ofReal_ratCast, RCLike.ofReal_one] using h

theorem RationalUnitSequence.rat_smul {a : C00 𝕜} (ha : RationalUnitSequence a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : RationalUnitSequence ((q : 𝕜) • a) := by
  constructor
  · intro i
    obtain ⟨r,s,he⟩ := ha.1 i
    refine ⟨q*r,q*s,?_⟩
    simp only [Finsupp.smul_apply, smul_eq_mul, he, Rat.cast_mul]
    ring
  · intro i
    have hnorm : ‖(q : 𝕜)‖ ≤ 1 := by
      rw [← RCLike.ofReal_ratCast, RCLike.norm_ofReal,
        abs_of_nonneg (by exact_mod_cast hq0 : (0 : ℝ) ≤ q)]
      exact_mod_cast hq1
    simp only [Finsupp.smul_apply, norm_smul]
    exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans
      (by simpa only [one_mul] using ha.2 i)

theorem support_rat_smul_of_pos (a : C00 𝕜) {q : ℚ} (hq : 0 < q) :
    ((q : 𝕜) • a).support = a.support := by
  have hq0 : (q : 𝕜) ≠ 0 := by exact_mod_cast hq.ne'
  ext i
  simp [Finsupp.mem_support_iff, hq0]

theorem codingDomain_append_rat_smul {xs : List (C00 𝕜)} (hxs : CodingDomain xs)
    {a : C00 𝕜} (ha : RationalUnitSequence a) (hbefore : ∀ b ∈ xs, Before b a)
    {q : ℚ} (hq0 : 0 < q) (hq1 : q ≤ 1) : CodingDomain (xs ++ [(q : 𝕜) • a]) := by
  constructor
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hxs.1 b hb
    · have he := List.mem_singleton.mp hb
      subst b
      exact ha.rat_smul hq0.le hq1
  · apply List.pairwise_append.mpr
    refine ⟨hxs.2, by simp, ?_⟩
    intro b hb c hc
    have he := List.mem_singleton.mp hc
    subst c
    intro i hi j hj
    rw [support_rat_smul_of_pos a hq0] at hj
    exact hbefore b hb i hi j hj

theorem tendsto_codingContraction_seminorm_error (p : Seminorm 𝕜 (C00 𝕜)) (a : C00 𝕜) :
    Tendsto (fun n : ℕ => p ((codingContraction n : 𝕜) • a - a)) atTop (𝓝 0) := by
  have h := ((tendsto_codingContraction_scalar (𝕜 := 𝕜)).sub_const 1).norm.mul_const (p a)
  have he (n : ℕ) : (codingContraction n : 𝕜) • a - a =
      ((codingContraction n : 𝕜)-1) • a := by rw [sub_smul, one_smul]
  simpa only [he, map_smul_eq_mul, sub_self, norm_zero, zero_mul] using h

end ThesisCommon.GowersMaurey
