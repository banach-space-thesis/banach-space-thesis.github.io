import PL1.DaugavetCriterion
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Finite averages of spikes imply the Daugavet slice criterion

All functionals are tested by finite averages. The only geometric input is
the explicitly stated finite-family hypothesis on a dense increasing union
of linear subspaces.
-/

noncomputable section
open scoped BigOperators NNReal
namespace PL1.Daugavet

variable (K E : Type*) [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]

/-- The quantitative finite spike family used in the manuscript. -/
def FiniteSpikeFamilies (V : ℕ → Submodule K E) : Prop :=
  ∀ n (h : E), h ∈ V n → ∀ f : E, f ∈ V n →
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, 0 < N ∧ ∃ w : Fin N → E,
        (N : K)⁻¹ • (∑ a, w a) = f ∧
        (∀ a, ‖w a‖ ≤ (1 + η) * ‖f‖) ∧
        (∀ a, (1 - 2 * δ) * (‖h‖ + ‖f‖) - η * ‖f‖ ≤ ‖h + w a‖)

variable {K E}

theorem exists_unit_re_apply_gt (φ : E →L[K] K) (hφ : ‖φ‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ x : E, ‖x‖ = 1 ∧ 1 - δ < RCLike.re (φ x) := by
  obtain ⟨x, hx, hfx⟩ := φ.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm
    (r := ⟨1 - δ, by linarith⟩) (by change 1 - δ < ‖φ‖; rw [hφ]; linarith)
  have hx' : ‖x‖ = 1 := congrArg (fun r : ℝ≥0 => (r : ℝ)) hx
  have hfx' : 1 - δ < ‖φ x‖ := hfx
  have hfx0 : φ x ≠ 0 := by
    intro he
    simp only [he, norm_zero] at hfx'
    linarith
  let c : K := (‖φ x‖ : K) / φ x
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, RCLike.norm_ofReal, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hfx0)
  refine ⟨c • x, by rw [norm_smul, hc, hx', mul_one], ?_⟩
  simpa only [map_smul, smul_eq_mul, c, div_mul_cancel₀ _ hfx0, RCLike.ofReal_re] using hfx'

theorem exists_unit_mem_dense_union (V : ℕ → Submodule K E)
    (hV : Dense (⋃ n, (V n : Set E))) (x : E) (hx : ‖x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ y : E, y ∈ V n ∧ ‖y‖ = 1 ∧ ‖x - y‖ < ε := by
  obtain ⟨v, hv, hxv⟩ := hV.exists_dist_lt x (lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2))
  obtain ⟨n, hvn⟩ := Set.mem_iUnion.mp hv
  rw [dist_eq_norm] at hxv
  have hv0 : v ≠ 0 := by
    intro he
    simp only [he, sub_zero, hx] at hxv
    linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
  have hvn0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  let y : E := ((‖v‖⁻¹ : ℝ) : K) • v
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, inv_mul_cancel₀ hvn0]
  have hyv : (‖v‖ : K) • y = v := by
    dsimp only [y]
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hvn0, RCLike.ofReal_one, one_smul]
  have hdiff : v - y = ((‖v‖ - 1 : ℝ) : K) • y := by
    rw [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, hyv, one_smul]
  have hnear : ‖v - y‖ ≤ ‖x - v‖ := by
    rw [hdiff, norm_smul, RCLike.norm_ofReal, hy, mul_one]
    simpa only [hx, norm_sub_rev] using abs_norm_sub_norm_le v x
  refine ⟨n, y, (V n).smul_mem _ hvn, hy, ?_⟩
  have ht := norm_add_le (x - v) (v - y)
  rw [sub_add_sub_cancel] at ht
  linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]

theorem exists_re_gt_of_finite_average (φ : E →L[K] K) {N : ℕ} (hN : 0 < N)
    (w : Fin N → E) (f : E) (hav : (N : K)⁻¹ • (∑ a, w a) = f)
    {b : ℝ} (hb : b < RCLike.re (φ f)) :
    ∃ a, b < RCLike.re (φ (w a)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : K)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : K) := by simp
  have he := congrArg (fun x => RCLike.re (φ x)) hav
  simp only [map_smul, smul_eq_mul, hc, RCLike.mul_re, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero, map_sum] at he
  by_contra! ha
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => ha a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNr.le)
  rw [← mul_assoc, inv_mul_cancel₀ hNr.ne', one_mul, he] at hm
  linarith

/-- The finite-average construction on a dense increasing union implies
the geometric slice criterion for every continuous dual functional. -/
theorem sliceCriterion_of_finiteSpikeFamilies (V : ℕ → Submodule K E)
    (hmono : Monotone V) (hdense : Dense (⋃ n, (V n : Set E)))
    (hspikes : FiniteSpikeFamilies K E V) : SliceCriterion K E := by
  classical
  intro h hh φ hφ ε hε
  let e : ℝ := min ε 1
  have he : 0 < e := lt_min hε zero_lt_one
  have heε : e ≤ ε := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  let d : ℝ := e / 64
  have hd : 0 < d := div_pos he (by norm_num)
  have hd1 : d < 1 := by dsimp [d]; linarith
  obtain ⟨g, hg, hφg⟩ := exists_unit_re_apply_gt φ hφ hd hd1
  obtain ⟨nf, f, hfV, hf, hgf⟩ := exists_unit_mem_dense_union V hdense g hg hd
  have hφf : 1 - 2 * d < RCLike.re (φ f) := by
    have hn := (RCLike.re_le_norm (φ (g - f))).trans (φ.le_opNorm (g - f))
    rw [map_sub, map_sub, hφ, one_mul] at hn
    linarith
  obtain ⟨nh, h₀, hhV, hh₀, hhh⟩ := exists_unit_mem_dense_union V hdense h hh hd
  obtain ⟨N, hN, w, hav, hw, hsep⟩ := hspikes (max nh nf) h₀
    (hmono (le_max_left _ _) hhV) f (hmono (le_max_right _ _) hfV) d hd d hd
  obtain ⟨a, ha⟩ := exists_re_gt_of_finite_average φ hN w f hav hφf
  let x : E := (((1 + d)⁻¹ : ℝ) : K) • w a
  have h1d : 0 < 1 + d := by linarith
  have hx : ‖x‖ ≤ 1 := by
    have hw' := hw a
    rw [hf, mul_one] at hw'
    dsimp [x]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr h1d)]
    exact (mul_le_mul_of_nonneg_left hw' (inv_nonneg.mpr h1d.le)).trans_eq
      (inv_mul_cancel₀ h1d.ne')
  have hscale : ((1 + d : ℝ) : K) • x = w a := by
    dsimp only [x]
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ h1d.ne', RCLike.ofReal_one, one_smul]
  have hdiff : w a - x = (d : K) • x := by
    rw [← hscale, RCLike.ofReal_add, RCLike.ofReal_one, add_smul, one_smul]
    abel
  have hdiffnorm : ‖w a - x‖ ≤ d := by
    rw [hdiff, norm_smul, RCLike.norm_ofReal, abs_of_pos hd]
    exact mul_le_of_le_one_right hd.le hx
  have hφx : (1 + d) * RCLike.re (φ x) = RCLike.re (φ (w a)) := by
    have hs := congrArg (fun v => RCLike.re (φ v)) hscale
    simpa only [map_smul, smul_eq_mul, RCLike.mul_re, RCLike.ofReal_re,
      RCLike.ofReal_im, zero_mul, sub_zero] using hs
  refine ⟨x, hx, ?_, ?_⟩
  · have hreal : 1 - ε < (1 - 2 * d) / (1 + d) := by
      apply (lt_div_iff₀ h1d).mpr
      have heq : e = 64 * d := by dsimp [d]; ring
      nlinarith [mul_nonneg hε.le hd.le]
    exact hreal.trans ((div_lt_iff₀ h1d).mpr (by nlinarith [ha]))
  · have hs := hsep a
    rw [hh₀, hf] at hs
    have htri := norm_sub_norm_le (h₀ + w a) (h + x)
    have hid : (h₀ + w a) - (h + x) = (h₀ - h) + (w a - x) := by abel
    rw [hid] at htri
    have hu := norm_add_le (h₀ - h) (w a - x)
    rw [norm_sub_rev h₀ h] at hu
    have heq : e = 64 * d := by dsimp [d]; ring
    nlinarith

end PL1.Daugavet
