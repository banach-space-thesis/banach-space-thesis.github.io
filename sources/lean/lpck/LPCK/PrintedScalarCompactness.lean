import LPCK.PrintedCompactBlocks
import LPCK.OrdinalDualCotype
import ThesisCommon.Analysis.RCLikeEllOneSchur

/-! Compactness of operators into finite scalar ℓp. The argument uses
adjoint tests with disjoint coordinate supports, Schur convergence in the
ordinal dual, and the cotype threshold for the p < 2 estimate. -/
noncomputable section
open Filter Set
open scoped ENNReal Topology BigOperators
namespace LPCK.Printed
open ThesisCommon

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

private theorem exists_sublinear_contradiction {a M δ : ℝ} (ha : a < 1) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ M * (N : ℝ)^a < (N : ℝ) * δ := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN, hpos⟩ := ((ht.eventually (eventually_gt_atTop (M / δ))).and
    (eventually_gt_atTop (0 : ℕ))).exists
  have hn : (0 : ℝ) < N := by exact_mod_cast hpos
  refine ⟨N, hpos, ?_⟩
  calc
    _ < ((N : ℝ) ^ (1 - a) * δ) * (N : ℝ) ^ a :=
      mul_lt_mul_of_pos_right ((div_lt_iff₀ hδ).mp hN) (Real.rpow_pos_of_pos hn _)
    _ = ((N : ℝ) ^ (1 - a) * (N : ℝ) ^ a) * δ := by ring
    _ = (N : ℝ) * δ := by rw [← Real.rpow_add hn, sub_add_cancel, Real.rpow_one]

private theorem sum_composed {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {N : ℕ} (T : X →L[𝕜] Z) (f : Fin N → Z →L[𝕜] 𝕜) (c : Fin N → 𝕜) :
    (∑ i, c i • (f i).comp T) = (∑ i, c i • f i).comp T := by
  ext x : 1
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]

/-- Cotype two of the actual dual gives compactness for the complete
printed range 1 ≤ p < 2, including the endpoint p = 1. -/
theorem scalarLp_compact_of_dual_cotype_two {C : ℝ}
    (hc : HasRademacherCotype (X →L[𝕜] 𝕜) 2 C)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p < 2)
    (T : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p) : IsCompactOperator T := by
  by_contra hT
  have hp' : p ≠ ∞ := ne_of_lt (hp.trans (by simp))
  obtain ⟨δ, hδ, f, hf, hsum⟩ := exists_noncompact_adjoint_tests p hp' T hT
  let a := (p.toReal - 1) / p.toReal
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le
    (Fact.out : 1 ≤ p))) hp'
  have hp2 : p.toReal < 2 := by
    exact (ENNReal.toReal_lt_toReal hp' (by norm_num)).2 hp
  have ha : a * 2 < 1 := by
    dsimp [a]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hp0]
    linarith
  obtain ⟨N, hN, hlarge⟩ := exists_sublinear_contradiction ha (M := (C * ‖T‖)^2)
    (δ := δ^2) (by positivity)
  let x (i : Fin N) := (f i.val).comp T
  have hs (θ : Fin N → Bool) : ‖∑ i, if θ i then x i else -x i‖ ≤ (N : ℝ)^a * ‖T‖ := by
    let c (i : Fin N) : 𝕜 := if θ i then 1 else -1
    have he : (∑ i, if θ i then x i else -x i) = ∑ i, c i • x i := by
      apply Finset.sum_congr rfl
      intro i _
      cases hθ : θ i
      · simp only [hθ, Bool.false_eq_true, if_false, c]
        exact (neg_one_smul 𝕜 (x i)).symm
      · simp [c, hθ]
    rw [he, sum_composed T (fun i : Fin N => f i.val) c]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hsum N Fin.valEmbedding c
        (fun i => by dsimp [c]; split_ifs <;> simp)) (norm_nonneg T))
  have hu := hc.sum_rpow_le_of_sign_bound x (by positivity) hs
  simp only [Real.rpow_two] at hu
  have hl : (N : ℝ) * δ^2 ≤ ∑ i, ‖x i‖^2 := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      (sq_le_sq₀ hδ.le (norm_nonneg (x i))).2 (hf i.val))
  have heq : C^2 * ((N : ℝ)^a * ‖T‖)^2 = (C * ‖T‖)^2 * (N : ℝ)^(a*2) := by
    rw [mul_pow, ← Real.rpow_two ((N : ℝ)^a), ← Real.rpow_mul (Nat.cast_nonneg N)]
    ring
  exact (not_lt_of_ge (hl.trans (hu.trans_eq heq))) hlarge

/-- For every finite p, the disjoint adjoint tests tend weakly to zero. -/
theorem scalarLp_compact_of_schur_dual {I : Type*}
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p) : IsCompactOperator T := by
  by_contra hT
  obtain ⟨δ, hδ, f, hf, hsum⟩ := exists_noncompact_adjoint_tests p hp T hT
  let a := (p.toReal - 1) / p.toReal
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le
    (Fact.out : 1 ≤ p))) hp
  have ha : a < 1 := by dsimp [a]; rw [div_lt_iff₀ hp0]; linarith
  let x (n : ℕ) := (f n).comp T
  have hw (φ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
      Tendsto (fun n => φ (x n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    apply tendsto_order.2
    refine ⟨fun b hb => Eventually.of_forall (fun _ => hb.trans_le (norm_nonneg _)), ?_⟩
    intro r hr
    let S : Set ℕ := {n | r ≤ ‖φ (x n)‖}
    have hS : S.Finite := by
      by_contra hS
      obtain ⟨N, hN, hbig⟩ := exists_sublinear_contradiction ha (M := ‖φ‖ * ‖T‖) hr
      let e : Fin N ↪ ℕ := Fin.valEmbedding.trans ((Set.Infinite.natEmbedding S hS).trans
        (Function.Embedding.subtype S))
      choose c hc he using fun i : Fin N => RCLike.exists_norm_eq_mul_self (φ (x (e i)))
      let w := ∑ i, c i • x (e i)
      have hw : w = (∑ i, c i • f (e i)).comp T := sum_composed T _ c
      have hφ : φ w = (↑(∑ i, ‖φ (x (e i))‖) : 𝕜) := by
        simp only [w, map_sum, map_smul, smul_eq_mul, RCLike.ofReal_sum, ← he]
      have hl : (N : ℝ) * r ≤ ‖φ w‖ := by
        rw [hφ, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        have hh (i : Fin N) : r ≤ ‖φ (x (e i))‖ :=
          ((Set.Infinite.natEmbedding S hS) i.val).property
        simpa using (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin N) _ => hh i))
      have hnw : ‖w‖ ≤ (N : ℝ)^a * ‖T‖ := by
        rw [hw]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hsum N e c (fun i => (hc i).le)) (norm_nonneg T))
      have hu := (φ.le_opNorm w).trans (mul_le_mul_of_nonneg_left hnw (norm_nonneg φ))
      have hle := hl.trans hu
      rw [show ‖φ‖ * ((N : ℝ)^a * ‖T‖) = (‖φ‖ * ‖T‖) * (N : ℝ)^a by ring] at hle
      exact (not_lt_of_ge hle) hbig
    obtain ⟨b, hb⟩ := hS.bddAbove
    exact eventually_atTop.2 ⟨b+1, fun n hn => lt_of_not_ge
      (fun hh => (Nat.not_succ_le_self b) (hn.trans (hb hh)))⟩
  have ht := (scalar_schur_of_equiv_ellOne d x hw).norm
  have he : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by simpa using ht
  obtain ⟨n, hn⟩ := (he.eventually_lt_const hδ).exists
  exact (not_lt_of_ge (hf n)) hn

/-- LPCK Proposition 3.6, for every ordinal and every finite exponent
at least one. Both arguments are on the actual bounded dual. -/
theorem proposition_3_6 (α : Ordinal) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : OrdinalContinuous 𝕜 α →L[𝕜] lp (fun _ : ℕ => 𝕜) p) : IsCompactOperator T :=
  scalarLp_compact_of_schur_dual (ordinalContinuousDualEllOneEquiv α) p hp T

end LPCK.Printed
