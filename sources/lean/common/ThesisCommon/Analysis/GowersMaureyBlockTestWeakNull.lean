import ThesisCommon.Analysis.GowersMaureyRISSubsequence
import ThesisCommon.Analysis.GowersMaureyRISLemmaSeven
import ThesisCommon.Analysis.GowersMaureyOperatorSeminorm

/-! Actual block-test sequences are weakly null. A functional with large
values on a subsequence would, after scalar phase alignment, contradict
the concrete Lemma 7 bound on an RIS subsequence. No shrinking-basis or
operator-representation assumption enters the argument. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem tendsto_functional_small_interval_sequence_zero (D : ConstructionData 𝕜)
    (u : ℕ → C00 𝕜) (hu : ∀ i j, i < j → Before (u i) (u j))
    (hbound : ∀ n, intervalNorm D (n+1) (u n) ≤ 1)
    (φ : ShiftSpace D →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (denseEmbedding D (u n))) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hex : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ‖φ (denseEmbedding D (u n))‖ < ε := by
    by_contra h
    push_neg at h
    obtain ⟨a,ha,hbad⟩ := Nat.exists_strictMono_subsequence
      (P := fun n => ε ≤ ‖φ (denseEmbedding D (u n))‖)
      (fun M => by obtain ⟨n,hn,hv⟩ := h (M+1); exact ⟨n,by omega,hv⟩)
    choose c hc hp using fun i => RCLike.exists_norm_eq_mul_self (φ (denseEmbedding D (u (a i))))
    let v (i : ℕ) := c i • u (a i)
    have hphase (i : ℕ) : φ (denseEmbedding D (v i)) =
        (‖φ (denseEmbedding D (u (a i)))‖ : ℝ) := by
      simp only [v, map_smul, smul_eq_mul]
      exact (hp i).symm
    have hv : ∀ i j, i < j → Before (v i) (v j) := by
      intro i j hij s hs t ht
      exact hu _ _ (ha hij) s (Finsupp.support_smul hs) t (Finsupp.support_smul ht)
    have hvne (i : ℕ) : v i ≠ 0 := by
      intro hz
      have he := hphase i
      rw [hz, map_zero, map_zero] at he
      have hn : ‖φ (denseEmbedding D (u (a i)))‖ = 0 := by
        exact RCLike.ofReal_injective (by simpa only [RCLike.ofReal_zero] using he.symm)
      have := hbad i
      linarith
    have hq : StrictMono (fun i => a i+1) := fun i j hij => Nat.add_lt_add_right (ha hij) 1
    have hvbound (i : ℕ) : intervalNorm D (a i+1) (v i) ≤ 1 := by
      simpa only [v, map_smul_eq_mul, hc, one_mul] using hbound (a i)
    have hodd : StrictMono (fun m : ℕ => 2*m+1) := by intro i j hij; dsimp only; omega
    have hseq : Tendsto (fun m : ℕ => (D.j (2*m+1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (D.j_strict.tendsto_atTop.comp hodd.tendsto_atTop)
    obtain ⟨m,hm⟩ := ((tendsto_logarithmicWeight_atTop.comp hseq).eventually
      (eventually_gt_atTop (4*‖φ‖/ε))).exists
    let N := D.j (2*m+1)
    change 4*‖φ‖/ε < logarithmicWeight N at hm
    have hNp : (0 : ℝ) < N := by exact_mod_cast D.j_positive (2*m+1)
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast D.j_positive (2*m+1)
    have hfp : 0 < logarithmicWeight N := zero_lt_one.trans_le (one_le_logarithmicWeight_real hN1)
    have hgap : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
        (Real.exp (D.j (2*m+1) : ℝ)) :=
      ⟨Real.log_le_self hNp.le,
        (show (N : ℝ) ≤ (N : ℝ)+1 by linarith).trans (Real.add_one_le_exp _)⟩
    obtain ⟨b,hb,hr⟩ := exists_RIS_subsequence D v (fun i => a i+1) hv hvne hq hvbound N
      (ε := 1) (by norm_num) (le_refl 1)
    obtain ⟨hr⟩ := hr
    let w := ∑ i : Fin N, v (b i)
    have hlow : (N : ℝ)*ε ≤ ∑ i : Fin N, ‖φ (denseEmbedding D (u (a (b i))))‖ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin N) _ => hbad (b i))
    have he : φ (denseEmbedding D w) =
        ((∑ i : Fin N, ‖φ (denseEmbedding D (u (a (b i))))‖ : ℝ) : 𝕜) := by
      simp only [w, map_sum, hphase]
    have hphi : (N : ℝ)*ε ≤ ‖φ‖ * implicitNorm D w := by
      apply hlow.trans
      calc
        _ = ‖φ (denseEmbedding D w)‖ := by
          rw [he, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
        _ ≤ ‖φ‖ * ‖denseEmbedding D w‖ := φ.le_opNorm _
        _ = _ := by rw [denseEmbedding_norm]; rfl
    have hnorm := hr.normalized_norm_le_lemma7 m hgap
    change implicitNorm D ((logarithmicWeight N / N) • w) ≤ 1+3*(1:ℝ) at hnorm
    rw [seminorm_real_smul, abs_of_nonneg (div_nonneg hfp.le hNp.le)] at hnorm
    have hn : implicitNorm D w * logarithmicWeight N ≤ 4*N := by
      have heq : logarithmicWeight N / N * implicitNorm D w =
          (implicitNorm D w * logarithmicWeight N) / N := by ring
      rw [heq] at hnorm
      exact (div_le_iff₀ hNp).mp (by norm_num at hnorm ⊢; exact hnorm)
    have hmul := (mul_le_mul_of_nonneg_right hphi hfp.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (norm_nonneg φ))
    have hcancel : ε * logarithmicWeight N ≤ 4*‖φ‖ := by
      apply (mul_le_mul_iff_right₀ hNp).mp
      nlinarith only [hmul]
    have hstrict : 4*‖φ‖ < ε * logarithmicWeight N := by
      have hv := (div_lt_iff₀ hε).mp hm
      simpa only [mul_comm] using hv
    exact (not_lt_of_ge hcancel) hstrict
  simpa only [dist_zero_right] using hex

theorem BlockTestSequence.tendsto_functional_zero {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (φ : ShiftSpace D →L[𝕜] 𝕜) :
    Tendsto (fun n => φ (denseEmbedding D (u.vector n))) atTop (𝓝 0) :=
  tendsto_functional_small_interval_sequence_zero D u.vector u.successive u.norm_bound φ

end ThesisCommon.GowersMaurey
