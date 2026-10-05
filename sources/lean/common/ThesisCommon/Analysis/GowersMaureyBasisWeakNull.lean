import ThesisCommon.Analysis.GowersMaureyWeightedCoordinates

/-! The genuine coordinate basis is weakly null. The proof aligns scalar
phases and contradicts the sharp weighted coordinate-sum estimate at the
actual odd construction sizes. No shrinking-basis hypothesis is used. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem tendsto_functional_basisVector_zero (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) :
    Tendsto (fun n : ℕ => φ (basisVector D n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hex : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ‖φ (basisVector D n)‖ < ε := by
    by_contra h
    push_neg at h
    obtain ⟨a,ha,hbad⟩ := Nat.exists_strictMono_subsequence (P := fun n => ε ≤ ‖φ (basisVector D n)‖)
      (fun M => by obtain ⟨n,hn,hv⟩ := h (M+1); exact ⟨n,by omega,hv⟩)
    have hodd : StrictMono (fun m : ℕ => 2*m+1) := by
      intro i j hij
      dsimp only
      omega
    have hseq : Tendsto (fun m : ℕ => (D.j (2*m+1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (D.j_strict.tendsto_atTop.comp hodd.tendsto_atTop)
    obtain ⟨m,hm⟩ := ((tendsto_logarithmicWeight_atTop.comp hseq).eventually
      (eventually_gt_atTop (‖φ‖/ε))).exists
    let N := D.j (2*m+1)
    change ‖φ‖/ε < logarithmicWeight N at hm
    have hNpos : (0 : ℝ) < N := by exact_mod_cast D.j_positive (2*m+1)
    have hN1 : 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (D.j_positive (2*m+1))
    have hfpos : 0 < logarithmicWeight N :=
      zero_lt_one.trans_le (one_le_logarithmicWeight_real hN1)
    have hgap : (N : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
        (Real.exp (D.j (2*m+1) : ℝ)) := by
      exact ⟨Real.log_le_self hNpos.le,
        (show (N : ℝ) ≤ (N : ℝ)+1 by linarith).trans (Real.add_one_le_exp _)⟩
    have haN : StrictMono (fun i : Fin N => a i.val) := fun i j hij => ha hij
    have hlow : (N : ℝ)*ε ≤ ∑ i : Fin N, ‖φ (basisVector D (a i.val))‖ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin N) _ => hbad i.val)
    have hup := functional_basisVector_sum_norm_le D φ haN m hgap
    have hh := hlow.trans hup
    rw [← mul_div_assoc] at hh
    have hh' := (le_div_iff₀ hfpos).mp hh
    have hcancel : ε * logarithmicWeight N ≤ ‖φ‖ := by
      apply (mul_le_mul_iff_right₀ hNpos).mp
      nlinarith only [hh']
    have hstrict : ‖φ‖ < ε * logarithmicWeight N := by
      have hv := (div_lt_iff₀ hε).mp hm
      simpa only [mul_comm] using hv
    exact (not_lt_of_ge hcancel) hstrict
  simpa only [dist_zero_right] using hex

end ThesisCommon.GowersMaurey
