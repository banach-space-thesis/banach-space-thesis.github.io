import ThesisCommon.Analysis.JamesSchauderBasis
import ThesisCommon.Analysis.JamesDisjointFunctionals

/-! Finite, finitely supported witnesses for failure of shrinking. The
witnesses are obtained by actual normalization, scalar phase alignment and
the proved convergence of initial coordinate projections. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_late_finite_witness
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) {ε : ℝ} (_hε : 0 < ε) (N : ℕ)
    (x : JamesSequenceSpace 𝕜 p) (hxzero : ∀ n ≤ N, x n = 0)
    (hφx : ε * ‖x‖ < ‖φ x‖) :
    ∃ M : ℕ, ∃ z : JamesSequenceSpace 𝕜 p,
      (∀ n ≤ N, z n = 0) ∧ (∀ n, M < n → z n = 0) ∧
        ‖z‖ ≤ 1 ∧ ε < RCLike.re (φ z) := by
  have hx : x ≠ 0 := by intro hz; simp [hz] at hφx
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨a, ha, hphase⟩ := RCLike.exists_norm_eq_mul_self (φ x)
  let y : JamesSequenceSpace 𝕜 p := (‖x‖ : 𝕜)⁻¹ • (a • x)
  have hyn : ‖y‖ = 1 := by
    simp only [y, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hxn, ha,
      one_mul, inv_mul_cancel₀ hxn.ne']
  have hyφ : ε < RCLike.re (φ y) := by
    have heq : φ y = ((‖φ x‖ / ‖x‖ : ℝ) : 𝕜) := by
      dsimp [y]
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hphase]
      push_cast
      ring
    rw [heq, RCLike.ofReal_re]
    exact (lt_div_iff₀ hxn).mpr hφx
  have ht : Tendsto
      (fun M => RCLike.re (φ (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) M y)))
      atTop (𝓝 (RCLike.re (φ y))) :=
    ((RCLike.continuous_re.comp φ.continuous).tendsto y).comp
      (JamesSequenceSpace.initial_tendsto hp y)
  obtain ⟨M, hM⟩ := ((tendsto_order.mp ht).1 ε hyφ).exists
  refine ⟨M, JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) M y, ?_, ?_, ?_, hM⟩
  · intro n hn
    by_cases hm : n ≤ M
    · simp [JamesSequenceSpace.initial_apply, hm, y, hxzero n hn]
    · simp [JamesSequenceSpace.initial_apply, hm]
  · intro n hn
    simp [JamesSequenceSpace.initial_apply, hn.not_ge]
  · exact (JamesSequenceSpace.norm_initialValue_le M y).trans_eq hyn

include hp in
theorem james_finite_disjoint_witnesses
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ x : JamesSequenceSpace 𝕜 p,
      (∀ n ≤ N, x n = 0) ∧ ε * ‖x‖ < ‖φ x‖) :
    ∀ m : ℕ, ∃ x : Fin m → JamesSequenceSpace 𝕜 p,
      (∀ n : ℕ, (Finset.univ.filter (fun i => x i n ≠ 0)).card ≤ 1) ∧
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ i, ε ≤ RCLike.re (φ (x i))) := by
  classical
  have hf (m : ℕ) : ∃ M : ℕ, ∃ x : Fin m → JamesSequenceSpace 𝕜 p,
      (∀ n : ℕ, (Finset.univ.filter (fun i => x i n ≠ 0)).card ≤ 1) ∧
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ i, ε ≤ RCLike.re (φ (x i))) ∧
      (∀ i n, M < n → x i n = 0) := by
    induction m with
    | zero =>
      refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
      · intro n; simp
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
    | succ m ih =>
      obtain ⟨M, x, hdisj, hnorm, hφ, hsupport⟩ := ih
      obtain ⟨y, hyzero, hyφ⟩ := hbad M
      obtain ⟨L, z, hzero, hlate, hznorm, hzφ⟩ :=
        james_late_finite_witness p hp φ hε M y hyzero hyφ
      let w : Fin (m + 1) → JamesSequenceSpace 𝕜 p := Fin.snoc x z
      refine ⟨max M L, w, ?_, ?_, ?_, ?_⟩
      · intro n
        apply Finset.card_le_one.mpr
        intro i hi j hj
        have hi' : w i n ≠ 0 := (Finset.mem_filter.mp hi).2
        have hj' : w j n ≠ 0 := (Finset.mem_filter.mp hj).2
        clear hi hj
        revert hi' hj'
        refine Fin.lastCases ?_ (fun i => ?_) i
        · refine Fin.lastCases (by intros; rfl) (fun j => ?_) j
          intro hi' hj'
          have hi0 : z n ≠ 0 := by simpa [w] using hi'
          have hj0 : x j n ≠ 0 := by simpa [w] using hj'
          by_cases hn : n ≤ M
          · exact False.elim (hi0 (hzero n hn))
          · exact False.elim (hj0 (hsupport j n (Nat.lt_of_not_ge hn)))
        · refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hi' hj'
            have hi0 : x i n ≠ 0 := by simpa [w] using hi'
            have hj0 : z n ≠ 0 := by simpa [w] using hj'
            by_cases hn : n ≤ M
            · exact False.elim (hj0 (hzero n hn))
            · exact False.elim (hi0 (hsupport i n (Nat.lt_of_not_ge hn)))
          · intro hi' hj'
            apply congrArg Fin.castSucc
            apply (Finset.card_le_one.mp (hdisj n))
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [w] using hi'⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [w] using hj'⟩
      · intro i
        exact Fin.lastCases (by simpa [w] using hznorm)
          (fun j => by simpa [w] using hnorm j) i
      · intro i
        exact Fin.lastCases (by simpa [w] using hzφ.le)
          (fun j => by simpa [w] using hφ j) i
      · intro i n hn
        exact Fin.lastCases (by simpa [w] using hlate n ((le_max_right M L).trans_lt hn))
          (fun j => by simpa [w] using hsupport j n ((le_max_left M L).trans_lt hn)) i
  intro m
  obtain ⟨M, x, hd, hn, hφ, _⟩ := hf m
  exact ⟨x, hd, hn, hφ⟩

end ThesisCommon
