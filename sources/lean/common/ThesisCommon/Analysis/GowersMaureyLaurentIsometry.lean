import ThesisCommon.Analysis.GowersMaureyToeplitzBlocks
import ThesisCommon.Analysis.GowersMaureyLogScaling

/-! The operator-norm part of the source's Laurent estimate. Finite-band
coefficients are tested on actual separated coordinate sums, and the
finite-support approximation in lp extends the equality to every Wiener
sequence. The strictly singular quotient representation is separate. -/
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wiener_norm_eq_band_sum (M : ℕ) (a : WienerSequences 𝕜)
    (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0) :
    ‖a‖ = ∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖ := by
  classical
  let e : Fin (2*M+1) ↪ ℤ := {
    toFun := fun j => (j.val : ℤ)-M
    inj' := by
      intro i j h
      change (i.val : ℤ)-M = (j.val : ℤ)-M at h
      apply Fin.ext
      omega
  }
  rw [wiener_norm_eq_tsum]
  have hs : ∀ d ∉ Finset.univ.map e, ‖a d‖ = 0 := by
    intro d hd
    by_cases hlo : d < -(M : ℤ)
    · simp only [hband d (Or.inl hlo), norm_zero]
    by_cases hhi : (M : ℤ) < d
    · simp only [hband d (Or.inr hhi), norm_zero]
    have hidx : (d + M).toNat < 2*M+1 := by omega
    exact False.elim (hd (Finset.mem_map.mpr ⟨⟨(d+M).toNat, hidx⟩, Finset.mem_univ _, by
      change (((d+M).toNat : ℤ) - M) = d
      omega⟩))
  rw [tsum_eq_sum hs, Finset.sum_map]
  rfl

theorem norm_laurentOperator_ge_of_band (D : ConstructionData 𝕜) (M : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0) :
    ‖a‖ ≤ ‖laurentOperator D a‖ := by
  have hmono : StrictMono (fun m : ℕ => D.j (2*m+1)) := by
    intro i j hij
    apply D.j_strict
    omega
  have hsize : Tendsto (fun m : ℕ => (D.j (2*m+1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  have hratio := (tendsto_logarithmicWeight_div_scaled
    (c := ((2*M+1 : ℕ) : ℝ)) (by positivity)).comp hsize
  have hlim := hratio.mul_const (∑ j : Fin (2*M+1), ‖a ((j.val : ℤ)-M)‖)
  simp only [one_mul] at hlim
  rw [wiener_norm_eq_band_sum M a hband]
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro m
  have hr : (D.j (2*m+1) : ℝ) ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ)) :=
    ⟨Real.log_le_self (by positivity), le_trans (by linarith) (Real.add_one_le_exp _)⟩
  simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_comm]
    using laurent_band_norm_lower_at_size D M (D.j (2*m+1)) m a hband hr

theorem norm_laurentOperator_eq (D : ConstructionData 𝕜) (a : WienerSequences 𝕜) :
    ‖laurentOperator D a‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · exact ((laurentOperator D).le_opNorm a).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_laurentOperator_le D) (norm_nonneg a))
  · have hclosed : IsClosed {b : WienerSequences 𝕜 | ‖b‖ ≤ ‖laurentOperator D b‖} :=
      isClosed_le continuous_norm (laurentOperator D).continuous.norm
    apply hclosed.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a)
    apply Filter.Eventually.of_forall
    intro s
    let M : ℕ := s.sup Int.natAbs
    apply norm_laurentOperator_ge_of_band D M _
    intro d hd
    have hnot : d ∉ s := by
      intro hdmem
      have hb : d.natAbs ≤ M := Finset.le_sup (f := Int.natAbs) hdmem
      have hlo : -d ≤ ((-d).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at hlo
      have hhi : d ≤ (d.natAbs : ℤ) := Int.le_natAbs
      rcases hd with hd | hd <;> omega
    change (∑ i ∈ s, lp.single 1 i (a i)) d = 0
    simp only [lp.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hid : i ≠ d := by intro he; exact hnot (he ▸ hi)
    simp [lp.single_apply, Ne.symm hid]

/-- Isometric Laurent synthesis on the literal absolutely summable sequences. -/
def laurentOperatorIsometry (D : ConstructionData 𝕜) :
    WienerSequences 𝕜 →ₗᵢ[𝕜] (ShiftSpace D →L[𝕜] ShiftSpace D) := {
  (laurentOperator D).toLinearMap with
  norm_map' := norm_laurentOperator_eq D
}

end ThesisCommon.GowersMaurey
