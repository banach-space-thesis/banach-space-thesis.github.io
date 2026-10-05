import ThesisCommon.Analysis.GowersMaureyLaurentTailTests
import ThesisCommon.Analysis.GowersMaureySeminormTailTests
import ThesisCommon.Analysis.GowersMaureyLogScaling
import Mathlib.Analysis.SpecificLimits.Basic

/-! The source's full Laurent equality: the actual block-sequence
seminorm and operator norm both equal the absolutely summable coefficient
norm. Finite-band tail tests prove the lower bound; continuity extends it
to all Wiener sequences. No assertion that every operator is Laurent
modulo a small operator is used here. -/
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wiener_norm_div_le_spaceOperatorSeminorm_of_band
    (D : ConstructionData 𝕜) (M : ℕ) (a : WienerSequences 𝕜)
    (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖a‖ / (1+δ) ≤ spaceOperatorSeminorm D (laurentOperator D a) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  apply le_spaceOperatorSeminorm_of_tail_tests D (laurentOperator D a) b
  intro n hn B
  let r : ℕ → ℕ := fun m => n * D.j (2*m+1)
  have hrmono : StrictMono r := by
    intro i j hij
    apply Nat.mul_lt_mul_of_pos_left _ hn
    exact D.j_strict (by omega)
  have hrsize : Tendsto (fun m => (r m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrmono.tendsto_atTop
  have hratio := (tendsto_logarithmicWeight_div_scaled
    (c := ((2*M+1 : ℕ) : ℝ)) (by positivity)).comp hrsize
  have hlim := (hratio.mul_const ‖a‖).div_const (1+δ)
  simp only [one_mul] at hlim
  have hlt := hlim.eventually_const_lt hb
  have hf := hrsize.eventually (eventually_logarithmicWeight_le_one_add_mul_div hδ hn)
  have hr2 := hrmono.tendsto_atTop.eventually (eventually_ge_atTop 2)
  obtain ⟨m, hm2, hmf, hmb⟩ := (hr2.and (hf.and hlt)).exists
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hquot : (r m : ℝ) / n = (D.j (2*m+1) : ℝ) := by
    dsimp only [r]
    rw [Nat.cast_mul]
    field_simp
  have hgap : (r m : ℝ)/n ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ)) := by
    rw [hquot]
    exact ⟨Real.log_le_self (by positivity),
      (by linarith [Real.add_one_le_exp (D.j (2*m+1) : ℝ)])⟩
  refine ⟨normalizedToeplitzTailVector 𝕜 M (r m) B δ,
    normalizedToeplitzTailVector_mem_afterCutoff M (r m) B δ,
    normalizedToeplitzTailVector_intervalNorm_le D M (r m) B m n hδ.le hgap hmf, ?_⟩
  apply le_trans _ (normalizedToeplitzTailVector_image_norm_lower D M (r m) B a hband hm2 hδ.le)
  simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    mul_comm] using hmb.le

theorem wiener_norm_le_spaceOperatorSeminorm_of_band
    (D : ConstructionData 𝕜) (M : ℕ) (a : WienerSequences 𝕜)
    (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0) :
    ‖a‖ ≤ spaceOperatorSeminorm D (laurentOperator D a) := by
  have hlim := (tendsto_const_nhds (x := ‖a‖)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat)
    (by norm_num : (1 : ℝ)+0 ≠ 0)
  have hh : Tendsto (fun n : ℕ => ‖a‖ / (1 + 1/((n : ℝ)+1))) atTop (𝓝 ‖a‖) := by
    simpa only [add_zero, div_one] using hlim
  apply le_of_tendsto hh
  exact Eventually.of_forall (fun n => wiener_norm_div_le_spaceOperatorSeminorm_of_band
    D M a hband (δ := 1/((n : ℝ)+1)) (by positivity))

theorem spaceOperatorSeminorm_laurentOperator (D : ConstructionData 𝕜)
    (a : WienerSequences 𝕜) : spaceOperatorSeminorm D (laurentOperator D a) = ‖a‖ := by
  classical
  apply le_antisymm
  · exact (spaceOperatorSeminorm_le_norm D _).trans_eq (norm_laurentOperator_eq D a)
  · have hclosed : IsClosed {b : WienerSequences 𝕜 |
        ‖b‖ ≤ spaceOperatorSeminorm D (laurentOperator D b)} :=
      isClosed_le continuous_norm ((spaceOperatorSeminorm_continuous D).comp (laurentOperator D).continuous)
    apply hclosed.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a)
    apply Eventually.of_forall
    intro s
    let M : ℕ := s.sup Int.natAbs
    apply wiener_norm_le_spaceOperatorSeminorm_of_band D M _
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

theorem norm_laurentOperator_eq_spaceOperatorSeminorm (D : ConstructionData 𝕜)
    (a : WienerSequences 𝕜) : ‖laurentOperator D a‖ = spaceOperatorSeminorm D (laurentOperator D a) := by
  rw [norm_laurentOperator_eq, spaceOperatorSeminorm_laurentOperator]

end ThesisCommon.GowersMaurey
