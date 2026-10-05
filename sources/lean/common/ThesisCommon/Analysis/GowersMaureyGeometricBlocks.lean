import ThesisCommon.Analysis.GowersMaureyCoordinateLowerBounds
import ThesisCommon.Analysis.GowersMaureyLogGrowth
import ThesisCommon.Analysis.GowersMaureyBlockTails

/-! Actual long geometric blocks in the constructed finite-sequence norm.
They provide unit approximate shift eigenvectors after every finite cutoff.
Only the proved logarithmic lower estimate and concrete shift formula enter. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def geometricBlock (z : 𝕜) (N B : ℕ) : C00 𝕜 :=
  ∑ i ∈ Finset.range N, Finsupp.single (B+i) (z^i)

@[simp] theorem geometricBlock_zero (z : 𝕜) (B : ℕ) : geometricBlock z 0 B = 0 := by
  simp [geometricBlock]

theorem geometricBlock_succ (z : 𝕜) (N B : ℕ) :
    geometricBlock z (N+1) B = geometricBlock z N B + Finsupp.single (B+N) (z^N) := by
  simp only [geometricBlock, Finset.sum_range_succ]

theorem geometricBlock_coordinate (z : 𝕜) (N B : ℕ) {i : ℕ} (hi : i < N) :
    geometricBlock z N B (B+i) = z^i := by
  classical
  rw [geometricBlock, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact Finsupp.single_eq_of_ne (by omega)
  · simp [hi]

theorem geometricBlock_support {z : 𝕜} {N B k : ℕ}
    (hk : k ∈ (geometricBlock z N B).support) : B ≤ k ∧ k < B+N := by
  classical
  obtain ⟨i,hi,hki⟩ := Finsupp.mem_support_finset_sum k hk
  have hiN : i < N := Finset.mem_range.mp hi
  have he : k = B+i := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hki (Finsupp.single_eq_of_ne h)
  omega

theorem geometricBlock_shift_identity (z : 𝕜) (N B : ℕ) :
    z • spread 0 1 (geometricBlock z N B)-geometricBlock z N B =
      Finsupp.single (B+N) (z^N)-Finsupp.single B 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [geometricBlock_succ, map_add, smul_add]
    rw [spread_single]
    simp only [Nat.zero_le, if_true, Nat.sub_zero]
    rw [Finsupp.smul_single, smul_eq_mul, ← pow_succ']
    have he : B+N+1 = B+(N+1) := by omega
    rw [he]
    calc
      _ = (z • spread 0 1 (geometricBlock z N B)-geometricBlock z N B) +
          Finsupp.single (B+(N+1)) (z^(N+1))-Finsupp.single (B+N) (z^N) := by abel
      _ = _ := by rw [ih]; abel

theorem geometricBlock_shift_error_le (D : ConstructionData 𝕜)
    {z : 𝕜} (hz : ‖z‖ = 1) (N B : ℕ) :
    implicitNorm D (spread 0 1 (geometricBlock z N B)-z⁻¹ • geometricBlock z N B) ≤ 2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have he : spread 0 1 (geometricBlock z N B)-z⁻¹ • geometricBlock z N B =
      z⁻¹ • (z • spread 0 1 (geometricBlock z N B)-geometricBlock z N B) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  rw [he, map_smul_eq_mul, norm_inv, hz, inv_one, one_mul,
    geometricBlock_shift_identity]
  calc
    _ ≤ implicitNorm D (Finsupp.single (B+N) (z^N)) +
        implicitNorm D (Finsupp.single B 1) := map_sub_le_add _ _ _
    _ = 2 := by norm_num [implicitNorm_single, norm_pow, hz]

theorem geometricBlock_norm_lower (D : ConstructionData 𝕜)
    {z : 𝕜} (hz : ‖z‖ = 1) (N B : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ≤ logarithmicWeight N * implicitNorm D (geometricBlock z N B) := by
  have hh := coordinate_sum_norm_le_weight D hN
    (show StrictMono (fun i : Fin N => B+i.val) from fun _ _ h => Nat.add_lt_add_left h B)
    (geometricBlock z N B)
  have hcoord : ∀ i : Fin N, geometricBlock z N B (B+i.val) = z^i.val :=
    fun i => geometricBlock_coordinate z N B i.isLt
  simpa only [hcoord, norm_pow, hz, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hh

theorem exists_unit_tail_shift_approximate_eigenvector (D : ConstructionData 𝕜)
    {z : 𝕜} (hz : ‖z‖ = 1) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : C00 𝕜, x ∈ afterCutoff B ∧ implicitNorm D x = 1 ∧
      implicitNorm D (spread 0 1 x-z⁻¹ • x) < ε := by
  obtain ⟨N₀,hN₀⟩ := logarithmicWeight_nat_subpower (q := 1) (by norm_num)
    (show 0 < ε/2 by positivity)
  let N := max N₀ 2
  have hN : 2 ≤ N := le_max_right _ _
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : logarithmicWeight N < (ε/2)*(N : ℝ) := by
    simpa only [Real.rpow_one] using hN₀ N (le_max_left _ _)
  let u := geometricBlock z N (B+1)
  have hl := geometricBlock_norm_lower D hz N (B+1) hN
  have hn : 0 < implicitNorm D u := by
    by_contra h
    have hzero : implicitNorm D u = 0 := le_antisymm (not_lt.mp h) (apply_nonneg _ _)
    change (N : ℝ) ≤ logarithmicWeight N * implicitNorm D u at hl
    rw [hzero, mul_zero] at hl
    exact hNp.not_ge hl
  let r : ℝ := (implicitNorm D u)⁻¹
  have hr : 0 < r := inv_pos.mpr hn
  refine ⟨(r : 𝕜) • u, ?_, ?_, ?_⟩
  · intro k hk
    have hu : u k = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      have hh := geometricBlock_support hmem
      omega
    simp [hu]
  · rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hr]
    exact inv_mul_cancel₀ hn.ne'
  · have he : spread 0 1 ((r : 𝕜) • u)-z⁻¹ • ((r : 𝕜) • u) =
        (r : 𝕜) • (spread 0 1 u-z⁻¹ • u) := by
      rw [map_smul, smul_sub, smul_comm z⁻¹]
    rw [he, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hr]
    have hu := geometricBlock_shift_error_le D hz N (B+1)
    have hb : 2 < ε * implicitNorm D u := by
      change (N : ℝ) ≤ logarithmicWeight N * implicitNorm D u at hl
      have hm := mul_lt_mul_of_pos_right hf hn
      nlinarith
    calc
      _ ≤ r * 2 := mul_le_mul_of_nonneg_left hu hr.le
      _ < ε := by
        dsimp only [r]
        rw [inv_mul_eq_div, div_lt_iff₀ hn]
        exact hb

end ThesisCommon.GowersMaurey
