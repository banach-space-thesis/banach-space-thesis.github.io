import ThesisCommon.Analysis.MatrixBlockAveraging
import ThesisCommon.Analysis.MatrixBlockDecay
import ThesisCommon.Analysis.MatrixSumOperators
import ThesisCommon.Analysis.FiniteDimensionalUnitBallNets

/-! Uniformly small canonical k-by-k blocks on every prescribed
d-dimensional subspace of the actual finite ℓp operator space. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem exists_matrixBlock_small_on_subspace_of_comparisons (p : BanachExponent)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hupper : ∀ N : ℕ, 0 < N → ∀ A : FiniteMatrixBlock 𝕜 p N,
      matrixHilbertSchmidtNorm p A ≤ (N : ℝ) ^ (1 / 2 + a) * ‖A‖)
    (hlower : ∀ N : ℕ, 0 < N → ∀ A : FiniteMatrixBlock 𝕜 p N,
      ‖A‖ ≤ (N : ℝ) ^ a * matrixHilbertSchmidtNorm p A)
    (k d : ℕ) (hk : 0 < k) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ E : Submodule 𝕜 (FiniteMatrixBlock 𝕜 p N), Module.finrank 𝕜 E = d →
        ∃ α τ : Fin k ↪o Fin N, ∀ x : E,
          ‖matrixBlockProjection p α.toEmbedding τ.toEmbedding (x : FiniteMatrixBlock 𝕜 p N)‖ ≤ ε * ‖x‖ := by
  classical
  let L := finiteDimensionalNetBound d (ε / 2)
  let δ : ℝ := ε / (2 * (k : ℝ) ^ a)
  have hkpow : 0 < (k : ℝ) ^ a := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hkpow)
  obtain ⟨N₀, hN₀, hbudget⟩ := exists_matrixBlock_budget k L hk (1 + 2 * a)
    (by linarith) (by linarith) hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN E hdim
  letI : NormedSpace 𝕜 E := Submodule.normedSpace E
  letI : FiniteDimensional 𝕜 E := FiniteDimensional.of_finrank_pos (by rw [hdim]; exact hd)
  have hNpos : 0 < N := hN₀.trans_le hN
  obtain ⟨S, hSnorm, hScard, hScover⟩ := exists_unitBall_net_card_le 𝕜 E (half_pos hε)
  rw [hdim] at hScard
  let u : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let xs (r : Fin S.card) : FiniteMatrixBlock 𝕜 p N := (u r).val.val
  have hxs (r : Fin S.card) : ‖xs r‖ ≤ 1 := hSnorm (u r).val (u r).property
  have henergy (r : Fin S.card) : matrixHilbertSchmidtNorm p (xs r) ^ 2 ≤ (N : ℝ) ^ (1 + 2 * a) := by
    have hnorm : matrixHilbertSchmidtNorm p (xs r) ≤ (N : ℝ) ^ (1 / 2 + a) :=
      (hupper N hNpos (xs r)).trans
        (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hxs r)
            (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 + a)))
    calc
      _ ≤ ((N : ℝ) ^ (1 / 2 + a)) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr hnorm
      _ = _ := by rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]; congr 1; ring
  obtain ⟨hm, hb⟩ := hbudget N hN
  let e := consecutiveMatrixEmbedding (Nat.div_mul_le_self N k)
  have htotal : (∑ r : Fin S.card, matrixHilbertSchmidtNorm p (xs r) ^ 2) ≤
      ((N / k : ℕ) : ℝ) ^ 2 * δ ^ 2 := by
    calc
      _ ≤ ∑ _r : Fin S.card, (N : ℝ) ^ (1 + 2 * a) := Finset.sum_le_sum (fun r _ => henergy r)
      _ = (S.card : ℝ) * (N : ℝ) ^ (1 + 2 * a) := by simp
      _ ≤ (L : ℝ) * (N : ℝ) ^ (1 + 2 * a) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ ≤ _ := hb
  obtain ⟨s, t, hst⟩ := exists_small_matrixBlock_finite_family p hm e xs hδ.le htotal
  let α := consecutiveMatrixBlock (Nat.div_mul_le_self N k) s
  let τ := consecutiveMatrixBlock (Nat.div_mul_le_self N k) t
  let Q := matrixBlockProjection (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding
  have hQ : ‖Q‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [mul_one] using mul_le_mul (norm_matrixInsert_le p α.toEmbedding τ.toEmbedding)
        (norm_matrixRestrict_le p α.toEmbedding τ.toEmbedding)
        (norm_nonneg (matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)) zero_le_one)
  have hQxs (r : Fin S.card) : ‖Q (xs r)‖ ≤ ε / 2 := by
    have hres : matrixHilbertSchmidtNorm p (matrixRestrict p α.toEmbedding τ.toEmbedding (xs r)) ≤ δ := hst r
    calc
      _ ≤ ‖matrixRestrict p α.toEmbedding τ.toEmbedding (xs r)‖ := by
        exact ((matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).le_opNorm _).trans
          (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (norm_matrixInsert_le (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)
              (norm_nonneg (matrixRestrict p α.toEmbedding τ.toEmbedding (xs r))))
      _ ≤ (k : ℝ) ^ a * matrixHilbertSchmidtNorm p (matrixRestrict p α.toEmbedding τ.toEmbedding (xs r)) :=
        hlower k hk _
      _ ≤ (k : ℝ) ^ a * δ := mul_le_mul_of_nonneg_left hres hkpow.le
      _ = ε / 2 := by dsimp only [δ]; field_simp [ne_of_gt hkpow]
  let R : E →L[𝕜] FiniteMatrixBlock 𝕜 p N := Q.comp E.subtypeL
  have hR : ‖R‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hScover x hx.le
    let r := u.symm ⟨y, hy⟩
    have hr : xs r = y.val := by simp only [xs, r, Equiv.apply_symm_apply]
    have hyQ : ‖Q y.val‖ ≤ ε / 2 := by simpa only [hr] using hQxs r
    have hdiff : ‖Q (x.val - y.val)‖ ≤ ε / 2 :=
      ((Q.le_opNorm _).trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hQ (norm_nonneg (x.val - y.val)))).trans hxy
    change ‖Q x.val‖ ≤ ε
    have heq : Q x.val = Q y.val + Q (x.val - y.val) := by rw [map_sub]; abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  refine ⟨α, τ, ?_⟩
  intro x
  exact (R.le_opNorm x).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg x))

end ThesisCommon

