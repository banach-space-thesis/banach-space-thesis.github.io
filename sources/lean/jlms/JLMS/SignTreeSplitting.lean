import JLMS.PairedFiniteBlocks
import JLMS.DualRadiusWitness
import JLMS.DualCompactUniformBound
import JLMS.SignTreeEstimates

/-!
# Splitting each finite sign-tree branch into two infinite subbranches

Stability supplies a large fixed-vector value for the normalized average of
all paired differences. Uniform bounds on the newly enlarged finite-dimensional
space then force every pair to have opposite near-unit signs. Common thinning
preserves disjointness and all earlier branch values.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_split_sign_families (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (hstable : ∀ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = 1)
    (e : ι → ℕ → ℕ) (he : Function.Injective (fun p : ι × ℕ => e p.1 p.2))
    (hs : ∀ i, StrictMono (e i)) (D : X → Submodule 𝕜 X)
    (hD : ∀ x, FiniteDimensional 𝕜 (D x)) (hxD : ∀ x, x ∈ D x) :
    ∃ x : X, ‖x‖ = 1 ∧ ∃ p : ℕ → ℕ, StrictMono p ∧
      (∀ i n j, j < 2 → ‖(f (e i (2 * p n + j))).comp (D x).subtypeL‖ ≤ 2) ∧
      ∀ i n, ‖f (e i (2 * p n + 1)) x - 1‖ ≤ 1 / 4 ∧
        ‖f (e i (2 * p n)) x - (-1)‖ ≤ 1 / 4 := by
  classical
  let N : ℝ := Fintype.card ι
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNone : 1 ≤ N := by
    change (1 : ℝ) ≤ (Fintype.card ι : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  let ε : ℝ := 1 / (2048 * N)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε ≤ 1 / 1024 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 2048 * N)).mpr
    nlinarith
  have hεone : ε < 1 := by linarith
  obtain ⟨q, hq, b, hb⟩ := exists_paired_average_block e he hs f
  obtain ⟨x, hx, s, hs', hlarge⟩ := exists_unit_real_subsequence_gt
    (b.applyDual f) hC (b.norm_applyDual_le f hf)
    (show 0 ≤ 1 - ε by linarith) (by rw [hstable]; linarith)
  letI := hD x
  have hunit : DualEventualBound f 1 := by
    have ht := dualAsymptoticRadius_eventualBound f hC hf
    have heq : dualAsymptoticRadius f = 1 := by
      have h := hstable (NormalizedBlockSystem.units (𝕜 := 𝕜))
      have heq : (NormalizedBlockSystem.units (𝕜 := 𝕜)).applyDual f = f := by
        funext n; exact NormalizedBlockSystem.units_applyDual f n
      rwa [heq] at h
    rwa [heq] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (dualEventualBound_finiteDimensional_restriction f hC hf (by norm_num)
      hunit hε (D x))
  let p (n : ℕ) := q (s (n + M))
  have hp : StrictMono p := hq.comp (hs'.comp (by
    intro i j hij
    change i + M < j + M
    omega))
  have hrestr (i : ι) (n j : ℕ) :
      ‖(f (e i (2 * p n + j))).comp (D x).subtypeL‖ ≤ 1 + ε := by
    apply hM
    have h1 := (hs i).id_le (2 * p n + j)
    have h2 : s (n + M) ≤ q (s (n + M)) := hq.id_le (s (n + M))
    have h3 : n + M ≤ s (n + M) := hs'.id_le (n + M)
    dsimp [p] at h1 ⊢
    omega
  have hvalue (i : ι) (n j : ℕ) : ‖f (e i (2 * p n + j)) x‖ ≤ 1 + ε := by
    let y : D x := ⟨x, hxD x⟩
    have hh := ((f (e i (2 * p n + j))).comp (D x).subtypeL).le_opNorm y
    exact hh.trans (by simpa only [y, Submodule.coe_norm, hx, mul_one] using
      mul_le_mul_of_nonneg_right (hrestr i n j) (norm_nonneg y))
  refine ⟨x, hx, p, hp, fun i n j _ => (hrestr i n j).trans (by linarith), ?_⟩
  intro i n
  let a (i : ι) := (RCLike.re (f (e i (2 * p n + 1)) x) -
    RCLike.re (f (e i (2 * p n)) x)) / 2
  have hau (i : ι) : a i ≤ 1 + ε := by
    have h1 := RCLike.re_le_norm (f (e i (2 * p n + 1)) x)
    have h0 := (abs_le.mp (RCLike.abs_re_le_norm (f (e i (2 * p n)) x))).1
    have hnorm1 := hvalue i n 1
    have hnorm0 := hvalue i n 0
    dsimp [a]
    simp only [Nat.add_zero] at h0 hnorm0
    linarith
  have havg : N * (1 - ε) ≤ ∑ i, a i := by
    have hh := hlarge (n + M)
    rw [hb] at hh
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, RCLike.re_ofReal_mul, map_sum, map_sub] at hh
    have heq : (∑ i, a i) = (∑ i, (RCLike.re (f (e i (2 * p n + 1)) x) -
        RCLike.re (f (e i (2 * p n)) x))) / 2 := by
      simp only [a, div_eq_mul_inv, ← Finset.sum_mul]
    rw [heq]
    change 1 - ε < (1 / (2 * N)) * _ at hh
    have hhh := mul_lt_mul_of_pos_right hh (by positivity : 0 < 2 * N)
    have hcancel (z : ℝ) : (1 / (2 * N)) * z * (2 * N) = z := by
      field_simp
    rw [hcancel] at hhh
    change (1 - ε) * (2 * N) < (∑ i, (RCLike.re (f (e i (2 * p n + 1)) x) -
      RCLike.re (f (e i (2 * p n)) x))) at hhh
    nlinarith
  have hm : 1 - (1 / 1024 : ℝ) ≤ a i := by
    apply finite_average_sign_margin Finset.univ a hε.le _ (fun i _ => hau i)
      (by simpa only [Finset.card_univ] using havg) (Finset.mem_univ i)
    dsimp [ε, N]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  have hop := half_difference_opposite_signs
    (f (e i (2 * p n + 1)) x) (f (e i (2 * p n)) x)
    (hvalue i n 1) (by simpa using hvalue i n 0) hm
  exact ⟨norm_near_positive_sign _ ((hvalue i n 1).trans (by linarith))
      (by linarith [hop.1]),
    norm_near_negative_sign _ ((hvalue i n 0).trans (by simpa using hsmall))
      (by linarith [hop.2])⟩

end JLMS
