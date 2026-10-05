import ThesisCommon.Analysis.EllOneSchur
import ThesisCommon.Analysis.GrothendieckMoments
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The Rademacher obstruction to Schur's property. Finite equal-size
partitions suffice to compute the weak convergence; there is no measure-space
representation hypothesis in this argument. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ThesisCommon
open Grothendieck

theorem rademacher_coefficient_bound {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (a : Fin n → ℝ) (ha : ∀ i, mean (fun ω => signedValue (ω i) (f ω)) = a i)
    {C : ℝ} (_hC : 0 ≤ C) (hf : ∀ ω, |f ω| ≤ C) : ∑ i, a i ^ 2 ≤ C ^ 2 := by
  have hid : mean (fun ω => rademacher a ω * f ω) = ∑ i, a i ^ 2 := by
    simp only [rademacher, Finset.sum_mul]
    rw [mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : (fun ω => signedValue (ω i) (a i) * f ω) =
        (fun ω => a i * signedValue (ω i) (f ω)) := by
      funext ω
      cases ω i <;> simp [signedValue]
    rw [heq, mean_mul_left, ha i, pow_two]
  have hsq : mean (fun ω => f ω ^ 2) ≤ C ^ 2 := by
    calc
      _ ≤ mean (fun _ : Fin n → Bool => C ^ 2) := mean_mono (fun ω => by
        simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (f ω)) (hf ω) 2))
      _ = C ^ 2 := mean_const _
  have hcs := mean_mul_sq_le (rademacher a) f
  rw [hid, rademacher_second] at hcs
  have hpos : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith

/-- Every fixed functional is square summable on a Rademacher system whose
level-N leaves have norm at most M divided by the number of leaves. -/
theorem rademacher_functional_summable_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (p : (n : ℕ) → (Fin n → Bool) → E) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n ω, (Fintype.card (Fin n → Bool) : ℝ) * ‖p n ω‖ ≤ M)
    (hv : ∀ n (i : Fin n), v i = ∑ ω : Fin n → Bool, signedValue (ω i) (p n ω))
    (φ : E →L[ℝ] ℝ) : Summable (fun n => (φ (v n)) ^ 2) := by
  apply summable_of_sum_range_le (fun n => sq_nonneg _) (c := (‖φ‖ * M) ^ 2)
  intro n
  rw [← Fin.sum_univ_eq_sum_range]
  let c : ℝ := Fintype.card (Fin n → Bool)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast Fintype.card_pos
  let f : (Fin n → Bool) → ℝ := fun ω => c * φ (p n ω)
  apply rademacher_coefficient_bound f (fun i : Fin n => φ (v i)) ?_
    (mul_nonneg (norm_nonneg _) hM) ?_
  · intro i
    have heq : (fun ω => signedValue (ω i) (f ω)) =
        (fun ω => c * signedValue (ω i) (φ (p n ω))) := by
      funext ω
      cases ω i <;> simp [f, signedValue]
    rw [heq, mean_mul_left]
    have hmean : c * mean (fun ω => signedValue (ω i) (φ (p n ω))) =
        ∑ ω : Fin n → Bool, signedValue (ω i) (φ (p n ω)) := by
      dsimp [mean]
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rw [hmean]
    dsimp only
    rw [hv n i, map_sum]
    apply Finset.sum_congr rfl
    intro ω _
    cases ω i <;> simp [signedValue]
  · intro ω
    calc
      |f ω| = c * ‖φ (p n ω)‖ := by simp only [f, abs_mul, abs_of_pos hc, Real.norm_eq_abs]
      _ ≤ c * (‖φ‖ * ‖p n ω‖) := mul_le_mul_of_nonneg_left (φ.le_opNorm _) hc.le
      _ = ‖φ‖ * (c * ‖p n ω‖) := by ring
      _ ≤ ‖φ‖ * M := mul_le_mul_of_nonneg_left (hp n ω) (norm_nonneg _)

theorem rademacher_weakly_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (p : (n : ℕ) → (Fin n → Bool) → E) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n ω, (Fintype.card (Fin n → Bool) : ℝ) * ‖p n ω‖ ≤ M)
    (hv : ∀ n (i : Fin n), v i = ∑ ω : Fin n → Bool, signedValue (ω i) (p n ω))
    (φ : E →L[ℝ] ℝ) : Tendsto (fun n => φ (v n)) atTop (𝓝 0) := by
  have ht := (rademacher_functional_summable_sq v p hM hp hv φ).tendsto_atTop_zero
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  simp only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (φ (v n)))] at hb
  rw [dist_zero_right, Real.norm_eq_abs]
  nlinarith [sq_abs (φ (v n)), abs_nonneg (φ (v n))]

/-- Such a system must converge in norm in every space isomorphic to ell-one.
In particular, a system with a fixed nonzero norm cannot exist there. -/
theorem schur_rademacher_tendsto_zero
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (v : ℕ → E) (p : (n : ℕ) → (Fin n → Bool) → E) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n ω, (Fintype.card (Fin n → Bool) : ℝ) * ‖p n ω‖ ≤ M)
    (hv : ∀ n (i : Fin n), v i = ∑ ω : Fin n → Bool, signedValue (ω i) (p n ω)) :
    Tendsto v atTop (𝓝 0) :=
  schur_of_equiv_ellOne d v (rademacher_weakly_null v p hM hp hv)

end ThesisCommon
