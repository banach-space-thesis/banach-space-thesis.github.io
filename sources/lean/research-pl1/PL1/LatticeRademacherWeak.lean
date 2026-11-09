import PL1.LatticeRademacher

/-!
# Weak nullness from finite Rademacher square estimates

The estimate is required on every finite family of distinct indices.
Consequently the proof tests convergence against every continuous functional,
not merely a selected countable norming family.
-/

noncomputable section
open Filter TopologicalSpace Finset
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- Signed averages always contain a positive number of terms. -/
def signedAverage (r : ℕ → E) (q : ℕ → ℕ) (ε : ℕ → ℝ) (N : ℕ) : E :=
  ((N + 1 : ℕ) : ℝ)⁻¹ • ∑ i : Fin (N + 1), ε i • r (q i)

theorem abs_signedAverage_le (r : ℕ → E) (u : E)
    (hr : ∀ n, |r n| ≤ u) (q : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) (N : ℕ) :
    |signedAverage r q ε N| ≤ u := by
  classical
  have hu : 0 ≤ u := (abs_nonneg (r 0)).trans (hr 0)
  have hterm (i : Fin (N + 1)) : |ε i • r (q i)| ≤ u := by
    rw [abs_smul']
    rcases hε i with h | h <;> simpa [h] using hr (q i)
  have hsum : |∑ i : Fin (N + 1), ε i • r (q i)| ≤
      ((N + 1 : ℕ) : ℝ) • u := by
    rw [abs]
    have heq : (∑ _ : Fin (N + 1), u) = ((N + 1 : ℕ) : ℝ) • u := by
      simp [← Nat.cast_smul_eq_nsmul ℝ]
    rw [← heq]
    apply sup_le
    · exact sum_le_sum (fun i _ => (le_abs_self _).trans (hterm i))
    · rw [← sum_neg_distrib]
      exact sum_le_sum (fun i _ => (neg_le_abs _).trans (hterm i))
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [signedAverage, abs_smul', abs_of_nonneg (inv_nonneg.mpr hN.le)]
  simpa only [inv_smul_smul₀ hN.ne'] using
    smul_le_smul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)

/-- All finite signed square bounds, including every subsequence. -/
def HasRademacherSquareBound (φ : E →L[ℝ] ℝ) (u : E) (r : ℕ → E) : Prop :=
  ∀ (N : ℕ) (q : Fin N → ℕ), Function.Injective q →
    ∀ ε : Fin N → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) →
      (φ |∑ i, ε i • r (q i)|) ^ 2 ≤ (φ u) ^ 2 * N

/-- Normalizing the finite square estimate makes the positive functional
of the absolute signed average tend to zero. -/
theorem tendsto_dual_abs_signedAverage (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    (u : E) (r : ℕ → E) (hsq : HasRademacherSquareBound φ u r)
    (q : ℕ → ℕ) (hq : Function.Injective q) (ε : ℕ → ℝ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    Tendsto (fun N => φ |signedAverage r q ε N|) atTop (𝓝 0) := by
  have hN (N : ℕ) : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hbound (N : ℕ) : (φ |signedAverage r q ε N|) ^ 2 ≤
      (φ u) ^ 2 * ((N + 1 : ℕ) : ℝ)⁻¹ := by
    have h := hsq (N + 1) (fun i => q i)
      (fun i j hij => Fin.ext (hq hij)) (fun i => ε i) (fun i => hε i)
    rw [signedAverage, abs_smul', abs_of_nonneg (inv_nonneg.mpr (hN N).le),
      map_smul, smul_eq_mul, mul_pow]
    calc
      _ ≤ (((N + 1 : ℕ) : ℝ)⁻¹) ^ 2 * ((φ u) ^ 2 * (N + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by field_simp
  have hinv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hsquares : Tendsto (fun N => (φ |signedAverage r q ε N|) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound (by simpa using hinv.const_mul ((φ u) ^ 2))
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquares
  convert h using 1
  · funext N
    exact (Real.sqrt_sq (StrongDual.apply_nonneg_of_nonneg hφ (abs_nonneg _))).symm
  · simp

/-- In a Schur Banach lattice, the finite square bound forces all signed
averages along every injective subsequence to tend to zero in norm. -/
theorem tendsto_signedAverage [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) (u : E) (r : ℕ → E)
    (hr : ∀ n, |r n| ≤ u) (hsq : HasRademacherSquareBound φ u r)
    (q : ℕ → ℕ) (hq : Function.Injective q) (ε : ℕ → ℝ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    Tendsto (signedAverage r q ε) atTop (𝓝 0) := by
  have h := (tendsto_zero_iff_strictlyPositive hS φ hφ
    (fun N => |signedAverage r q ε N|) u ((abs_nonneg (r 0)).trans (hr 0))
      (fun N => ⟨abs_nonneg _, abs_signedAverage_le r u hr q ε hε N⟩)).mpr
        (tendsto_dual_abs_signedAverage φ hφ.nonneg u r hsq q hq ε hε)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_abs_eq_norm, norm_zero] using h.norm

/-- Vanishing signed averages along all injective subsequences imply weak
nullness against the entire real continuous dual. -/
theorem weaklyConverges_zero_of_signedAverage (r : ℕ → E)
    (havg : ∀ (q : ℕ → ℕ), Function.Injective q →
      ∀ ε : ℕ → ℝ, (∀ n, ε n = 1 ∨ ε n = -1) →
        Tendsto (signedAverage r q ε) atTop (𝓝 0)) : WeaklyConverges ℝ E r 0 := by
  classical
  intro ψ
  rw [map_zero]
  by_contra hbad
  rw [Metric.tendsto_atTop] at hbad
  push Not at hbad
  obtain ⟨δ, hδ, hbad⟩ := hbad
  choose k hk hkδ using hbad
  let next : ℕ → ℕ := fun n => k (n + 1)
  let q : ℕ → ℕ := fun n => next^[n] (k 0)
  have hqstep (n : ℕ) : q (n + 1) = k (q n + 1) := Function.iterate_succ_apply' _ _ _
  have hq : StrictMono q := strictMono_nat_of_lt_succ (fun n => by
    rw [hqstep]
    exact (Nat.lt_succ_self _).trans_le (hk _))
  have hqδ (n : ℕ) : δ ≤ |ψ (r (q n))| := by
    cases n with
    | zero => simpa [q, Real.dist_eq] using hkδ 0
    | succ n => simpa only [hqstep, Real.dist_eq, sub_zero] using hkδ (q n + 1)
  let ε : ℕ → ℝ := fun n => if 0 ≤ ψ (r (q n)) then 1 else -1
  have hε (n : ℕ) : ε n = 1 ∨ ε n = -1 := by dsimp [ε]; split <;> simp
  have heq (n : ℕ) : ε n * ψ (r (q n)) = |ψ (r (q n))| := by
    by_cases h : 0 ≤ ψ (r (q n))
    · simp [ε, h, abs_of_nonneg h]
    · simp [ε, h, abs_of_neg (lt_of_not_ge h)]
  have havgδ (N : ℕ) : δ ≤ ψ (signedAverage r q ε N) := by
    have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hs : ((N + 1 : ℕ) : ℝ) * δ ≤ ∑ i : Fin (N + 1), |ψ (r (q i))| := by
      simpa using sum_le_sum (s := (univ : Finset (Fin (N + 1)))) (fun i _ => hqδ i)
    rw [signedAverage, map_smul, smul_eq_mul, map_sum]
    simp_rw [map_smul, smul_eq_mul, heq]
    have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hN.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul] using h
  have ht : Tendsto (fun N => ψ (signedAverage r q ε N)) atTop (𝓝 0) := by
    rw [← map_zero ψ]
    exact (ψ.continuous.tendsto 0).comp (havg q hq.injective ε hε)
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const hδ).exists
  exact (not_lt_of_ge (havgδ N)) hN

/-- Actual square estimates for all distinct finite index families imply
weak nullness in a Schur Banach lattice. -/
theorem weaklyConverges_zero_of_rademacherSquareBound [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ)
    (u : E) (r : ℕ → E) (hr : ∀ n, |r n| ≤ u)
    (hsq : HasRademacherSquareBound φ u r) : WeaklyConverges ℝ E r 0 :=
  weaklyConverges_zero_of_signedAverage r
    (tendsto_signedAverage hS φ hφ u r hr hsq)

/-- A nonzero constant-modulus Rademacher system contradicts the Schur
property once its finite square estimates have been established. -/
theorem eq_zero_of_constant_abs_rademacherSquareBound [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ)
    (u : E) (r : ℕ → E) (hr : ∀ n, |r n| = u)
    (hsq : HasRademacherSquareBound φ u r) : u = 0 := by
  have h := hS r 0 (weaklyConverges_zero_of_rademacherSquareBound hS φ hφ u r
    (fun n => (hr n).le) hsq)
  have hnorm (n : ℕ) : ‖r n‖ = ‖u‖ := by rw [← norm_abs_eq_norm (r n), hr n]
  have hn : Tendsto (fun _ : ℕ => ‖u‖) atTop (𝓝 0) := by
    simpa only [hnorm, norm_zero] using h.norm
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hn)

end PL1.SchurLattice
