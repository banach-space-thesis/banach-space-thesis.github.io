import PL1.LpInclusions
import PL1.Definitions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The first Walsh chaos in Haar L1

This module develops the concrete Rademacher map and its finite-sum moment
estimates. Constants in the embedding estimate need not be optimal.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace PL1.Walsh

private theorem continuous_integrable (f : C(Group, ℝ)) : Integrable f haar :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Haar expectation on continuous real functions, as a linear map. -/
def expectation : C(Group, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂haar
  map_add' f g := integral_add (continuous_integrable f) (continuous_integrable g)
  map_smul' c f := integral_smul c f

@[simp] theorem expectation_one : expectation 1 = 1 := by
  simp [expectation]

@[simp] theorem expectation_const_mul (c : ℝ) (f : C(Group, ℝ)) :
    expectation (ContinuousMap.const Group c * f) = c * expectation f :=
  integral_const_mul c f

@[simp] theorem expectation_const (c : ℝ) : expectation (ContinuousMap.const Group c) = c := by
  simp [expectation]

/-- A finite Rademacher polynomial, as an actual continuous function on the sign group. -/
def rademacherPolynomial (s : Finset ℕ) (a : ℕ → ℝ) : C(Group, ℝ) :=
  ∑ j ∈ s, ContinuousMap.const Group (a j) * characterContinuous {j}

@[simp] theorem rademacherPolynomial_empty (a : ℕ → ℝ) :
    rademacherPolynomial ∅ a = 0 := by simp [rademacherPolynomial]

theorem rademacherPolynomial_insert {j : ℕ} {s : Finset ℕ} (hj : j ∉ s) (a : ℕ → ℝ) :
    rademacherPolynomial (insert j s) a =
      ContinuousMap.const Group (a j) * characterContinuous {j} + rademacherPolynomial s a := by
  simp only [rademacherPolynomial, Finset.sum_insert hj]

theorem character_flip_of_not_mem {s : Finset ℕ} {j : ℕ} (hj : j ∉ s) :
    character s (flip j) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [flip, Function.update_of_ne hij, signValue]

theorem rademacherPolynomial_flip {s : Finset ℕ} {j : ℕ} (hj : j ∉ s)
    (a : ℕ → ℝ) (x : Group) :
    rademacherPolynomial s a (flip j * x) = rademacherPolynomial s a x := by
  simp only [rademacherPolynomial, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.const_apply, characterContinuous]
  apply Finset.sum_congr rfl
  intro i hi
  have hji : j ∉ ({i} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using (fun h : j = i => hj (h ▸ hi))
  simp only [ContinuousMap.coe_mk, character_mul, character_flip_of_not_mem hji, one_mul]

/-- An odd factor in a fresh Rademacher coordinate has zero Haar expectation. -/
theorem expectation_rademacher_odd {s : Finset ℕ} {j : ℕ} (hj : j ∉ s)
    (a : ℕ → ℝ) (k : ℕ) :
    expectation (rademacherPolynomial s a ^ k * characterContinuous {j}) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := flip j)
  intro x
  change rademacherPolynomial s a (flip j * x) ^ k * character {j} (flip j * x) =
    -(rademacherPolynomial s a x ^ k * character {j} x)
  rw [rademacherPolynomial_flip hj, character_mul,
    character_flip_of_mem (Finset.mem_singleton_self j)]
  ring

private theorem rademacherPolynomial_square {s : Finset ℕ} {j : ℕ} (hj : j ∉ s)
    (a : ℕ → ℝ) :
    rademacherPolynomial (insert j s) a ^ 2 =
      rademacherPolynomial s a ^ 2 +
      ContinuousMap.const Group (2 * a j) * (rademacherPolynomial s a * characterContinuous {j}) +
      ContinuousMap.const Group (a j ^ 2) := by
  ext x
  rw [rademacherPolynomial_insert hj]
  change (a j * character {j} x + rademacherPolynomial s a x) ^ 2 =
    rademacherPolynomial s a x ^ 2 + 2 * a j *
      (rademacherPolynomial s a x * character {j} x) + a j ^ 2
  have hr : character {j} x ^ 2 = 1 := by
    simpa only [pow_two] using character_mul_self {j} x
  nlinarith [sq_nonneg (a j)]

/-- The exact second moment of a finite real Rademacher polynomial. -/
theorem expectation_rademacher_square (s : Finset ℕ) (a : ℕ → ℝ) :
    expectation (rademacherPolynomial s a ^ 2) = ∑ j ∈ s, a j ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [rademacherPolynomial_square hj, map_add, map_add,
      expectation_const_mul, expectation_const, ih]
    have ho := expectation_rademacher_odd hj a 1
    simp only [pow_one] at ho
    rw [ho]
    simp [Finset.sum_insert hj, add_comm]

private theorem rademacherPolynomial_fourth {s : Finset ℕ} {j : ℕ} (hj : j ∉ s)
    (a : ℕ → ℝ) :
    rademacherPolynomial (insert j s) a ^ 4 =
      rademacherPolynomial s a ^ 4 +
      ContinuousMap.const Group (4 * a j) * (rademacherPolynomial s a ^ 3 * characterContinuous {j}) +
      ContinuousMap.const Group (6 * a j ^ 2) * (rademacherPolynomial s a ^ 2) +
      ContinuousMap.const Group (4 * a j ^ 3) * (rademacherPolynomial s a * characterContinuous {j}) +
      ContinuousMap.const Group (a j ^ 4) := by
  ext x
  rw [rademacherPolynomial_insert hj]
  change (a j * character {j} x + rademacherPolynomial s a x) ^ 4 =
    rademacherPolynomial s a x ^ 4 + 4 * a j *
      (rademacherPolynomial s a x ^ 3 * character {j} x) +
      6 * a j ^ 2 * rademacherPolynomial s a x ^ 2 +
      4 * a j ^ 3 * (rademacherPolynomial s a x * character {j} x) + a j ^ 4
  have hr : character {j} x ^ 2 = 1 := by
    simpa only [pow_two] using character_mul_self {j} x
  rcases sq_eq_one_iff.mp hr with hr | hr <;> rw [hr] <;> ring

/-- The exact fourth moment, including its negative diagonal correction. -/
theorem expectation_rademacher_fourth (s : Finset ℕ) (a : ℕ → ℝ) :
    expectation (rademacherPolynomial s a ^ 4) =
      3 * (∑ j ∈ s, a j ^ 2) ^ 2 - 2 * ∑ j ∈ s, a j ^ 4 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [rademacherPolynomial_fourth hj]
    simp only [map_add, expectation_const_mul, expectation_const,
      expectation_rademacher_odd hj a 3, expectation_rademacher_square, ih]
    have ho := expectation_rademacher_odd hj a 1
    simp only [pow_one] at ho
    rw [ho]
    simp only [Finset.sum_insert hj]
    ring

theorem expectation_rademacher_fourth_le (s : Finset ℕ) (a : ℕ → ℝ) :
    expectation (rademacherPolynomial s a ^ 4) ≤ 3 * (∑ j ∈ s, a j ^ 2) ^ 2 := by
  rw [expectation_rademacher_fourth]
  have h : 0 ≤ ∑ j ∈ s, a j ^ 4 := Finset.sum_nonneg (fun j _ => by positivity)
  linarith

private theorem quartic_lower_bound (A u : ℝ) (hA : 0 ≤ A) (hu : 0 ≤ u) :
    A * u ^ 2 ≤ 4 * A * Real.sqrt A * u + (1 / 16 : ℝ) * u ^ 4 := by
  have hr := Real.sqrt_nonneg A
  have hr2 := Real.sq_sqrt hA
  by_cases h : u ≤ 4 * Real.sqrt A
  · have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hA hu)
    nlinarith [pow_nonneg hu 4]
  · have hle : 4 * Real.sqrt A ≤ u := (lt_of_not_ge h).le
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ 4 * Real.sqrt A) hu).mpr hle
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg u)
    nlinarith [mul_nonneg (mul_nonneg hA hr) hu]

/-- An elementary moment interpolation bound, with a nonoptimal but convenient constant.
The proof uses a pointwise quartic inequality instead of fractional-exponent Hölder. -/
theorem sqrt_secondMoment_le_eight_firstMoment (f : C(Group, ℝ)) (A : ℝ) (hA : 0 ≤ A)
    (h2 : expectation (f ^ 2) = A) (h4 : expectation (f ^ 4) ≤ 6 * A ^ 2) :
    Real.sqrt A ≤ 8 * ∫ x, ‖f x‖ ∂haar := by
  let af : C(Group, ℝ) := ⟨fun x => |f x|, f.continuous.abs⟩
  have habs : expectation af = ∫ x, ‖f x‖ ∂haar := by rfl
  have hnonneg : 0 ≤ expectation af := integral_nonneg (fun x => abs_nonneg (f x))
  have hint : expectation (ContinuousMap.const Group A * f ^ 2) ≤
      expectation (ContinuousMap.const Group (4 * A * Real.sqrt A) * af +
        ContinuousMap.const Group (1 / 16 : ℝ) * f ^ 4) := by
    apply integral_mono (continuous_integrable _) (continuous_integrable _)
    intro x
    change A * f x ^ 2 ≤ 4 * A * Real.sqrt A * |f x| + (1 / 16 : ℝ) * f x ^ 4
    have h := quartic_lower_bound A |f x| hA (abs_nonneg _)
    simpa only [sq_abs, (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_abs] using h
  simp only [map_add, expectation_const_mul, h2] at hint
  rw [← habs]
  by_cases hAz : A = 0
  · simpa [hAz] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hnonneg
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hrp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
    by_contra hbad
    have hL : expectation af < Real.sqrt A / 8 := by linarith
    have hm := mul_lt_mul_of_pos_left hL (by positivity : 0 < 4 * A * Real.sqrt A)
    have heq : (4 * A * Real.sqrt A) * (Real.sqrt A / 8) = A ^ 2 / 2 := by
      calc
        _ = A * (Real.sqrt A ^ 2) / 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hA]; ring
    rw [heq] at hm
    nlinarith [sq_pos_of_pos hAp]

theorem rademacher_firstMoment_lower (s : Finset ℕ) (a : ℕ → ℝ) :
    Real.sqrt (∑ j ∈ s, a j ^ 2) ≤
      8 * ∫ x, ‖rademacherPolynomial s a x‖ ∂haar := by
  apply sqrt_secondMoment_le_eight_firstMoment _ _
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (expectation_rademacher_square s a)
  exact (expectation_rademacher_fourth_le s a).trans (by nlinarith [sq_nonneg (∑ j ∈ s, a j ^ 2)])

section RademacherMap

variable (𝕜 : Type*) [RCLike 𝕜]

theorem orthonormal_rademacherL2 :
    Orthonormal 𝕜 (fun j : ℕ => scalarCharacterLp 𝕜 2 {j}) :=
  (orthonormal_scalarCharacterL2 𝕜).comp (fun j : ℕ => ({j} : Finset ℕ))
    (fun _i _j h => Finset.singleton_injective h)

/-- The Rademacher series defines an isometry from actual scalar ell2 into Haar L2. -/
def rademacherL2 : Ell2 𝕜 →ₗᵢ[𝕜] Lp 𝕜 2 haar :=
  (orthonormal_rademacherL2 𝕜).orthogonalFamily.linearIsometry

theorem rademacherL2_single (j : ℕ) (a : 𝕜) :
    rademacherL2 𝕜 (lp.single 2 j a) = a • scalarCharacterLp 𝕜 2 {j} := by
  exact (orthonormal_rademacherL2 𝕜).orthogonalFamily.linearIsometry_apply_single a

/-- The concrete first-chaos map into Haar L1. -/
def rademacherL1 : Ell2 𝕜 →L[𝕜] Lp 𝕜 1 haar :=
  l2ToL1.comp (rademacherL2 𝕜).toContinuousLinearMap

theorem rademacherL1_single (j : ℕ) (a : 𝕜) :
    rademacherL1 𝕜 (lp.single 2 j a) = a • scalarCharacterLp 𝕜 1 {j} := by
  change l2ToL1 (rademacherL2 𝕜 (lp.single 2 j a)) = _
  rw [rademacherL2_single, map_smul, l2ToL1_scalarCharacter]

theorem norm_rademacherL1_le (a : Ell2 𝕜) : ‖rademacherL1 𝕜 a‖ ≤ ‖a‖ := by
  have h := ProbabilityLp.norm_inclusionFun_le haar 1 2 (by norm_num) (rademacherL2 𝕜 a)
  change ‖rademacherL1 𝕜 a‖ ≤ ‖rademacherL2 𝕜 a‖ at h
  simpa only [LinearIsometry.norm_map] using h

end RademacherMap

theorem scalarCharacterLp_real (p : ℝ≥0∞) (F : Finset ℕ) :
    scalarCharacterLp ℝ p F = characterLp p F := by
  apply Lp.ext
  exact (coeFn_scalarCharacterLp ℝ p F).trans (coeFn_characterLp p F).symm

theorem rademacherL1_real_sum (s : Finset ℕ) (a : ℕ → ℝ) :
    rademacherL1 ℝ (∑ j ∈ s, lp.single 2 j (a j)) =
      ContinuousMap.toLp 1 haar ℝ (rademacherPolynomial s a) := by
  simp only [map_sum, rademacherL1_single, scalarCharacterLp_real,
    rademacherPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : ContinuousMap.const Group (a j) * characterContinuous {j} =
      a j • characterContinuous {j} := by ext x; rfl
  rw [heq, map_smul, toLp_characterContinuous]

theorem norm_rademacherL1_real_sum (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖rademacherL1 ℝ (∑ j ∈ s, lp.single 2 j (a j))‖ =
      ∫ x, ‖rademacherPolynomial s a x‖ ∂haar := by
  rw [rademacherL1_real_sum, L1.norm_eq_integral_norm]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp haar
    (rademacherPolynomial s a)).fun_comp norm)

theorem norm_ell2_real_sum (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ j ∈ s, lp.single 2 j (a j)‖ = Real.sqrt (∑ j ∈ s, a j ^ 2) := by
  have h := lp.norm_sum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) a s
  norm_num [Real.rpow_natCast, Real.norm_eq_abs, sq_abs] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem rademacherL1_real_sum_lower (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ j ∈ s, lp.single 2 j (a j)‖ ≤
      8 * ‖rademacherL1 ℝ (∑ j ∈ s, lp.single 2 j (a j))‖ := by
  rw [norm_ell2_real_sum, norm_rademacherL1_real_sum]
  exact rademacher_firstMoment_lower s a

theorem rademacherL1_real_lower (a : Ell2 ℝ) :
    ‖a‖ ≤ 8 * ‖rademacherL1 ℝ a‖ := by
  have hsum := lp.hasSum_single (p := 2) (by norm_num) a
  exact le_of_tendsto_of_tendsto' hsum.norm
    ((((rademacherL1 ℝ).continuous.tendsto a).comp hsum).norm.const_mul 8)
    (fun s => rademacherL1_real_sum_lower s a)

theorem rademacherL1_real_antilipschitz : AntilipschitzWith 8 (rademacherL1 ℝ) :=
  (rademacherL1 ℝ).antilipschitz_of_bound rademacherL1_real_lower

theorem rademacherL1_real_injective : Function.Injective (rademacherL1 ℝ) :=
  rademacherL1_real_antilipschitz.injective

theorem rademacherL1_real_isClosed_range : IsClosed (Set.range (rademacherL1 ℝ)) :=
  rademacherL1_real_antilipschitz.isClosed_range (rademacherL1 ℝ).uniformContinuous

/-- The genuine Hilbert space ell2 is continuously linearly isomorphic to the
closed first Walsh chaos in Haar L1. -/
def rademacherL1_real_equivRange : Ell2 ℝ ≃L[ℝ] (rademacherL1 ℝ).range :=
  (rademacherL1 ℝ).equivRange rademacherL1_real_injective rademacherL1_real_isClosed_range

theorem haarL1_contains_ell2_real : ContainsIsomorphicCopy ℝ (Ell2 ℝ) (Lp ℝ 1 haar) :=
  ⟨(rademacherL1 ℝ).range, rademacherL1_real_isClosed_range, ⟨rademacherL1_real_equivRange⟩⟩

section ScalarEmbedding

variable (𝕜 : Type*) [RCLike 𝕜]

def scalarRademacherPolynomial (s : Finset ℕ) (a : ℕ → 𝕜) : C(Group, 𝕜) :=
  ∑ j ∈ s, a j • scalarCharacterContinuous 𝕜 {j}

theorem re_scalarRademacherPolynomial (s : Finset ℕ) (a : ℕ → 𝕜) (x : Group) :
    RCLike.re (scalarRademacherPolynomial 𝕜 s a x) =
      rademacherPolynomial s (fun j => RCLike.re (a j)) x := by
  simp [scalarRademacherPolynomial, rademacherPolynomial, scalarCharacterContinuous,
    scalarCharacter, characterContinuous, RCLike.mul_re]

theorem im_scalarRademacherPolynomial (s : Finset ℕ) (a : ℕ → 𝕜) (x : Group) :
    RCLike.im (scalarRademacherPolynomial 𝕜 s a x) =
      rademacherPolynomial s (fun j => RCLike.im (a j)) x := by
  simp [scalarRademacherPolynomial, rademacherPolynomial, scalarCharacterContinuous,
    scalarCharacter, characterContinuous, RCLike.mul_im]

theorem rademacherL1_sum (s : Finset ℕ) (a : ℕ → 𝕜) :
    rademacherL1 𝕜 (∑ j ∈ s, lp.single 2 j (a j)) =
      ContinuousMap.toLp 1 haar 𝕜 (scalarRademacherPolynomial 𝕜 s a) := by
  simp only [map_sum, rademacherL1_single, scalarRademacherPolynomial, map_smul,
    toLp_scalarCharacterContinuous]

theorem norm_rademacherL1_sum (s : Finset ℕ) (a : ℕ → 𝕜) :
    ‖rademacherL1 𝕜 (∑ j ∈ s, lp.single 2 j (a j))‖ =
      ∫ x, ‖scalarRademacherPolynomial 𝕜 s a x‖ ∂haar := by
  rw [rademacherL1_sum, L1.norm_eq_integral_norm]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp haar
    (scalarRademacherPolynomial 𝕜 s a)).fun_comp norm)

theorem norm_ell2_sum_le_re_add_im (s : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ j ∈ s, lp.single 2 j (a j)‖ ≤
      Real.sqrt (∑ j ∈ s, RCLike.re (a j) ^ 2) +
      Real.sqrt (∑ j ∈ s, RCLike.im (a j) ^ 2) := by
  have h := lp.norm_sum_single (E := fun _ : ℕ => 𝕜) (p := 2) (by norm_num) a s
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have hsplit : (∑ j ∈ s, ‖a j‖ ^ (2 : ℕ)) =
      (∑ j ∈ s, RCLike.re (a j) ^ 2) + (∑ j ∈ s, RCLike.im (a j) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [sq] using (RCLike.norm_sq_eq_def (z := a j))
  rw [hsplit] at h
  have hr := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ s) => sq_nonneg (RCLike.re (a j))))
  have hi := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ s) => sq_nonneg (RCLike.im (a j))))
  have hr0 := Real.sqrt_nonneg (∑ j ∈ s, RCLike.re (a j) ^ 2)
  have hi0 := Real.sqrt_nonneg (∑ j ∈ s, RCLike.im (a j) ^ 2)
  nlinarith [norm_nonneg (∑ j ∈ s, lp.single 2 j (a j)), mul_nonneg hr0 hi0]

theorem rademacherL1_sum_lower (s : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ j ∈ s, lp.single 2 j (a j)‖ ≤
      16 * ‖rademacherL1 𝕜 (∑ j ∈ s, lp.single 2 j (a j))‖ := by
  rw [norm_rademacherL1_sum]
  have hint : Integrable (fun x => ‖scalarRademacherPolynomial 𝕜 s a x‖) haar :=
    (scalarRademacherPolynomial 𝕜 s a).continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hre : (∫ x, ‖rademacherPolynomial s (fun j => RCLike.re (a j)) x‖ ∂haar) ≤
      ∫ x, ‖scalarRademacherPolynomial 𝕜 s a x‖ ∂haar := by
    apply integral_mono (continuous_integrable _).norm hint
    intro x
    change ‖rademacherPolynomial s (fun j => RCLike.re (a j)) x‖ ≤ _
    rw [← re_scalarRademacherPolynomial 𝕜 s a x]
    exact RCLike.norm_re_le_norm _
  have him : (∫ x, ‖rademacherPolynomial s (fun j => RCLike.im (a j)) x‖ ∂haar) ≤
      ∫ x, ‖scalarRademacherPolynomial 𝕜 s a x‖ ∂haar := by
    apply integral_mono (continuous_integrable _).norm hint
    intro x
    change ‖rademacherPolynomial s (fun j => RCLike.im (a j)) x‖ ≤ _
    rw [← im_scalarRademacherPolynomial 𝕜 s a x]
    exact RCLike.norm_im_le_norm _
  have hr := rademacher_firstMoment_lower s (fun j => RCLike.re (a j))
  have hi := rademacher_firstMoment_lower s (fun j => RCLike.im (a j))
  have hn := norm_ell2_sum_le_re_add_im 𝕜 s a
  linarith

/-- A uniform first-chaos lower bound covering both real and complex scalars. -/
theorem rademacherL1_lower (a : Ell2 𝕜) :
    ‖a‖ ≤ 16 * ‖rademacherL1 𝕜 a‖ := by
  have hsum := lp.hasSum_single (p := 2) (by norm_num) a
  exact le_of_tendsto_of_tendsto' hsum.norm
    ((((rademacherL1 𝕜).continuous.tendsto a).comp hsum).norm.const_mul 16)
    (fun s => rademacherL1_sum_lower 𝕜 s a)

theorem rademacherL1_antilipschitz : AntilipschitzWith 16 (rademacherL1 𝕜) :=
  (rademacherL1 𝕜).antilipschitz_of_bound (rademacherL1_lower 𝕜)

theorem rademacherL1_injective : Function.Injective (rademacherL1 𝕜) :=
  (rademacherL1_antilipschitz 𝕜).injective

theorem rademacherL1_isClosed_range : IsClosed (Set.range (rademacherL1 𝕜)) :=
  (rademacherL1_antilipschitz 𝕜).isClosed_range (rademacherL1 𝕜).uniformContinuous

def rademacherL1_equivRange : Ell2 𝕜 ≃L[𝕜] (rademacherL1 𝕜).range :=
  (rademacherL1 𝕜).equivRange (rademacherL1_injective 𝕜) (rademacherL1_isClosed_range 𝕜)

theorem haarL1_contains_ell2 : ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (Lp 𝕜 1 haar) :=
  ⟨(rademacherL1 𝕜).range, rademacherL1_isClosed_range 𝕜, ⟨rademacherL1_equivRange 𝕜⟩⟩

/-- A common eigenvalue on coordinate Rademacher functions extends to the whole
closed first chaos by norm convergence of the ell2 series. -/
theorem rademacherL1_eigen (S : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar) (c : 𝕜)
    (hS : ∀ j, S (scalarCharacterLp 𝕜 1 {j}) = c • scalarCharacterLp 𝕜 1 {j})
    (a : Ell2 𝕜) : S (rademacherL1 𝕜 a) = c • rademacherL1 𝕜 a := by
  have hs := lp.hasSum_single (p := 2) (by norm_num) a
  have hleft := (S.comp (rademacherL1 𝕜)).hasSum hs
  have hright := (c • rademacherL1 𝕜).hasSum hs
  apply hleft.unique
  convert hright using 1
  · ext j
    simp only [ContinuousLinearMap.comp_apply, rademacherL1_single,
      smul_apply, map_smul, hS, smul_smul]
    rw [mul_comm]
  · rfl

end ScalarEmbedding

end PL1.Walsh

