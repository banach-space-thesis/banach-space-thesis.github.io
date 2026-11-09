import PL1.ComplementedLatticeSumming
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Finite operator deductions. The matrix Grothendieck inequality
is an explicit hypothesis. No proof of that hypothesis is claimed here.
-/

noncomputable section
open scoped BigOperators

namespace PL1.FiniteSumming
open PL1.ComplementedLattice

/-- Coordinate form of finite real Grothendieck: the square-sum hypotheses
are exactly Euclidean unit-ball constraints. All dimensions are independent. -/
def MatrixGrothendieckWith (G : ℝ) : Prop :=
  0 ≤ G ∧ ∀ (r c d : ℕ) (a : Fin r → Fin c → ℝ)
    (u : Fin r → Fin d → ℝ) (v : Fin c → Fin d → ℝ) (B : ℝ),
    (∀ i, ∑ l, (u i l) ^ 2 ≤ 1) →
    (∀ j, ∑ l, (v j l) ^ 2 ≤ 1) →
    (∀ (s : Fin r → ℝ) (t : Fin c → ℝ),
      (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ B) →
    |∑ i, ∑ j, a i j * (∑ l, u i l * v j l)| ≤ G * B

abbrev EllOne (k : ℕ) := PiLp 1 (fun _ : Fin k => ℝ)

theorem norm_ellOne (k : ℕ) (x : EllOne k) : ‖x‖ = ∑ l, |x l| := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 x

def signOne (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

theorem signOne_sq (a : ℝ) : signOne a ^ 2 = 1 := by
  unfold signOne
  split <;> norm_num

theorem signOne_mul (a : ℝ) : signOne a * a = |a| := by
  unfold signOne
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem scalar_expansion {d : ℕ} (φ : (Fin d → ℝ) →L[ℝ] ℝ) (x : Fin d → ℝ) :
    ∑ j, φ (Pi.single j 1) * x j = φ x := by
  have hx : ∑ j, x j • Pi.single j (1 : ℝ) = x := by
    ext i
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    _ = φ (∑ j, x j • Pi.single j (1 : ℝ)) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = φ x := by rw [hx]

def entry {d k : ℕ} (T : (Fin d → ℝ) →L[ℝ] EllOne k) (l : Fin k) (j : Fin d) : ℝ :=
  T (Pi.single j 1) l

theorem entry_apply {d k : ℕ} (T : (Fin d → ℝ) →L[ℝ] EllOne k)
    (x : Fin d → ℝ) (l : Fin k) : ∑ j, entry T l j * x j = T x l := by
  exact scalar_expansion ((PiLp.proj 1 (fun _ : Fin k => ℝ) l).comp T) x

theorem entry_scalar_bound {d k : ℕ} (T : (Fin d → ℝ) →L[ℝ] EllOne k)
    (s : Fin k → ℝ) (t : Fin d → ℝ) (hs : ∀ l, |s l| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ l, ∑ j, entry T l j * s l * t j| ≤ ‖T‖ := by
  have he : (∑ l, ∑ j, entry T l j * s l * t j) = ∑ l, s l * T t l := by
    apply Finset.sum_congr rfl
    intro l _
    rw [← entry_apply T t l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑ l, |s l * T t l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |T t l| := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hs l)
    _ = ‖T t‖ := (norm_ellOne k _).symm
    _ ≤ ‖T‖ * ‖t‖ := T.le_opNorm _
    _ ≤ ‖T‖ := by
      have ht' : ‖t‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr ht
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht' (norm_nonneg T)

theorem rearrange {k d n : ℕ} (a : Fin k → Fin d → ℝ)
    (u : Fin k → Fin n → ℝ) (v : Fin d → Fin n → ℝ) :
    (∑ l, ∑ j, a l j * (∑ i, u l i * v j i)) =
      ∑ i, ∑ l, u l i * (∑ j, a l j * v j i) := by
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ l, ∑ i, ∑ j, a l j * (u l i * v j i) := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, a l j * (u l i * v j i) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem twoSumming_of_matrix {G : ℝ} (hG : MatrixGrothendieckWith G)
    (d k : ℕ) (T : (Fin d → ℝ) →L[ℝ] EllOne k) :
    TwoSummingWith T (G * ‖T‖) := by
  classical
  refine ⟨mul_nonneg hG.1 (norm_nonneg T), ?_⟩
  intro n x M hM hx
  have hc (j : Fin d) : ∑ i, (x i j) ^ 2 ≤ M ^ 2 := by
    let φ : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have hφ : ‖φ‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
      simpa only [φ, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z j)
    simpa only [φ, ContinuousLinearMap.proj_apply, sq_abs] using hx φ hφ
  by_cases hM0 : M = 0
  · have hz (i : Fin n) : x i = 0 := by
      ext j
      have hh := (Finset.single_le_sum (fun r _ => sq_nonneg (x r j)) (Finset.mem_univ i)).trans (hc j)
      rw [hM0, zero_pow (by norm_num : 2 ≠ 0)] at hh
      change x i j = 0
      nlinarith [sq_nonneg (x i j)]
    simp only [hz, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, hM0, mul_zero, le_refl]
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  let L : ℝ := Real.sqrt (∑ i, ‖T (x i)‖ ^ 2)
  have hLs : L ^ 2 = ∑ i, ‖T (x i)‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  by_cases hL0 : L = 0
  · rw [← hLs, hL0, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLp : 0 < L := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hL0)
  let u : Fin k → Fin n → ℝ := fun l i => (‖T (x i)‖ / L) * signOne (T (x i) l)
  let v : Fin d → Fin n → ℝ := fun j i => x i j / M
  have hu (l : Fin k) : ∑ i, (u l i) ^ 2 ≤ 1 := by
    simp only [u, mul_pow, signOne_sq, mul_one, div_pow]
    rw [← Finset.sum_div, ← hLs, div_self (pow_ne_zero _ hL0)]
  have hv (j : Fin d) : ∑ i, (v j i) ^ 2 ≤ 1 := by
    simp only [v, div_pow]
    rw [← Finset.sum_div]
    exact (div_le_one (sq_pos_of_pos hMp)).mpr (hc j)
  have hg := hG.2 k d n (entry T) u v ‖T‖ hu hv (entry_scalar_bound T)
  have he : (∑ l, ∑ j, entry T l j * (∑ i, u l i * v j i)) = L / M := by
    rw [rearrange]
    have hi (i : Fin n) : (∑ l, u l i * (∑ j, entry T l j * v j i)) =
        ‖T (x i)‖ ^ 2 / (L * M) := by
      calc
        _ = ∑ l, (‖T (x i)‖ / (L * M)) * |T (x i) l| := by
          apply Finset.sum_congr rfl
          intro l _
          have he' : (∑ j, entry T l j * v j i) = T (x i) l / M := by
            simp only [v, ← mul_div_assoc, ← Finset.sum_div, entry_apply]
          rw [he']
          dsimp only [u]
          rw [← signOne_mul (T (x i) l)]
          ring
        _ = _ := by rw [← Finset.mul_sum, ← norm_ellOne]; ring
    simp_rw [hi]
    rw [← Finset.sum_div, ← hLs]
    field_simp
  rw [he, abs_of_pos (div_pos hLp hMp)] at hg
  have hbound : L ≤ (G * ‖T‖) * M := (div_le_iff₀ hMp).mp hg
  rw [← hLs, ← mul_pow]
  exact pow_le_pow_left₀ hLp.le hbound 2

#print axioms twoSumming_of_matrix

def ellOneDual {d : ℕ} (t : Fin d → ℝ) : EllOne d →L[ℝ] ℝ :=
  ∑ j, t j • PiLp.proj 1 (fun _ : Fin d => ℝ) j

theorem ellOneDual_apply {d : ℕ} (t : Fin d → ℝ) (x : EllOne d) :
    ellOneDual t x = ∑ j, t j * x j := by
  simp only [ellOneDual, sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]

theorem norm_ellOneDual_le {d : ℕ} (t : Fin d → ℝ) (ht : ∀ j, |t j| ≤ 1) :
    ‖ellOneDual t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [ellOneDual_apply, Real.norm_eq_abs, one_mul, norm_ellOne]
  calc
    _ ≤ ∑ j, |t j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ht j)

theorem ellOne_scalar_bound {d n : ℕ} (x : Fin n → EllOne d) (M : ℝ)
    (hx : ∀ φ : EllOne d →L[ℝ] ℝ, ‖φ‖ ≤ 1 → ∑ i, |φ (x i)| ≤ M)
    (s : Fin n → ℝ) (t : Fin d → ℝ) (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ i, ∑ j, x i j * s i * t j| ≤ M := by
  have he : (∑ i, ∑ j, x i j * s i * t j) = ∑ i, s i * ellOneDual t (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [ellOneDual_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |s i * ellOneDual t (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ellOneDual t (x i)| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hs i)
    _ ≤ M := hx (ellOneDual t) (norm_ellOneDual_le t ht)

theorem ellOne_image_coordinate {d k : ℕ} (S : EllOne d →L[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EllOne d) (l : Fin k) :
    ∑ j, S (PiLp.single 1 j 1) l * x j = S x l := by
  let φ := (PiLp.proj 2 (fun _ : Fin k => ℝ) l).comp S
  have hx : ∑ j, x j • PiLp.single 1 j (1 : ℝ) = x := by
    simpa only [PiLp.basisFun_repr, PiLp.basisFun_apply] using
      (PiLp.basisFun 1 ℝ (Fin d)).sum_repr x
  change (∑ j, φ (PiLp.single 1 j 1) * x j) = φ x
  calc
    _ = φ (∑ j, x j • PiLp.single 1 j (1 : ℝ)) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = φ x := by rw [hx]

theorem normalized_sq_le {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) :
    ∑ l, (y l / ‖y‖) ^ 2 ≤ 1 := by
  simp only [div_pow]
  rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]
  by_cases hy : ‖y‖ = 0
  · simp [hy]
  · rw [div_self (pow_ne_zero _ hy)]

theorem oneSumming_of_matrix {G : ℝ} (hG : MatrixGrothendieckWith G)
    (d k : ℕ) (S : EllOne d →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    OneSummingWith S (G * ‖S‖) := by
  classical
  refine ⟨mul_nonneg hG.1 (norm_nonneg S), ?_⟩
  intro n x M hx
  by_cases hS : S = 0
  · simp [hS]
  have hSp : 0 < ‖S‖ := norm_pos_iff.mpr hS
  let u : Fin n → Fin k → ℝ := fun i l => S (x i) l / ‖S (x i)‖
  let v : Fin d → Fin k → ℝ := fun j l => S (PiLp.single 1 j 1) l / ‖S‖
  have hu (i : Fin n) : ∑ l, (u i l) ^ 2 ≤ 1 := normalized_sq_le (S (x i))
  have hv (j : Fin d) : ∑ l, (v j l) ^ 2 ≤ 1 := by
    simp only [v, div_pow]
    rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]
    apply (div_le_one (sq_pos_of_pos hSp)).mpr
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [PiLp.norm_single, norm_one, mul_one] using S.le_opNorm (PiLp.single 1 j (1 : ℝ))
  have hg := hG.2 n d k (fun i j => x i j) u v M hu hv (ellOne_scalar_bound x M hx)
  have he : (∑ i, ∑ j, x i j * (∑ l, u i l * v j l)) =
      (∑ i, ‖S (x i)‖) / ‖S‖ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ l, (u i l / ‖S‖) * (∑ j, S (PiLp.single 1 j 1) l * x i j) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [v]
        ring
      _ = ∑ l, (S (x i) l) ^ 2 / (‖S (x i)‖ * ‖S‖) := by
        simp_rw [ellOne_image_coordinate]
        apply Finset.sum_congr rfl
        intro l _
        dsimp only [u]
        ring
      _ = _ := by
        rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]
        by_cases hy : ‖S (x i)‖ = 0
        · simp [hy]
        · field_simp
  rw [he, abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hSp.le)] at hg
  have h := (div_le_iff₀ hSp).mp hg
  nlinarith

#print axioms oneSumming_of_matrix

end PL1.FiniteSumming

-- Final supplementary type audit: the matrix hypothesis remains visible.
#print PL1.FiniteSumming.MatrixGrothendieckWith
#check @PL1.FiniteSumming.twoSumming_of_matrix
#check @PL1.FiniteSumming.oneSumming_of_matrix


