import BanachIsometric.SimplexBoundarySphere
import BanachIsometric.RadialHomeomorphism
import Mathlib.Topology.Order.Lattice

/-! The actual asymmetric polyhedral gauge of the centered simplex.
The auxiliary coordinates drop the first barycentric coordinate, so the
inverse linear direction prepends minus the sum. This keeps the original
Euclidean norm and makes the boundary-to-sphere parametrization explicit. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology
open SphereGenerator

def simplexDirection (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) : Fin (n + 3) → ℝ :=
  Fin.cons (-(∑ j, v j)) (fun j => v j)

@[simp] theorem simplexDirection_zero_coord (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    simplexDirection n v 0 = -(∑ j, v j) := rfl

@[simp] theorem simplexDirection_succ (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2)))
    (j : Fin (n + 2)) : simplexDirection n v j.succ = v j := rfl

theorem simplexDirection_sum (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    ∑ i, simplexDirection n v i = 0 := by
  rw [Fin.sum_univ_succ]
  simp

theorem simplexDirection_continuous (n : ℕ) (i : Fin (n + 3)) :
    Continuous (fun v : EuclideanSpace ℝ (Fin (n + 2)) => simplexDirection n v i) := by
  induction i using Fin.cases with
  | zero => exact (continuous_finset_sum _ fun j _ =>
      PiLp.continuous_apply 2 (fun _ : Fin (n + 2) => ℝ) j).neg
  | succ j => exact PiLp.continuous_apply 2 (fun _ : Fin (n + 2) => ℝ) j

theorem simplexDirection_smul (n : ℕ) (t : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 2))) (i : Fin (n + 3)) :
    simplexDirection n (t • v) i = t * simplexDirection n v i := by
  induction i using Fin.cases with
  | zero => simp [← Finset.mul_sum]
  | succ j => simp

def simplexDirectionMax (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => -simplexDirection n v i)

theorem neg_simplexDirection_le_max (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 3)) : -simplexDirection n v i ≤ simplexDirectionMax n v := by
  exact Finset.le_sup' (fun j => -simplexDirection n v j) (Finset.mem_univ i)

@[simp] theorem simplexDirectionMax_zero (n : ℕ) : simplexDirectionMax n 0 = 0 := by
  have hd : ∀ i : Fin (n + 3), simplexDirection n 0 i = 0 := by
    intro i
    induction i using Fin.cases <;> simp
  simp [simplexDirectionMax, hd]

theorem simplexDirectionMax_pos (n : ℕ) {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : v ≠ 0) : 0 < simplexDirectionMax n v := by
  by_contra h
  have hm : simplexDirectionMax n v ≤ 0 := le_of_not_gt h
  have hd : ∀ i, 0 ≤ simplexDirection n v i := by
    intro i
    linarith [neg_simplexDirection_le_max n v i]
  have hz : ∀ i, simplexDirection n v i = 0 := by
    intro i
    exact congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hd).mp (simplexDirection_sum n v)) i
  apply hv
  ext j
  exact hz j.succ

theorem simplexDirectionMax_nonneg (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    0 ≤ simplexDirectionMax n v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (simplexDirectionMax_pos n hv).le

theorem simplexDirectionMax_continuous (n : ℕ) : Continuous (simplexDirectionMax n) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => (simplexDirection_continuous n i).neg)

theorem simplexDirectionMax_smul_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : EuclideanSpace ℝ (Fin (n + 2))) :
    simplexDirectionMax n (t • v) = t * simplexDirectionMax n v := by
  dsimp only [simplexDirectionMax]
  trans Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (n + 3) => t * (-simplexDirection n v i))
  · congr 1
    funext i
    rw [simplexDirection_smul]
    ring
  · exact (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty
      (f := fun i : Fin (n + 3) => -simplexDirection n v i)
      (fun a : ℝ => t * a) (fun a b => mul_max_of_nonneg a b ht)).symm

def simplexGauge (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) : ℝ :=
  simplexDirectionMax n v / simplexCenter n

theorem simplexGauge_homogeneous (n : ℕ) :
    IsDefinitePositiveHomogeneous (simplexGauge n) where
  nonneg v := div_nonneg (simplexDirectionMax_nonneg n v) (simplexCenter_pos n).le
  eq_zero_iff v := by
    constructor
    · intro h
      by_contra hv
      exact (div_pos (simplexDirectionMax_pos n hv) (simplexCenter_pos n)).ne' h
    · rintro rfl
      simp [simplexGauge]
  smul_nonneg t ht v := by
    simp only [simplexGauge, simplexDirectionMax_smul_nonneg n t ht, mul_div_assoc]

theorem simplexGauge_continuous (n : ℕ) : Continuous (simplexGauge n) :=
  (simplexDirectionMax_continuous n).div_const _

theorem simplexDirection_centered (n : ℕ) (w : Simplex (n + 2)) (i : Fin (n + 3)) :
    simplexDirection n (centeredSimplexVector n w) i = w i - simplexCenter n := by
  induction i using Fin.cases with
  | zero =>
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succ] at hs
    simp only [simplexDirection_zero_coord, centeredSimplexVector_apply,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    dsimp [simplexCenter]
    have hn : (n + 3 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    nlinarith
  | succ j => rfl

theorem simplexGauge_boundary (n : ℕ) (w : Simplex (n + 2))
    (hb : ∃ i, w i = 0) : simplexGauge n (centeredSimplexVector n w) = 1 := by
  obtain ⟨i, hi⟩ := hb
  have hm : simplexDirectionMax n (centeredSimplexVector n w) = simplexCenter n := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      rw [simplexDirection_centered]
      linarith [stdSimplex.zero_le w j]
    · have hj := neg_simplexDirection_le_max n (centeredSimplexVector n w) i
      rw [simplexDirection_centered, hi] at hj
      simpa using hj
  rw [simplexGauge, hm, div_self (simplexCenter_pos n).ne']

end BanachIsometric.SingularPrism
