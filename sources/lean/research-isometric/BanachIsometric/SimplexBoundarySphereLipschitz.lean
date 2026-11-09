import BanachIsometric.SimplexBoundarySphereHomeomorph
import BanachIsometric.RadialHomeomorphismLipschitz

/-! The inverse radial boundary-simplex chart is Lipschitz in its actual
subspace metrics. Its gauge is a maximum of finitely many linear functionals. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric SphereGenerator
open scoped NNReal

def simplexDirectionLinear (n : ℕ) (i : Fin (n + 3)) :
    EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] ℝ where
  toFun v := simplexDirection n v i
  map_add' x y := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · rfl
  map_smul' a x := simplexDirection_smul n a x i

theorem exists_lipschitz_simplexDirectionMax (n : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (simplexDirectionMax n) := by
  let L (i : Fin (n + 3)) := -(simplexDirectionLinear n i).toContinuousLinearMap
  let C : ℝ≥0 := ∑ i, ‖L i‖₊
  have hcoord (i : Fin (n + 3)) (x y : EuclideanSpace ℝ (Fin (n + 2))) :
      |L i x - L i y| ≤ (C : ℝ) * dist x y := by
    have hle : ‖L i‖₊ ≤ C := Finset.single_le_sum
      (f := fun j => ‖L j‖₊) (fun _ _ => zero_le _) (Finset.mem_univ i)
    have h := (L i).lipschitz.dist_le_mul x y
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hle) dist_nonneg)
  have hsub (x y : EuclideanSpace ℝ (Fin (n + 2))) :
      simplexDirectionMax n x - simplexDirectionMax n y ≤ (C : ℝ) * dist x y := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j : Fin (n + 3) => -simplexDirection n x j)
    change simplexDirectionMax n x = L i x at hi
    rw [hi]
    exact (sub_le_sub_left (neg_simplexDirection_le_max n y i) _).trans
      ((le_abs_self _).trans (hcoord i x y))
  refine ⟨C, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  rw [Real.dist_eq, abs_le]
  refine ⟨?_, hsub x y⟩
  have h := hsub y x
  rw [dist_comm y x] at h
  linarith

theorem exists_lipschitz_simplexGauge (n : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (simplexGauge n) := by
  obtain ⟨C, hC⟩ := exists_lipschitz_simplexDirectionMax n
  let A : ℝ →L[ℝ] ℝ := (simplexCenter n)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have he : simplexGauge n = A ∘ simplexDirectionMax n := by
    funext v
    change simplexDirectionMax n v / simplexCenter n = (simplexCenter n)⁻¹ * simplexDirectionMax n v
    ring
  rw [he]
  exact ⟨_, A.lipschitz.comp hC⟩

theorem exists_lipschitz_simplexBoundarySphereHomeomorph_symm (n : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (simplexBoundarySphereHomeomorph n).symm := by
  obtain ⟨L, hL⟩ := exists_lipschitz_simplexGauge n
  obtain ⟨K, hK⟩ := exists_lipschitz_radialGaugeMap (simplexGauge_homogeneous n) hL.lipschitzOnWith
  let A : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] (Fin (n + 3) → ℝ) :=
    ContinuousLinearMap.pi (fun i => (simplexDirectionLinear n i).toContinuousLinearMap)
  let b : Fin (n + 3) → ℝ := fun _ => simplexCenter n
  let f : Sph (n + 1) → (Fin (n + 3) → ℝ) := fun u =>
    b + A (radialGaugeMap (simplexGauge n) u.val)
  have hf : LipschitzWith _ f := (LipschitzWith.const b).add
    (A.lipschitz.comp (hK.comp (LipschitzWith.subtype_val _)))
  have he (u : Sph (n + 1)) : ((simplexBoundarySphereHomeomorph n).symm u).val.val = f u := rfl
  refine ⟨0 + ‖A‖₊ * (K * 1), LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change dist (((simplexBoundarySphereHomeomorph n).symm u).val.val)
    (((simplexBoundarySphereHomeomorph n).symm v).val.val) ≤ _
  rw [he, he]
  exact hf.dist_le_mul u v

end BanachIsometric.SingularPrism
