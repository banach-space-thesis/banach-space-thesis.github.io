import BanachIsometric.AffineBarycentricSubdivision
import Mathlib.Analysis.Normed.Module.Convex

/-! Quantitative mesh contraction at the actual barycenter of a simplex.
The norm is the given norm of the ambient real normed space. -/

noncomputable section
namespace BanachIsometric.SingularPrism

def barycentricMeshFactor (n : ℕ) : ℝ := n / (n + 1)

theorem barycentricMeshFactor_nonneg (n : ℕ) : 0 ≤ barycentricMeshFactor n := by
  exact div_nonneg (by positivity) (by positivity)

theorem barycentricMeshFactor_lt_one (n : ℕ) : barycentricMeshFactor n < 1 := by
  unfold barycentricMeshFactor
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem barycentricMeshFactor_le_succ (n : ℕ) :
    barycentricMeshFactor n ≤ barycentricMeshFactor (n + 1) := by
  unfold barycentricMeshFactor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_affineBarycenter_vertex_le {n : ℕ} (v : Fin (n + 1) → E)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) (i : Fin (n + 1)) :
    dist (affineBarycenter v) (v i) ≤ barycentricMeshFactor n * D := by
  classical
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hform : affineBarycenter v - v i =
      (n + 1 : ℝ)⁻¹ • ∑ j, (v j - v i) := by
    simp only [affineBarycenter, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hn, one_smul]
  have hsum : (∑ j, ‖v j - v i‖) ≤ (n : ℝ) * D := by
    calc
      _ ≤ ∑ j : Fin (n + 1), if j = i then 0 else D := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · simp [hji]
        · simpa only [if_neg hji, dist_eq_norm] using hD j i
      _ = ∑ j : Fin (n + 1), (D - if j = i then D else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = (n + 1 : ℝ) * D - D := by
        simp [Finset.sum_sub_distrib]
      _ = (n : ℝ) * D := by ring
  calc
    _ = ‖(n + 1 : ℝ)⁻¹ • ∑ j, (v j - v i)‖ := by rw [dist_eq_norm, hform]
    _ = (n + 1 : ℝ)⁻¹ * ‖∑ j, (v j - v i)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ j, ‖v j - v i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n + 1 : ℝ)⁻¹ * ((n : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = barycentricMeshFactor n * D := by simp only [barycentricMeshFactor, div_eq_mul_inv]; ring

theorem dist_affineBarycenter_convexHull_le {n : ℕ} (v : Fin (n + 1) → E)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    dist (affineBarycenter v) x ≤ barycentricMeshFactor n * D := by
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := convexHull_exists_dist_ge hx (affineBarycenter v)
  calc
    _ = dist x (affineBarycenter v) := dist_comm _ _
    _ ≤ dist (v i) (affineBarycenter v) := hi
    _ = dist (affineBarycenter v) (v i) := dist_comm _ _
    _ ≤ _ := dist_affineBarycenter_vertex_le v D hD i

end BanachIsometric.SingularPrism
