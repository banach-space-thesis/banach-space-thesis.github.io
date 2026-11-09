import BanachIsometric.SimplexRadialGauge

/-! Actual affine coordinates on the boundary of the standard simplex.
The level-one set is for the constructed simplex gauge, not a postulated
polyhedral model. Both inverse formulas and both continuities are proved. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology
open SphereGenerator NormedSpace

abbrev SimplexBoundary (n : ℕ) := {w : Simplex (n + 2) // ∃ i, w i = 0}
abbrev SimplexGaugeLevel (n : ℕ) :=
  {v : EuclideanSpace ℝ (Fin (n + 2)) // simplexGauge n v = 1}

def simplexBarycentricCoordinates (n : ℕ)
    (v : EuclideanSpace ℝ (Fin (n + 2))) (i : Fin (n + 3)) : ℝ :=
  simplexCenter n + simplexDirection n v i

theorem simplexBarycentricCoordinates_sum (n : ℕ)
    (v : EuclideanSpace ℝ (Fin (n + 2))) :
    ∑ i, simplexBarycentricCoordinates n v i = 1 := by
  simp only [simplexBarycentricCoordinates, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    simplexDirection_sum, add_zero, simplexCenter]
  have hn : (n + 3 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem simplexBarycentricCoordinates_centered (n : ℕ)
    (w : Simplex (n + 2)) :
    simplexBarycentricCoordinates n (centeredSimplexVector n w) = w := by
  funext i
  rw [simplexBarycentricCoordinates, simplexDirection_centered]
  ring

theorem simplexDirectionMax_level (n : ℕ) (v : SimplexGaugeLevel n) :
    simplexDirectionMax n v.val = simplexCenter n := by
  have hv := v.property
  change simplexDirectionMax n v.val / simplexCenter n = 1 at hv
  exact (div_eq_one_iff_eq (simplexCenter_pos n).ne').mp hv

def simplexGaugeLevelToBoundary (n : ℕ) : C(SimplexGaugeLevel n, SimplexBoundary n) where
  toFun v := ⟨⟨simplexBarycentricCoordinates n v.val, by
      constructor
      · intro i
        have hi := neg_simplexDirection_le_max n v.val i
        rw [simplexDirectionMax_level n v] at hi
        dsimp only [simplexBarycentricCoordinates]
        linarith
      · exact simplexBarycentricCoordinates_sum n v.val⟩, by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j : Fin (n + 3) => -simplexDirection n v.val j)
    change simplexDirectionMax n v.val = -simplexDirection n v.val i at hi
    rw [simplexDirectionMax_level n v] at hi
    refine ⟨i, ?_⟩
    change simplexCenter n + simplexDirection n v.val i = 0
    linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_const.add
      ((simplexDirection_continuous n i).comp continuous_subtype_val)

def simplexBoundaryToGaugeLevel (n : ℕ) : C(SimplexBoundary n, SimplexGaugeLevel n) where
  toFun w := ⟨centeredSimplexVector n w.val, simplexGauge_boundary n w.val w.property⟩
  continuous_toFun :=
    ((centeredSimplexVector n).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem simplexGaugeLevelToBoundary_toGaugeLevel (n : ℕ)
    (v : SimplexGaugeLevel n) :
    simplexBoundaryToGaugeLevel n (simplexGaugeLevelToBoundary n v) = v := by
  apply Subtype.ext
  ext j
  change simplexCenter n + v.val j - simplexCenter n = v.val j
  ring

@[simp] theorem simplexBoundaryToGaugeLevel_toBoundary (n : ℕ)
    (w : SimplexBoundary n) :
    simplexGaugeLevelToBoundary n (simplexBoundaryToGaugeLevel n w) = w := by
  apply Subtype.ext
  apply stdSimplex.ext
  exact simplexBarycentricCoordinates_centered n w.val

def simplexBoundaryGaugeLevelHomeomorph (n : ℕ) :
    SimplexBoundary n ≃ₜ SimplexGaugeLevel n where
  toFun := simplexBoundaryToGaugeLevel n
  invFun := simplexGaugeLevelToBoundary n
  left_inv := simplexBoundaryToGaugeLevel_toBoundary n
  right_inv := simplexGaugeLevelToBoundary_toGaugeLevel n
  continuous_toFun := (simplexBoundaryToGaugeLevel n).continuous
  continuous_invFun := (simplexGaugeLevelToBoundary n).continuous

end BanachIsometric.SingularPrism
