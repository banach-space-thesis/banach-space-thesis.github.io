import NonCalkinAlgebra.MatrixDensityLower
import NonCalkinAlgebra.MetricCardinality

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
variable (D : Type) [NormedRing D] [NormedAlgebra ℂ D]

def finiteMatrixCodeValue (L : List (ℕ × ℕ × D)) :
    CoefficientSpace D →L[ℂ] CoefficientSpace D :=
  (L.map (fun v => theta D v.1 v.2.1 v.2.2)).sum

@[simp] theorem finiteMatrixCodeValue_nil : finiteMatrixCodeValue D [] = 0 := rfl

@[simp] theorem finiteMatrixCodeValue_cons (v : ℕ × ℕ × D) (L : List (ℕ × ℕ × D)) :
    finiteMatrixCodeValue D (v :: L) = theta D v.1 v.2.1 v.2.2 + finiteMatrixCodeValue D L := rfl

theorem finiteMatrixCodeValue_mem (L : List (ℕ × ℕ × D)) :
    finiteMatrixCodeValue D L ∈ finiteMatrixSpan D := by
  induction L with
  | nil => exact (finiteMatrixSpan D).zero_mem
  | cons v L ih =>
    exact (finiteMatrixSpan D).add_mem (theta_mem_finiteMatrixSpan D v.1 v.2.1 v.2.2) ih

theorem finiteMatrixCodeValue_append (L M : List (ℕ × ℕ × D)) :
    finiteMatrixCodeValue D (L ++ M) = finiteMatrixCodeValue D L + finiteMatrixCodeValue D M := by
  simp only [finiteMatrixCodeValue, List.map_append, List.sum_append]

theorem finiteMatrixCodeValue_smul (c : ℂ) (L : List (ℕ × ℕ × D)) :
    finiteMatrixCodeValue D (L.map fun v => (v.1, v.2.1, c • v.2.2)) =
      c • finiteMatrixCodeValue D L := by
  induction L with
  | nil => simp only [List.map_nil, finiteMatrixCodeValue_nil, smul_zero]
  | cons v L ih =>
    simp only [List.map_cons, finiteMatrixCodeValue_cons, theta_smul, ih, smul_add]

theorem exists_finiteMatrixCode {T : CoefficientSpace D →L[ℂ] CoefficientSpace D}
    (hT : T ∈ finiteMatrixSpan D) : ∃ L : List (ℕ × ℕ × D), finiteMatrixCodeValue D L = T := by
  change T ∈ Submodule.span ℂ (matrixGenerators D) at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨i, j, d, rfl⟩ := hT
    exact ⟨[(i, j, d)], by simp only [finiteMatrixCodeValue_cons, finiteMatrixCodeValue_nil, add_zero]⟩
  | zero => exact ⟨[], rfl⟩
  | add T U hT hU ihT ihU =>
    obtain ⟨L, rfl⟩ := ihT
    obtain ⟨M, rfl⟩ := ihU
    exact ⟨L ++ M, finiteMatrixCodeValue_append D L M⟩
  | smul c T hT ih =>
    obtain ⟨L, rfl⟩ := ih
    exact ⟨L.map (fun v => (v.1, v.2.1, c • v.2.2)), finiteMatrixCodeValue_smul D c L⟩

theorem finiteMatrixSpan_cardinal_le_continuum (hD : Cardinal.mk D ≤ Cardinal.continuum) :
    Cardinal.mk (finiteMatrixSpan D) ≤ Cardinal.continuum := by
  let F : List (ℕ × ℕ × D) → finiteMatrixSpan D :=
    fun L => ⟨finiteMatrixCodeValue D L, finiteMatrixCodeValue_mem D L⟩
  have hsurj : Function.Surjective F := by
    intro T
    obtain ⟨L, hL⟩ := exists_finiteMatrixCode D T.property
    exact ⟨L, Subtype.ext hL⟩
  have hnat : Cardinal.mk ℕ ≤ Cardinal.continuum := by
    simpa only [Cardinal.mk_nat] using Cardinal.aleph0_le_continuum
  have hcode : Cardinal.mk (ℕ × ℕ × D) ≤ Cardinal.continuum :=
    cardinal_prod_le_continuum hnat (cardinal_prod_le_continuum hnat hD)
  exact (Cardinal.mk_le_of_surjective hsurj).trans
    ((Cardinal.mk_list_le_max (ℕ × ℕ × D)).trans (max_le Cardinal.aleph0_le_continuum hcode))

theorem matrixClosure_cardinal_le_continuum (hD : Cardinal.mk D ≤ Cardinal.continuum) :
    Cardinal.mk (matrixClosure D) ≤ Cardinal.continuum :=
  cardinal_closure_le_continuum (finiteMatrixSpan D :
    Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) (finiteMatrixSpan_cardinal_le_continuum D hD)

theorem matrixAlgebra_cardinal_le_continuum (hD : Cardinal.mk D ≤ Cardinal.continuum) :
    Cardinal.mk (matrixAlgebra D) ≤ Cardinal.continuum := by
  let F : ℂ × matrixClosure D → matrixAlgebra D := fun v =>
    ⟨v.1 • 1 + v.2.val,
      (mem_unitizedMatrixSubspace D _).mpr ⟨v.1, v.2.val, v.2.property, rfl⟩⟩
  have hsurj : Function.Surjective F := by
    intro a
    obtain ⟨c, j, hj, heq⟩ := (mem_unitizedMatrixSubspace D a).mp a.property
    exact ⟨(c, ⟨j, hj⟩), Subtype.ext heq.symm⟩
  exact (Cardinal.mk_le_of_surjective hsurj).trans
    (cardinal_prod_le_continuum Cardinal.mk_complex.le (matrixClosure_cardinal_le_continuum D hD))

variable [NormOneClass D]

/-- Exact continuum density in Theorem 1.1. The metric cardinal estimate
above is an alternative to the paper's rational finite-combination count. -/
theorem matrixAlgebra_density_continuum (hD : HasDensityCharacter D Cardinal.continuum) :
    HasDensityCharacter (matrixAlgebra D) Cardinal.continuum := by
  have hupper := matrixAlgebra_cardinal_le_continuum D
    (cardinal_le_continuum_of_density_continuum hD)
  have hlower := matrixAlgebra_density_lower_bound D hD Set.univ dense_univ
  rw [Cardinal.mk_univ] at hlower
  exact ⟨⟨Set.univ, dense_univ, by rw [Cardinal.mk_univ]; exact le_antisymm hupper hlower⟩,
    matrixAlgebra_density_lower_bound D hD⟩

end NonCalkinAlgebra
