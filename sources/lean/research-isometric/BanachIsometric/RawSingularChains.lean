import BanachIsometric.SingularPrismGeometry
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Concrete rational singular chains on the literal real standard simplex.
The differential is the actual alternating sum of precomposition by faces.
Its square-zero proof uses the finite-index pairing from Mathlib's
`AlternatingFaceMapComplex` (Joël Riou, Adam Topaz, Johan Commelin, Apache 2.0),
instantiated here on the actual simplex-face maps. A later explicit coordinate
isomorphism compares this model to the NNReal-simplex singular functor.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

abbrev RawSingularSimplex (X : Type*) [TopologicalSpace X] (n : ℕ) := C(Simplex n, X)
abbrev RawRationalChains (X : Type*) [TopologicalSpace X] (n : ℕ) := RawSingularSimplex X n →₀ ℚ

def rawFace {n : ℕ} (i : Fin (n + 2)) :
    RawRationalChains X (n + 1) →ₗ[ℚ] RawRationalChains X n :=
  Finsupp.lmapDomain ℚ ℚ (fun simplex => simplex.comp (face i))

def rawBoundary (n : ℕ) : RawRationalChains X (n + 1) →ₗ[ℚ] RawRationalChains X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • rawFace i

@[simp] theorem rawFace_single {n : ℕ} (i : Fin (n + 2))
    (simplex : RawSingularSimplex X (n + 1)) (a : ℚ) :
    rawFace i (Finsupp.single simplex a) = Finsupp.single (simplex.comp (face i)) a := by
  simp [rawFace]

theorem rawBoundary_single (n : ℕ) (simplex : RawSingularSimplex X (n + 1)) (a : ℚ) :
    rawBoundary n (Finsupp.single simplex a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (simplex.comp (face i)) a := by
  simp only [rawBoundary, LinearMap.sum_apply, LinearMap.smul_apply, rawFace_single]

theorem face_face {n : ℕ} (i j : Fin (n + 2)) (h : i ≤ j) :
    (face j.succ).comp (face i) = (face i.castSucc).comp (face j) := by
  have h' : (i : ℕ) ≤ (j : ℕ) := h
  have he : j.succ.succAbove ∘ i.succAbove = i.castSucc.succAbove ∘ j.succAbove := by
    funext k
    apply Fin.ext
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_iff_val_lt_val,
      Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> simp_all <;> omega
  change (simplexMap j.succ.succAbove).comp (simplexMap i.succAbove) =
    (simplexMap i.castSucc.succAbove).comp (simplexMap j.succAbove)
  rw [simplexMap_comp, simplexMap_comp, he]

theorem rawFace_comp {n : ℕ} (i j : Fin (n + 2)) (h : i ≤ j) :
    (rawFace (X := X) i).comp (rawFace j.succ) =
      (rawFace j).comp (rawFace i.castSucc) := by
  simp only [rawFace, ← Finsupp.lmapDomain_comp]
  congr 1
  funext simplex
  exact congrArg (fun f => simplex.comp f) (face_face i j h)

theorem rawBoundary_squared (n : ℕ) :
    (rawBoundary (X := X) n).comp (rawBoundary (n + 1)) = 0 := by
  classical
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, rawBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul, Finset.smul_sum, smul_smul, LinearMap.zero_apply]
  rw [Finset.sum_comm, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.coe_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero'] at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.coe_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      exact mul_comm _ _
    · have hji : Fin.castLT j (lt_of_le_of_lt (Finset.mem_filter.mp hij).right i.is_lt) ≤ i :=
        (Finset.mem_filter.mp hij).right
      simpa only [φ, Fin.castSucc_castLT, LinearMap.comp_apply] using
        (LinearMap.congr_fun (rawFace_comp (X := X) _ i hji) c).symm

def rawChainMap (f : C(X, Y)) (n : ℕ) : RawRationalChains X n →ₗ[ℚ] RawRationalChains Y n :=
  Finsupp.lmapDomain ℚ ℚ (fun simplex => f.comp simplex)

theorem rawChainMap_boundary (f : C(X, Y)) (n : ℕ) :
    (rawBoundary (X := Y) n).comp (rawChainMap f (n + 1)) =
      (rawChainMap f n).comp (rawBoundary n) := by
  apply LinearMap.ext
  intro c
  simp only [rawBoundary, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have he : (rawFace (X := Y) i).comp (rawChainMap f (n + 1)) =
      (rawChainMap f n).comp (rawFace i) := by
    simp only [rawFace, rawChainMap, ← Finsupp.lmapDomain_comp]
    rfl
  exact LinearMap.congr_fun he c

end BanachIsometric.SingularPrism
