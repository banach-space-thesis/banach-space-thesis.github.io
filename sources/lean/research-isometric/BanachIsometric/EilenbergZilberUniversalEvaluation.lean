import BanachIsometric.RawTensorMapChain
import BanachIsometric.RawAcyclicFillers

/-! Evaluating fixed universal simplex-product chains gives actual natural
bilinear crossproduct candidates. No boundary or inverse identity is assumed
for an arbitrary universal family in this file. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct DirectSum Topology

abbrev UniversalProductChains (n : ℕ) :=
  ∀ p q : ℕ, p + q = n → RawRationalChains (Simplex p × Simplex q) n

def universalTensorGenerator (p q : ℕ) : RawBigradedTensorChains (Simplex p) (Simplex q) :=
  rawTensorInclusion (Simplex p) (Simplex q) p q
    (Finsupp.single (ContinuousMap.id (Simplex p)) 1 ⊗ₜ[ℚ]
      Finsupp.single (ContinuousMap.id (Simplex q)) 1)

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

def universalCrossBilinear {n : ℕ} (U : UniversalProductChains n)
    (p q : ℕ) (h : p + q = n) :
    RawRationalChains X p →ₗ[ℚ] RawRationalChains Y q →ₗ[ℚ] RawRationalChains (X × Y) n :=
  Finsupp.linearCombination ℚ (fun σ => Finsupp.linearCombination ℚ
    (fun τ => rawChainMap (awProductMap σ τ) n (U p q h)))

def universalCrossBidegree {n : ℕ} (U : UniversalProductChains n)
    (p q : ℕ) (h : p + q = n) :
    RawTensorChains X Y p q →ₗ[ℚ] RawRationalChains (X × Y) n :=
  TensorProduct.lift (universalCrossBilinear U p q h)

theorem universalCrossBidegree_single {n p q : ℕ} (U : UniversalProductChains n)
    (h : p + q = n) (σ : RawSingularSimplex X p) (τ : RawSingularSimplex Y q) (a b : ℚ) :
    universalCrossBidegree U p q h (Finsupp.single σ a ⊗ₜ[ℚ] Finsupp.single τ b) =
      a • b • rawChainMap (awProductMap σ τ) n (U p q h) := by
  rw [universalCrossBidegree, TensorProduct.lift.tmul]
  simp only [universalCrossBilinear, Finsupp.linearCombination_single, LinearMap.smul_apply]

def universalCrossEvaluation {n : ℕ} (U : UniversalProductChains n) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawRationalChains (X × Y) n :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawRationalChains (X × Y) n) (fun ij =>
    if h : ij.1 + ij.2 = n then universalCrossBidegree U ij.1 ij.2 h else 0)

theorem universalCrossEvaluation_inclusion {n p q : ℕ} (U : UniversalProductChains n)
    (h : p + q = n) (c : RawTensorChains X Y p q) :
    universalCrossEvaluation U (rawTensorInclusion X Y p q c) = universalCrossBidegree U p q h c := by
  simp only [universalCrossEvaluation, rawTensorInclusion, DirectSum.toModule_lof, dif_pos h]

theorem universalCrossEvaluation_inclusion_of_ne {n p q : ℕ} (U : UniversalProductChains n)
    (h : p + q ≠ n) (c : RawTensorChains X Y p q) :
    universalCrossEvaluation U (rawTensorInclusion X Y p q c) = 0 := by
  simp only [universalCrossEvaluation, rawTensorInclusion, DirectSum.toModule_lof,
    dif_neg h, LinearMap.zero_apply]

theorem universalCrossEvaluation_generator {n p q : ℕ} (U : UniversalProductChains n)
    (h : p + q = n) : universalCrossEvaluation U (universalTensorGenerator p q) = U p q h := by
  rw [universalTensorGenerator, universalCrossEvaluation_inclusion U h, universalCrossBidegree_single]
  have hi : awProductMap (ContinuousMap.id (Simplex p)) (ContinuousMap.id (Simplex q)) =
      ContinuousMap.id (Simplex p × Simplex q) := rfl
  rw [hi, rawChainMap_id]
  simp only [LinearMap.id_apply, one_smul]

theorem universalTensorGenerator_pushforward (σ : RawSingularSimplex X p) (τ : RawSingularSimplex Y q) :
    rawBigradedTensorMap σ τ (universalTensorGenerator p q) =
      rawTensorInclusion X Y p q (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1) := by
  simp only [universalTensorGenerator, rawBigradedTensorMap_inclusion, TensorProduct.map_tmul,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ContinuousMap.comp_id]

theorem universalCrossEvaluation_naturality {n : ℕ} (U : UniversalProductChains n)
    (f : C(X, X')) (g : C(Y, Y')) :
    (universalCrossEvaluation (X := X') (Y := Y') U).comp (rawBigradedTensorMap f g) =
      (rawChainMap (awProductMap f g) n).comp (universalCrossEvaluation U) := by
  classical
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro τ
  apply LinearMap.ext_ring
  change universalCrossEvaluation U
      (rawBigradedTensorMap f g (rawTensorInclusion X Y p q
        (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1))) =
    rawChainMap (awProductMap f g) n (universalCrossEvaluation U
      (rawTensorInclusion X Y p q (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)))
  rw [rawBigradedTensorMap_inclusion]
  by_cases h : p + q = n
  · rw [TensorProduct.map_tmul]
    have hf : rawChainMap f p (Finsupp.single σ 1) = Finsupp.single (f.comp σ) 1 := by simp [rawChainMap]
    have hg : rawChainMap g q (Finsupp.single τ 1) = Finsupp.single (g.comp τ) 1 := by simp [rawChainMap]
    rw [hf, hg, universalCrossEvaluation_inclusion U h, universalCrossEvaluation_inclusion U h,
      universalCrossBidegree_single, universalCrossBidegree_single, one_smul, one_smul]
    have hpush := LinearMap.congr_fun
      (rawChainMap_comp (awProductMap σ τ) (awProductMap f g) n) (U p q h)
    have hprod : (awProductMap f g).comp (awProductMap σ τ) =
        awProductMap (f.comp σ) (g.comp τ) := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [hprod] at hpush
    simpa only [LinearMap.comp_apply, one_smul] using hpush
  · rw [universalCrossEvaluation_inclusion_of_ne U h,
      universalCrossEvaluation_inclusion_of_ne U h, map_zero]

end BanachIsometric.SingularEZ
