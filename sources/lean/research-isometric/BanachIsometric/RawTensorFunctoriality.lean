import BanachIsometric.RawTensorHomogeneousGenerators
import BanachIsometric.EilenbergZilberUniversalEvaluation

/-! Identity and composition for the actual tensor-chain pushforwards, and
their action on the homogeneous universal generators. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism SingularEZ
open scoped TensorProduct

variable {X Y X' Y' X'' Y'' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace X''] [TopologicalSpace Y'']

theorem rawBigradedTensorMap_id :
    rawBigradedTensorMap (ContinuousMap.id X) (ContinuousMap.id Y) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawBigradedTensorMap (ContinuousMap.id X) (ContinuousMap.id Y)
      (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) = rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)
  simp only [rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, rawChainMap_id, LinearMap.id_apply]

theorem rawBigradedTensorMap_comp (f : C(X, X')) (g : C(Y, Y'))
    (f' : C(X', X'')) (g' : C(Y', Y'')) :
    rawBigradedTensorMap (f'.comp f) (g'.comp g) =
      (rawBigradedTensorMap f' g').comp (rawBigradedTensorMap f g) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawBigradedTensorMap (f'.comp f) (g'.comp g)
      (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
    rawBigradedTensorMap f' g' (rawBigradedTensorMap f g
      (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)))
  simp only [rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, rawChainMap_comp,
    LinearMap.comp_apply]

theorem rawBigradedTensorMapHomogeneous_id (n : ℕ) (c : rawTensorTotalDegree X Y n) :
    rawBigradedTensorMapHomogeneous (ContinuousMap.id X) (ContinuousMap.id Y) n c = c := by
  apply Subtype.ext
  change rawBigradedTensorMap (ContinuousMap.id X) (ContinuousMap.id Y) c.val = c.val
  rw [rawBigradedTensorMap_id, LinearMap.id_apply]

theorem rawBigradedTensorMapHomogeneous_comp (f : C(X, X')) (g : C(Y, Y'))
    (f' : C(X', X'')) (g' : C(Y', Y'')) (n : ℕ) (c : rawTensorTotalDegree X Y n) :
    rawBigradedTensorMapHomogeneous (f'.comp f) (g'.comp g) n c =
      rawBigradedTensorMapHomogeneous f' g' n (rawBigradedTensorMapHomogeneous f g n c) := by
  apply Subtype.ext
  exact LinearMap.congr_fun (rawBigradedTensorMap_comp f g f' g') c.val

def universalTensorHomogeneousGenerator {n p q : ℕ} (h : p + q = n) :
    rawTensorTotalDegree (Simplex p) (Simplex q) n :=
  rawTensorHomogeneousInclusion h
    (Finsupp.single (ContinuousMap.id (Simplex p)) 1 ⊗ₜ[ℚ]
      Finsupp.single (ContinuousMap.id (Simplex q)) 1)

theorem universalTensorHomogeneousGenerator_pushforward {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex X p) (τ : RawSingularSimplex Y q) :
    rawBigradedTensorMapHomogeneous σ τ n (universalTensorHomogeneousGenerator h) =
      rawTensorHomogeneousInclusion h (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1) := by
  apply Subtype.ext
  exact universalTensorGenerator_pushforward σ τ

end BanachIsometric.SingularAW
