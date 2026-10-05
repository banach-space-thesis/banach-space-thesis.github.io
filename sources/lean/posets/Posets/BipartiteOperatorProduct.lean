import Posets.BipartiteOperatorNorms

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P Q : Type*}

local instance productCompleteBipartiteOrder : PartialOrder (P ⊕ Q) := completeBipartiteOrder
local instance productBipartiteHMul : HMul (BipartiteAlgebra 𝕜 P Q) (BipartiteAlgebra 𝕜 P Q)
    (BipartiteAlgebra 𝕜 P Q) :=
  ⟨fun T S => ⟨T.val * S.val, incidenceOperators_mul T.property S.property⟩⟩

def bipartiteLeftDiagonalMap : BipartiteAlgebra 𝕜 P Q →ₗ[𝕜] (Discrete P →ᵇ 𝕜) where
  toFun := bipartiteLeftDiagonal
  map_add' := by intro T S; ext p; rfl
  map_smul' := by intro a T; ext p; rfl

def bipartiteRightDiagonalMap : BipartiteAlgebra 𝕜 P Q →ₗ[𝕜] (Discrete Q →ᵇ 𝕜) where
  toFun := bipartiteRightDiagonal
  map_add' := by intro T S; ext p; rfl
  map_smul' := by intro a T; ext p; rfl

def bipartiteUpperBlockMap : BipartiteAlgebra 𝕜 P Q →ₗ[𝕜] (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) where
  toFun := bipartiteUpperBlock
  map_add' := by intro T S; ext f p; rfl
  map_smul' := by intro a T; ext f p; rfl

theorem bipartiteLeftBlock_mul (T S : BipartiteAlgebra 𝕜 P Q) :
    bipartiteLeftBlock (T * S : BipartiteAlgebra 𝕜 P Q) =
      (multiplicationOperator (bipartiteLeftDiagonal T)).comp
        (multiplicationOperator (bipartiteLeftDiagonal S)) := by
  ext f p
  change sumCZeroFst (T.val (S.val (sumCZeroInl f))) p = _
  rw [bipartite_fst_apply, bipartite_fst_apply, bipartite_snd_apply]
  simp only [sumCZeroFst_inl, sumCZeroSnd_inl, map_zero, add_zero]
  rfl

theorem bipartiteRightBlock_mul (T S : BipartiteAlgebra 𝕜 P Q) :
    bipartiteRightBlock (T * S : BipartiteAlgebra 𝕜 P Q) =
      (multiplicationOperator (bipartiteRightDiagonal T)).comp
        (multiplicationOperator (bipartiteRightDiagonal S)) := by
  ext f p
  change sumCZeroSnd (T.val (S.val (sumCZeroInr f))) p = _
  rw [bipartite_snd_apply, bipartite_snd_apply]
  simp only [sumCZeroSnd_inr]
  rfl

theorem bipartiteLeftDiagonal_mul (T S : BipartiteAlgebra 𝕜 P Q) :
    bipartiteLeftDiagonal (T * S : BipartiteAlgebra 𝕜 P Q) = bipartiteLeftDiagonal T * bipartiteLeftDiagonal S := by
  ext p
  have h := congrArg (fun A : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P =>
    A (unitVector 𝕜 p.val) p) (bipartiteLeftBlock_mul T S)
  rw [bipartiteLeftBlock_eq_multiplier] at h
  simpa using h

theorem bipartiteRightDiagonal_mul (T S : BipartiteAlgebra 𝕜 P Q) :
    bipartiteRightDiagonal (T * S : BipartiteAlgebra 𝕜 P Q) = bipartiteRightDiagonal T * bipartiteRightDiagonal S := by
  ext p
  have h := congrArg (fun A : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 Q =>
    A (unitVector 𝕜 p.val) p) (bipartiteRightBlock_mul T S)
  rw [bipartiteRightBlock_eq_multiplier] at h
  simpa using h

theorem bipartiteUpperBlock_mul (T S : BipartiteAlgebra 𝕜 P Q) :
    bipartiteUpperBlock (T * S : BipartiteAlgebra 𝕜 P Q) =
      (multiplicationOperator (bipartiteLeftDiagonal T)).comp (bipartiteUpperBlock S) +
      (bipartiteUpperBlock T).comp (multiplicationOperator (bipartiteRightDiagonal S)) := by
  ext f p
  change sumCZeroFst (T.val (S.val (sumCZeroInr f))) p = _
  rw [bipartite_fst_apply, bipartite_fst_apply, bipartite_snd_apply]
  simp only [sumCZeroFst_inr, sumCZeroSnd_inr, map_zero, zero_add]
  rfl

end Posets






