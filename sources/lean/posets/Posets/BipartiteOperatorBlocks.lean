import Posets.BipartiteOperatorSpaces
import Posets.IdealCounts

/-! The block structure of the complete bipartite incidence algebra. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P Q : Type*}

local instance completeBipartiteOrder : PartialOrder (P ⊕ Q) :=
  bipartiteOrder (fun _ _ => True)

abbrev BipartiteAlgebra (𝕜 : Type) [RCLike 𝕜] (P Q : Type*) :=
  incidenceSubalgebra 𝕜 (P ⊕ Q)

@[simp] theorem sumCZeroInl_unit (p : P) :
    sumCZeroInl (Q := Q) (unitVector 𝕜 p) = unitVector 𝕜 (Sum.inl p) := by
  ext x
  rcases x with ⟨s | t⟩ <;> simp

@[simp] theorem sumCZeroInr_unit (q : Q) :
    sumCZeroInr (P := P) (unitVector 𝕜 q) = unitVector 𝕜 (Sum.inr q) := by
  ext x
  rcases x with ⟨s | t⟩ <;> simp

def bipartiteLeftBlock (T : BipartiteAlgebra 𝕜 P Q) : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P :=
  sumCZeroFst.comp (T.val.comp sumCZeroInl)
def bipartiteUpperBlock (T : BipartiteAlgebra 𝕜 P Q) : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P :=
  sumCZeroFst.comp (T.val.comp sumCZeroInr)
def bipartiteLowerBlock (T : BipartiteAlgebra 𝕜 P Q) : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 Q :=
  sumCZeroSnd.comp (T.val.comp sumCZeroInl)
def bipartiteRightBlock (T : BipartiteAlgebra 𝕜 P Q) : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 Q :=
  sumCZeroSnd.comp (T.val.comp sumCZeroInr)

theorem bipartiteLowerBlock_eq_zero (T : BipartiteAlgebra 𝕜 P Q) :
    bipartiteLowerBlock T = 0 := by
  apply ContinuousLinearMap.ext_on discreteUnit_dense_span
  rintro _ ⟨p, rfl⟩
  rw [discreteUnit_eq_unitVector]
  ext q
  simpa [bipartiteLowerBlock, scalarMatrix, sumLeftEmbedding, sumRightEmbedding] using
    T.property (Sum.inr q.val) (Sum.inl p.val) (by exact not_false)

theorem scalarMatrix_norm_le (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s t : P) :
    ‖scalarMatrix 𝕜 T s t‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (unitVector 𝕜 t)‖ := (T _).toBCF.norm_coe_le_norm _
    _ ≤ ‖T‖ * ‖unitVector 𝕜 t‖ := T.le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (bimodule_unitVector_norm_le _) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

def bipartiteLeftDiagonal (T : BipartiteAlgebra 𝕜 P Q) : Discrete P →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => scalarMatrix 𝕜 T.val (Sum.inl p.val) (Sum.inl p.val)) ‖T.val‖
    (fun p => scalarMatrix_norm_le T.val (Sum.inl p.val) (Sum.inl p.val))
def bipartiteRightDiagonal (T : BipartiteAlgebra 𝕜 P Q) : Discrete Q →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun q => scalarMatrix 𝕜 T.val (Sum.inr q.val) (Sum.inr q.val)) ‖T.val‖
    (fun q => scalarMatrix_norm_le T.val (Sum.inr q.val) (Sum.inr q.val))

theorem bipartiteLeftBlock_eq_multiplier (T : BipartiteAlgebra 𝕜 P Q) :
    bipartiteLeftBlock T = multiplicationOperator (bipartiteLeftDiagonal T) := by
  apply ContinuousLinearMap.ext_on discreteUnit_dense_span
  rintro _ ⟨p, rfl⟩
  rw [discreteUnit_eq_unitVector]
  ext q
  by_cases h : q.val = p.val
  · cases p; cases q; dsimp at h; subst_vars
    simp [bipartiteLeftBlock, bipartiteLeftDiagonal, scalarMatrix, sumLeftEmbedding]
  · have hz := T.property (Sum.inl q.val) (Sum.inl p.val) h
    simpa [bipartiteLeftBlock, scalarMatrix, sumLeftEmbedding, h] using hz

theorem bipartiteRightBlock_eq_multiplier (T : BipartiteAlgebra 𝕜 P Q) :
    bipartiteRightBlock T = multiplicationOperator (bipartiteRightDiagonal T) := by
  apply ContinuousLinearMap.ext_on discreteUnit_dense_span
  rintro _ ⟨p, rfl⟩
  rw [discreteUnit_eq_unitVector]
  ext q
  by_cases h : q.val = p.val
  · cases p; cases q; dsimp at h; subst_vars
    simp [bipartiteRightBlock, bipartiteRightDiagonal, scalarMatrix, sumRightEmbedding]
  · have hz := T.property (Sum.inr q.val) (Sum.inr p.val) h
    simpa [bipartiteRightBlock, scalarMatrix, sumRightEmbedding, h] using hz

theorem bipartite_fst_apply (T : BipartiteAlgebra 𝕜 P Q) (f : CZeroOn 𝕜 (P ⊕ Q)) :
    sumCZeroFst (T.val f) =
      multiplicationOperator (bipartiteLeftDiagonal T) (sumCZeroFst f) +
      bipartiteUpperBlock T (sumCZeroSnd f) := by
  conv_lhs => rw [← sumCZero_decomposition f]
  simp only [map_add]
  rw [← bipartiteLeftBlock_eq_multiplier]
  rfl

theorem bipartite_snd_apply (T : BipartiteAlgebra 𝕜 P Q) (f : CZeroOn 𝕜 (P ⊕ Q)) :
    sumCZeroSnd (T.val f) = multiplicationOperator (bipartiteRightDiagonal T) (sumCZeroSnd f) := by
  conv_lhs => rw [← sumCZero_decomposition f]
  simp only [map_add]
  change bipartiteLowerBlock T (sumCZeroFst f) +
    bipartiteRightBlock T (sumCZeroSnd f) = _
  rw [bipartiteLowerBlock_eq_zero, ContinuousLinearMap.zero_apply, zero_add,
    bipartiteRightBlock_eq_multiplier]

end Posets

