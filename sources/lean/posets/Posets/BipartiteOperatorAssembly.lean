import Posets.BipartiteOperatorNorms
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P Q : Type*}

local instance assemblyCompleteBipartiteOrder : PartialOrder (P ⊕ Q) := completeBipartiteOrder

@[simp] theorem sumCZeroFst_unit_inl (p : P) :
    sumCZeroFst (Q := Q) (unitVector 𝕜 (Sum.inl p)) = unitVector 𝕜 p := by
  rw [← sumCZeroInl_unit, sumCZeroFst_inl]
@[simp] theorem sumCZeroSnd_unit_inl (p : P) :
    sumCZeroSnd (Q := Q) (unitVector 𝕜 (Sum.inl p)) = 0 := by
  rw [← sumCZeroInl_unit, sumCZeroSnd_inl]
@[simp] theorem sumCZeroFst_unit_inr (q : Q) :
    sumCZeroFst (P := P) (unitVector 𝕜 (Sum.inr q)) = 0 := by
  rw [← sumCZeroInr_unit, sumCZeroFst_inr]
@[simp] theorem sumCZeroSnd_unit_inr (q : Q) :
    sumCZeroSnd (P := P) (unitVector 𝕜 (Sum.inr q)) = unitVector 𝕜 q := by
  rw [← sumCZeroInr_unit, sumCZeroSnd_inr]

def bipartiteAssembleOperator (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜) :
    CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q) :=
  sumCZeroInl.comp ((multiplicationOperator a).comp sumCZeroFst) +
    sumCZeroInl.comp (T.comp sumCZeroSnd) +
    sumCZeroInr.comp ((multiplicationOperator b).comp sumCZeroSnd)

@[simp] theorem bipartiteAssembleOperator_inl (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜)
    (f : CZeroOn 𝕜 (P ⊕ Q)) (p : P) :
    bipartiteAssembleOperator a T b f ⟨Sum.inl p⟩ =
      a ⟨p⟩ * sumCZeroFst f ⟨p⟩ + T (sumCZeroSnd f) ⟨p⟩ := by
  simp [bipartiteAssembleOperator]

@[simp] theorem bipartiteAssembleOperator_inr (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜)
    (f : CZeroOn 𝕜 (P ⊕ Q)) (q : Q) :
    bipartiteAssembleOperator a T b f ⟨Sum.inr q⟩ = b ⟨q⟩ * sumCZeroSnd f ⟨q⟩ := by
  simp [bipartiteAssembleOperator]

def bipartiteAssemble (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜) :
    BipartiteAlgebra 𝕜 P Q :=
  ⟨bipartiteAssembleOperator a T b, by
    intro s t hst
    rcases s with p | q <;> rcases t with p' | q'
    · have hne : p ≠ p' := hst
      simp [scalarMatrix, hne]
    · exact (hst trivial).elim
    · simp [scalarMatrix]
    · have hne : q ≠ q' := hst
      simp [scalarMatrix, hne]⟩

@[simp] theorem bipartiteLeftDiagonal_assemble (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜) :
    bipartiteLeftDiagonal (bipartiteAssemble a T b) = a := by
  ext p
  change bipartiteAssembleOperator a T b (unitVector 𝕜 (Sum.inl p.val)) ⟨Sum.inl p.val⟩ = a p
  simp

@[simp] theorem bipartiteRightDiagonal_assemble (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜) :
    bipartiteRightDiagonal (bipartiteAssemble a T b) = b := by
  ext q
  change bipartiteAssembleOperator a T b (unitVector 𝕜 (Sum.inr q.val)) ⟨Sum.inr q.val⟩ = b q
  simp

@[simp] theorem bipartiteUpperBlock_assemble (a : Discrete P →ᵇ 𝕜)
    (T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) (b : Discrete Q →ᵇ 𝕜) :
    bipartiteUpperBlock (bipartiteAssemble a T b) = T := by
  ext f p
  change bipartiteAssembleOperator a T b (sumCZeroInr f) ⟨Sum.inl p.val⟩ = T f p
  simp

set_option maxHeartbeats 800000 in
theorem continuous_bipartite_insert :
    Continuous (fun T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P =>
      bipartiteAssemble (0 : Discrete P →ᵇ 𝕜) T (0 : Discrete Q →ᵇ 𝕜)) := by
  apply Continuous.subtype_mk
  change Continuous (fun T : CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P =>
    sumCZeroInl.comp ((multiplicationOperator (0 : Discrete P →ᵇ 𝕜)).comp sumCZeroFst) +
      sumCZeroInl.comp (T.comp sumCZeroSnd) +
      sumCZeroInr.comp ((multiplicationOperator (0 : Discrete Q →ᵇ 𝕜)).comp sumCZeroSnd))
  let post : (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 P) →L[𝕜]
      (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 (P ⊕ Q)) :=
    ContinuousLinearMap.compL 𝕜 (CZeroOn 𝕜 (P ⊕ Q)) (CZeroOn 𝕜 P) (CZeroOn 𝕜 (P ⊕ Q)) sumCZeroInl
  let pre : (CZeroOn 𝕜 Q →L[𝕜] CZeroOn 𝕜 P) →L[𝕜]
      (CZeroOn 𝕜 (P ⊕ Q) →L[𝕜] CZeroOn 𝕜 P) :=
    (ContinuousLinearMap.compL 𝕜 (CZeroOn 𝕜 (P ⊕ Q)) (CZeroOn 𝕜 Q) (CZeroOn 𝕜 P)).flip sumCZeroSnd
  have hzero : multiplicationOperator (0 : Discrete P →ᵇ 𝕜) = 0 := by ext f p; simp
  have hzero' : multiplicationOperator (0 : Discrete Q →ᵇ 𝕜) = 0 := by ext f p; simp
  simp only [hzero, hzero', ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
    zero_add, add_zero]
  exact post.continuous.comp pre.continuous

end Posets







