import Posets.AlspachCounterexampleCompactOperator
import Posets.AlspachCounterexampleProbabilityMass

/-! The constructed row parameter space is homeomorphic to its actual
weak-star compact set of probability measures. In particular its topological
rank can be transported to the set used in Wolfe's definition. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
namespace Posets
namespace AlspachCompactRows
variable {𝕜 : Type*} [RCLike 𝕜] (F : AlspachCompactRows 𝕜)

def weakRows (i : F.Index) : WeakDual 𝕜 (JLMS.CZero 𝕜 F.Point) :=
  StrongDual.toWeakDual (F.pointAtomicModel.representation.symm (F.rows.forest.row i))

theorem weakRows_continuous : Continuous F.weakRows :=
  WeakDual.continuous_of_continuous_eval F.atomicRows_continuous

theorem weakRows_injective : Function.Injective F.weakRows := by
  intro i j hij
  have hv : F.rows.forest.row i = F.rows.forest.row j := by
    have he := congrArg (fun μ : WeakDual 𝕜 (JLMS.CZero 𝕜 F.Point) =>
      F.pointAtomicModel.representation (WeakDual.toStrongDual μ)) hij
    change F.pointAtomicModel.representation (F.pointAtomicModel.representation.symm _) =
      F.pointAtomicModel.representation (F.pointAtomicModel.representation.symm _) at he
    simpa only [F.pointAtomicModel.representation.apply_symm_apply] using he
  have he : lp.single (E := fun _ : F.Index => 𝕜) 1 i 1 = lp.single 1 j 1 := by
    rw [← F.rows.forest.inverse_read_row i, ← F.rows.forest.inverse_read_row j, hv]
  by_contra hn
  have hc := congrArg (fun a : lp (fun _ : F.Index => 𝕜) 1 => a i) he
  simp [lp.single_apply, hn, Ne.symm hn] at hc

theorem weakRows_isClosedEmbedding : IsClosedEmbedding F.weakRows :=
  F.weakRows_continuous.isClosedEmbedding F.weakRows_injective

def weakRowsHomeomorph : F.Index ≃ₜ Set.range F.weakRows :=
  F.weakRows_isClosedEmbedding.isEmbedding.toHomeomorph

theorem weakRows_range_compact : IsCompact (Set.range F.weakRows) :=
  isCompact_range F.weakRows_continuous

theorem weakRows_range_closed : IsClosed (Set.range F.weakRows) :=
  F.weakRows_isClosedEmbedding.isClosed_range

theorem weakRows_norm (i : F.Index) : ‖WeakDual.toStrongDual (F.weakRows i)‖ = 1 := by
  change ‖F.pointAtomicModel.representation.symm (F.rows.row i).vector‖ = 1
  rw [F.pointAtomicModel.representation.symm.norm_map]
  exact (F.rows.row i).vector_norm

theorem weakRows_mass (i : F.Index) (U : Set F.Point) :
    wolfeMass F.pointAtomicModel (F.weakRows i) U = (F.rows.row i).mass U :=
  (F.rows.row i).wolfeMass_probability F.pointAtomicModel U

theorem weakRows_adjoint (i : F.Index) :
    F.weakRows i = StrongDual.toWeakDual
      (JLMS.banachAdjoint F.evaluation (JLMS.evaluation i)) := by
  apply DFunLike.ext
  intro f
  change F.pointAtomicModel.representation.symm (F.rows.forest.row i) f = F.evaluation f i
  rfl

end AlspachCompactRows
end Posets

