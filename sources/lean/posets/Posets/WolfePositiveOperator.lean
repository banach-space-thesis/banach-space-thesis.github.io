import Posets.WolfePositiveCompact
import Posets.WolfeCZeroPreservation
import Posets.AlspachCounterexampleWeakRows

/-! For an actual positive-row evaluation operator, every adjoint-ball Wolfe
witness reduces to a witness among its rows, at any smaller positive scale.
The base selection follows the operator supremum norm; the transfinite step
uses the proved compact positive selection theorem. Thus no unproved convex
hull identification or preservation criterion is needed for this reduction. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [TopologicalSpace P]

theorem wolfe_positive_evaluation_mass_selection
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (q : P → AlspachProbability K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 P)
    (hT : ∀ f p, T f p = wolfeProbabilityRow M (q p) f)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε)
    {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hμ : μ ∈ adjointUnitBall T)
    {U : Set K} (hU : IsOpen U) (hε : ε ≤ wolfeMass M μ U) :
    ∃ p : P, δ ≤ (q p).mass U := by
  obtain ⟨f, hn, hs, hlarge⟩ := exists_supported_wolfe_norming_function M hK μ hU
    (hδε.trans_le hε)
  by_contra hno
  push_neg at hno
  have hTf : ‖T f‖ ≤ δ := (BoundedContinuousFunction.norm_le hδ).mpr fun p => by
    change ‖T f p‖ ≤ δ
    rw [hT]
    exact (norm_apply_le_wolfeMass_of_support_subset M
      (wolfeProbabilityRow M (q p)) f hs hn).trans (by
        rw [show wolfeMass M (wolfeProbabilityRow M (q p)) U = (q p).mass U from
          (q p).wolfeMass_probability M U]
        exact (hno p).le)
  exact hlarge.not_ge ((norm_apply_le_of_mem_adjointUnitBall T hμ f).trans hTf)

theorem wolfe_positive_evaluation_selection [SeqCompactSpace P]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (q : P → AlspachProbability K)
    (hq : Continuous (fun p => wolfeProbabilityRow M (q p)))
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 P)
    (hT : ∀ f p, T f p = wolfeProbabilityRow M (q p) f)
    {ε δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε) (α : Ordinal.{u}) :
    ∀ z ∈ wolfeFamily M ε (adjointUnitBall T) α,
      ∃ p : P, (wolfeProbabilityRow M (q p), z.2) ∈
        wolfeFamily M δ (range (fun p => wolfeProbabilityRow M (q p))) α :=
  wolfe_positive_compact_selection M hK q hq (adjointUnitBall T)
    (fun _ hμ _ hU hε => wolfe_positive_evaluation_mass_selection M hK q T hT hδ hδε hμ hU hε) α

namespace AlspachCompactRows
variable (F : AlspachCompactRows 𝕜)

theorem wolfe_evaluation_selection {ε δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε)
    (α : Ordinal.{u}) :
    ∀ z ∈ wolfeFamily F.pointAtomicModel ε (adjointUnitBall F.evaluation) α,
      ∃ i : F.Index, (F.weakRows i, z.2) ∈
        wolfeFamily F.pointAtomicModel δ (range F.weakRows) α := by
  letI : TopologicalSpace.MetrizableSpace F.Index := alspach_countable_compact_metrizable F.Index
  exact wolfe_positive_evaluation_selection F.pointAtomicModel
    (alspach_countable_compact_scattered F.Point) F.rows.row F.weakRows_continuous
    F.evaluation (fun _ _ => rfl) hδ hδε α

theorem wolfe_evaluation_empty_of_rows {ε δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε)
    (α : Ordinal.{u})
    (hempty : wolfeFamily F.pointAtomicModel δ (range F.weakRows) α = ∅) :
    wolfeFamily F.pointAtomicModel ε (adjointUnitBall F.evaluation) α = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨i, hi⟩ := F.wolfe_evaluation_selection hδ hδε α z hz
  rw [hempty] at hi
  exact hi

end AlspachCompactRows
end Posets
