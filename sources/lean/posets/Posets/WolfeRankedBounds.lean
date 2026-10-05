import Posets.WolfeRankedClosure
import Posets.WolfeDiagonalLimits

/-! Propagation from the selected bottom leaves to their ranked ancestors.
The fixed parent cell is clopen, so both the outside-mass upper bound and
the signed indicator lower bound are closed conditions on the row. -/

noncomputable section
open Set Topology
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_outside_le [LocallyCompactSpace K] [T2Space K]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (α : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves α)
    {H : Set K} (hH : IsOpen H) (hpclosed : IsClosed (v p).2) {ε : ℝ}
    (hleaf : ∀ q ∈ rankedWolfeFamily v height B Leaves 0,
      (v q).2 ⊆ (v p).2 → wolfeMass M (v q).1 (H \ (v p).2) ≤ ε) :
    wolfeMass M (v p).1 (H \ (v p).2) ≤ ε := by
  have hc : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
      wolfeMass M μ (H \ (v p).2) ≤ ε} := by
    simpa only [Set.compl_setOf, not_lt] using
      (isOpen_wolfeMass_gt M hK (hH.sdiff hpclosed) ε).isClosed_compl
  exact rankedWolfeFamily_closed_lower v height B Leaves α hp (Ordinal.zero_le _) _ hc hleaf

theorem rankedWolfeFamily_diagonal_lower
    (M : JLMS.AtomicDualModel 𝕜 K)
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (α : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves α)
    (hpcl : IsClopen (v p).2) (hpc : IsCompact (v p).2)
    {H : Set K} (hpH : (v p).2 ⊆ H)
    (U : P → Set K) (hU : ∀ q, IsClopen (U q)) (hcU : ∀ q, IsCompact (U q))
    {ell ε : ℝ}
    (hleaf : ∀ q ∈ rankedWolfeFamily v height B Leaves 0,
      (v q).2 ⊆ (v p).2 → U q ⊆ (v p).2 ∧
        ell ≤ RCLike.re ((v q).1 (JLMS.clopenIndicator (U q) (hU q) (hcU q))) ∧
        wolfeMass M (v q).1 (H \ U q) ≤ ε) :
    ell - ε ≤ RCLike.re ((v p).1 (JLMS.clopenIndicator (v p).2 hpcl hpc)) := by
  have hc : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) |
      ell - ε ≤ RCLike.re (μ (JLMS.clopenIndicator (v p).2 hpcl hpc))} :=
    isClosed_le continuous_const
      (RCLike.continuous_re.comp (WeakDual.eval_continuous _))
  apply rankedWolfeFamily_closed_lower v height B Leaves α hp (Ordinal.zero_le _) _ hc
  intro q hq hqp
  obtain ⟨hUp, hdiag, hout⟩ := hleaf q hq hqp
  exact wolfe_re_indicator_le_of_outside M (v q).1 (hU q) (hcU q) hpcl hpc
    hUp hpH hdiag hout

end Posets
