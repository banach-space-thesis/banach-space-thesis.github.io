import Posets.CountableOrdinalPFPBandSelection

/-! Further full-rank leaf pruning is compatible with the already proved
norming estimates. Retain only hereditary nodes of the new leaf family. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}
variable {M : JLMS.AtomicDualModel 𝕜 (Iic θ)}
  {T : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ)}
  {lower : Iic γ} {ε : ℝ}

namespace OrdinalTowerNormingBand

def restrictLeaves (F : OrdinalTowerNormingBand M T lower ε)
    (L : Set (OrdinalTowerNode θ γ))
    (hroot : F.top ∈ rankedWolfeFamily (OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T))
      (fun q => q.level.val) F.base L F.top.level.val) : OrdinalTowerNormingBand M T lower ε := by
  let v : OrdinalTowerNode θ γ → WolfeNode 𝕜 (Iic θ) :=
    OrdinalTowerNode.toWolfeNode (wolfeOperatorRow T)
  let C := rankedWolfeHereditaryBase v (fun q => q.level.val) F.base L
  have hCB : C ⊆ F.base := rankedWolfeHereditaryBase_subset v (fun q => q.level.val) F.base L
  refine
    { top := F.top
      base := C
      leaves := L
      countable := F.countable.mono hCB
      root_mem := hroot
      rank := ?_
      cells := fun q hq => F.cells q (hCB hq)
      small := ?_
      outside := fun q hq hlow => F.outside q (hCB hq) hlow
      diagonal := fun q hq hlow => F.diagonal q (hCB hq) hlow }
  · rw [rankedWolfeFamily_restrict_hereditary]
    exact hroot
  · intro q hq
    apply lt_of_le_of_lt (wolfeMass_mono M (wolfeOperatorRow T q.point) ?_)
      (F.small q (hCB hq))
    rintro x ⟨r, hr, hrq, hx⟩
    exact ⟨r, hCB hr, hrq, hx⟩

end OrdinalTowerNormingBand
end Posets
