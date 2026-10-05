import Posets.IdealCountRealization
import Posets.ProductIdealConverse

/-! Proposition 8.4, with the usual nonempty finite-poset convention explicit. -/
noncomputable section
open ThesisCommon
namespace Posets

theorem proposition_8_4_proof (𝕜 : Type) [RCLike 𝕜] : Proposition_8_4 𝕜 := by
  refine ⟨?_, ?_, ⟨cZeroNontrivialClosedIdealEquivFinOne⟩,
    cZero_hasUniqueMaximalClosedIdeal⟩
  · intro n
    constructor
    · exact furnishedIdealCount_finite_poset_product
    · rintro ⟨r, k, P, hPf, hPo, hPn, hn⟩
      letI := hPf
      letI := hPo
      letI := hPn
      letI : ∀ i, LocallyFiniteOrder (P i) := fun i =>
        LocallyFiniteOrder.ofFiniteIcc (fun _ _ => Set.toFinite _)
      rw [hn]
      exact furnishedIdealCount_product r P
  · intro r k P hPf hPo hPn hpos
    letI : ∀ i, LocallyFiniteOrder (P i) := fun i =>
      LocallyFiniteOrder.ofFiniteIcc (fun _ _ => Set.toFinite _)
    exact exists_space_with_idealCounts r P hpos

end Posets
