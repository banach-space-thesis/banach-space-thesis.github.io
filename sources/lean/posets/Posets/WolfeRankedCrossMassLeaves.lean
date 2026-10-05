import Posets.WolfeRankedClosure
import Posets.WolfeOutsideMass
import Posets.WolfeRankedCrossMassSets

/-! Binary leaf pruning and passage of open-set mass bounds to all ranks. -/
noncomputable section
open Set Topology
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_inter_or_diff
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B L S : Set P)
    (α : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B L α) :
    p ∈ rankedWolfeFamily v height B (L ∩ S) α ∨
      p ∈ rankedWolfeFamily v height B (L \ S) α := by
  classical
  let C : Bool → Set P := fun b => if b then L ∩ S else L \ S
  have hC : L = ⋃ b, C b := by
    ext q
    constructor
    · intro hq
      by_cases hqS : q ∈ S
      · exact mem_iUnion.mpr ⟨true, hq, hqS⟩
      · exact mem_iUnion.mpr ⟨false, hq, hqS⟩
    · intro hq
      obtain ⟨b, hb⟩ := mem_iUnion.mp hq
      cases b <;> exact hb.1
  rw [hC, rankedWolfeFamily_iUnion] at hp
  obtain ⟨b, hb⟩ := mem_iUnion.mp hp
  cases b with
  | false => exact Or.inr hb
  | true => exact Or.inl hb

variable [LocallyCompactSpace K] [T2Space K]

/-- An open-set mass upper bound on rank-zero leaves holds at every retained rank. -/
theorem rankedWolfeFamily_mass_le_of_leaves (M : JLMS.AtomicDualModel 𝕜 K)
    (hK : JLMS.IsScattered K) (v : P → WolfeNode 𝕜 K)
    (height : P → Ordinal.{u}) (B L : Set P) {U : Set K} (hU : IsOpen U) {Q : ℝ}
    (hleaf : ∀ q ∈ B, height q = 0 → q ∈ L → wolfeMass M (v q).1 U ≤ Q)
    (α : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B L α) :
    wolfeMass M (v p).1 U ≤ Q := by
  have hclosed : IsClosed {μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K) | wolfeMass M μ U ≤ Q} := by
    simpa only [Set.compl_setOf, not_lt] using (isOpen_wolfeMass_gt M hK hU Q).isClosed_compl
  apply rankedWolfeFamily_closed_lower v height B L α hp (Ordinal.zero_le α) _ hclosed
  intro q hq _
  obtain ⟨hb, hh, hl⟩ := (mem_rankedWolfeFamily_zero v height B L q).mp hq
  exact hleaf q hb hh hl

end Posets
