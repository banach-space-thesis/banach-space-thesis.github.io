import Posets.TriangularProductTransfer
import Posets.CompactificationLift
import Posets.MrowkaHeight
import Mathlib.Analysis.Matrix

/-! Theorem 1.8 follows from the exact product realization in Theorem 1.5.
The sole unproved input is stated explicitly as a hypothesis. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
open scoped ZeroAtInfty Matrix.Norms.Operator
namespace Posets

set_option maxHeartbeats 1000000 in
theorem theorem_1_8_of_1_5 (𝕜 : Type) [RCLike 𝕜]
    (h5 : Theorem_1_5 𝕜 (fun _ : ℕ => BipartiteAlgebra 𝕜 RowDomain ColumnDomain)) :
    Theorem_1_8 𝕜 := by
  obtain ⟨𝒜, h𝒜, θ, ρ, hs, _, _⟩ :=
    h5 (fun _ => bipartite_admissible 𝕜 RowDomain ColumnDomain)
  obtain ⟨Φ, hΦ, hΦrange, hnΦ⟩ := exists_discontinuous_triangular_incidence_hom 𝕜
  obtain ⟨Ψ, hΨ, hΨrange, hnΨ, hΨsep⟩ :=
    discontinuous_hom_of_constantProduct_strongSplit θ ρ hs Φ hΦ hnΦ
  have hrange : Set.range Ψ = triangularTwo 𝕜 := hΨrange.trans hΦrange
  have hfin : ∀ T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜,
      FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) → Ψ T = 0 :=
    fun T hT => hΨsep T (finiteRank_hasSeparableRange T hT)
  letI : T2Space (Mrowka 𝒜) := mrowka_t2 𝒜 h𝒜
  letI : LocallyCompactSpace (Mrowka 𝒜) := mrowka_locallyCompact 𝒜 h𝒜
  obtain ⟨ΨK, hΨK, hΨKrange, _, _, _, hnΨK⟩ :=
    lemma_8_3_proof 𝕜 (Mrowka 𝒜) (Matrix (Fin 2) (Fin 2) 𝕜) Ψ hΨ hfin
  refine ⟨⟨𝒜, h𝒜, Ψ, hΨ, hrange, hnΨ⟩, ?_⟩
  exact ⟨OnePoint (Mrowka 𝒜), inferInstance, inferInstance, inferInstance,
    onePointMrowka_thirdDerived_empty 𝒜, ΨK, hΨK,
    hΨKrange.trans hrange, hnΨK hnΨ⟩

end Posets
