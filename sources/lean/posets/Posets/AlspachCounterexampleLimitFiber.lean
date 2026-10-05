import Posets.AlspachCounterexampleFiberWolfe
import Posets.AlspachCounterexampleRankLimit

/-! Each completed component of the ω-stage row family is a continuous
one-branch push-forward of its original finite stage, preserving every
Wolfe threshold and level under pullback. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Topology
open scoped OnePoint
namespace Posets
namespace AlspachCompactRows
variable {𝕜 : Type*} [RCLike 𝕜] (F : ℕ → AlspachCompactRows 𝕜)

abbrev limitFiberIndex (n : ℕ) : (F n).Index → (limit F).Index :=
  AlspachPointedRows.limitIndex (fun n => (F n).rows) n

abbrev limitFiberPoint (n : ℕ) : (F n).Point → (limit F).Point :=
  AlspachPointedRows.limitPoint (fun n => (F n).rows) n

theorem limitFiberIndex_eq_attach (n : ℕ) :
    limitFiberIndex F n = alspachOnePointAttach (fun n => (F n).Index)
      (fun n => (F n).rows.index) n := by
  funext j
  by_cases hj : j = (F n).rows.index
  · subst j
    simp [limitFiberIndex, AlspachPointedRows.limitIndex,
      alspachOnePointAttach, OnePoint.infty, OnePoint.map]
  · simp [limitFiberIndex, AlspachPointedRows.limitIndex, hj,
      alspachOnePointAttach, alspachPunctureHomeomorph_symm_nonroot,
      OnePoint.some, OnePoint.map]

theorem limitFiberIndex_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (limitFiberIndex F n) := by
  rw [limitFiberIndex_eq_attach]
  exact alspachOnePointAttach_isClosedEmbedding _ _ n

theorem limitFiberPoint_continuous (n : ℕ) : Continuous (limitFiberPoint F n) :=
  AlspachPointedRows.limitPoint_continuous (fun n => (F n).rows) n

theorem limitFiber_mass (n : ℕ) (j : (F n).Index) (U : Set (limit F).Point) :
    ((limit F).rows.row (limitFiberIndex F n j)).mass U =
      ((F n).rows.row j).mass (limitFiberPoint F n ⁻¹' U) := by
  change (AlspachPointedRows.limitRow (fun n => (F n).rows)
    (AlspachPointedRows.limitIndex (fun n => (F n).rows) n j)).mass U = _
  rw [AlspachPointedRows.limitRow_index, AlspachProbability.mass_map]

theorem limitFiber_wolfe_pullback {ε : ℝ} (n : ℕ) (α : Ordinal)
    (j : (F n).Index) (U : Set (limit F).Point)
    (h : ((limit F).weakRows (limitFiberIndex F n j), U) ∈
      wolfeFamily (limit F).pointAtomicModel ε
        (range (fun j => (limit F).weakRows (limitFiberIndex F n j))) α) :
    ((F n).weakRows j, limitFiberPoint F n ⁻¹' U) ∈
      wolfeFamily (F n).pointAtomicModel ε (range (F n).weakRows) α := by
  have hsel : ∀ j : (F n).Index, ∀ U : Set (limit F).Point, IsOpen U → U ⊆ univ →
      ε ≤ ((limit F).rows.row (limitFiberIndex F n j)).mass U →
      ∃ _ : Unit, ε ≤ ((F n).rows.row j).mass (limitFiberPoint F n ⁻¹' U) := by
    intro j U _ _ hm
    exact ⟨(), (limitFiber_mass F n j U) ▸ hm⟩
  obtain ⟨b, hb⟩ := wolfe_positive_mixture_pullback (F n).pointAtomicModel (limit F).pointAtomicModel
    (alspach_countable_compact_scattered (F n).Point) (F n).rows.row
    (fun j => (limit F).rows.row (limitFiberIndex F n j))
    (fun _ : Unit => limitFiberPoint F n) (fun _ => limitFiberPoint_continuous F n)
    (F n).weakRows_continuous
    ((limit F).weakRows_isClosedEmbedding.isEmbedding.comp
      (limitFiberIndex_isClosedEmbedding F n).isEmbedding)
    univ hsel α j U (subset_univ U) h
  exact hb

end AlspachCompactRows
end Posets
