import JLMS.OrdinalSpaceBlocksTopology
import JLMS.CZeroSum

/-!
# The c₀ estimate for restrictions to ordinal blocks

A continuous function that vanishes on the normal embedding has only
finitely many blocks on which its norm exceeds a positive threshold.
Indeed, its positive norm level set is compact, avoids the embedding's
range, and is covered by the pairwise disjoint open blocks. This is the
compactness form of Kislyakov's argument for equation (3.1).
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}

theorem finite_large_ordinalSpaceBlockRestrictions
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 β) (hf : ∀ x, f (L x) = 0) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {ξ : Set.Iio γ | ε ≤ ‖f.restrict (ordinalSpaceBlockSet L ξ)‖} := by
  classical
  let s : Set (OrdinalInterval β) := {x | ε / 2 ≤ ‖f x‖}
  have hs : IsCompact s := (isClosed_le continuous_const f.continuous.norm).isCompact
  have hcover : s ⊆ ⋃ ξ, ordinalSpaceBlockSet L ξ := by
    intro x hx
    have hxr : x ∉ Set.range L := by
      rintro ⟨y, rfl⟩
      have hh : ε / 2 ≤ ‖f (L y)‖ := hx
      rw [hf y, norm_zero] at hh
      exact (half_pos hε).not_ge hh
    obtain ⟨ξ, hξ⟩ := exists_ordinalSpaceBlock_of_not_mem_range L hL hzero htop x hxr
    exact Set.mem_iUnion.mpr ⟨ξ, hξ⟩
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (ordinalSpaceBlockSet L)
    (fun ξ => (ordinalSpaceBlock_isClopen L ξ).isOpen) hcover
  apply t.finite_toSet.subset
  intro ξ hξ
  by_contra hξt
  have hnorm : ‖f.restrict (ordinalSpaceBlockSet L ξ)‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
    intro x
    change ‖f x.val‖ ≤ ε / 2
    apply le_of_not_ge
    intro hx
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp (ht hx)
    obtain ⟨hηt, hxη⟩ := Set.mem_iUnion.mp hη
    have hξη : ξ ≠ η := by
      intro he
      exact hξt (he ▸ hηt)
    exact Set.disjoint_left.mp (ordinalSpaceBlocks_pairwiseDisjoint L hL hξη) x.prop hxη
  have hh : ε ≤ ε / 2 := hξ.trans hnorm
  linarith

theorem tendsto_norm_ordinalSpaceBlockRestrictions
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 β) (hf : ∀ x, f (L x) = 0) :
    Tendsto (fun ξ : Set.Iio γ => ‖f.restrict (ordinalSpaceBlockSet L ξ)‖) cofinite (𝓝 0) :=
  (tendsto_norm_cofinite_iff_finite _).mpr
    (fun _ hε => finite_large_ordinalSpaceBlockRestrictions L hL hzero htop f hf hε)

/-- The actual c₀ family of restrictions to the compact clopen blocks. -/
def ordinalSpaceBlockRestrictions
    (L : C(OrdinalInterval γ, OrdinalInterval β)) (hL : StrictMono L)
    (hzero : L ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (htop : L ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)
    (f : OrdinalC 𝕜 β) (hf : ∀ x, f (L x) = 0) :
    CZeroSum 𝕜 (fun ξ : Set.Iio γ => C(ordinalSpaceBlockSet L ξ, 𝕜)) :=
  CZeroSum.mk (fun ξ => f.restrict (ordinalSpaceBlockSet L ξ))
    (tendsto_norm_ordinalSpaceBlockRestrictions L hL hzero htop f hf)

end JLMS
