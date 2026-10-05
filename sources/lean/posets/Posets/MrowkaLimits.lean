import Posets.MrowkaTopology
import PosetsCommon.EscapingCompactSets

noncomputable section
open Filter Topology
namespace Posets

theorem map_cofinite_subtype (A : Set ℕ) :
    Filter.map (Subtype.val : A → ℕ) cofinite = Along A := by
  rw [← (Subtype.val_injective : Function.Injective (Subtype.val : A → ℕ)).comap_cofinite_eq]
  exact map_comap_setCoe_val cofinite A

theorem family_tendsto_along (𝒜 : Set (Set ℕ)) (A : 𝒜) :
    Tendsto (Sum.inl : ℕ → Mrowka 𝒜) (Along A.val)
      (@nhds (Mrowka 𝒜) (JFA.mrowkaTopology 𝒜) (Sum.inr A)) := by
  rw [← map_cofinite_subtype]
  exact family_tendsto 𝒜 A

/-- The sequence along a newly adjoined family member escapes every compact
subset of the original space. This is the topological content of Corollary 4.10. -/
theorem natural_tendsto_cocompact {𝒜 : Set (Set ℕ)} {B : Set ℕ}
    (hB : B ∉ 𝒜) (hbig : IsAlmostDisjoint (insert B 𝒜)) :
    Tendsto (Sum.inl : ℕ → Mrowka 𝒜) (Along B) (cocompact (Mrowka 𝒜)) := by
  letI := mrowka_t2 (insert B 𝒜) hbig
  let hinc : 𝒜 ⊆ insert B 𝒜 := Set.subset_insert B 𝒜
  let p : Mrowka (insert B 𝒜) := Sum.inr ⟨B, Set.mem_insert _ _⟩
  have hp : p ∉ Set.range (pointInclusion hinc) := by
    rintro ⟨q, hq⟩
    cases q with
    | inl n => simp [pointInclusion, p, JFA.Mrowka] at hq
    | inr A =>
      have hAB : A.val = B := congrArg Subtype.val (Sum.inr.inj hq)
      exact hB (hAB ▸ A.property)
  exact ThesisCommon.tendsto_cocompact_of_tendsto_outside_range
    (pointInclusion hinc) (pointInclusion_continuous hinc) (Sum.inl : ℕ → Mrowka 𝒜)
    (Along B) p hp (family_tendsto_along (insert B 𝒜) ⟨B, Set.mem_insert _ _⟩)

/-- Corollary 4.10 for the actual C₀ normed function space. -/
theorem corollary_4_10_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) (B : Set ℕ) :
    Corollary_4_10 𝕜 𝒜 B := by
  intro _ _ hB hbig f
  exact (zero_at_infty f).comp (natural_tendsto_cocompact hB hbig)

end Posets
