import Posets.CombinedFamily
import JFA.MrowkaTopology
import Mathlib.Data.Finset.Preimage

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable (𝒜 : ℕ → Set (Set ℕ))

def combineComponent (n : ℕ) (p : Mrowka (𝒜 n)) : Mrowka (combinedFamily 𝒜) :=
  combinePoint 𝒜 ⟨n, p⟩

theorem combineComponent_image_tail (n : ℕ) (A : 𝒜 n) (G F : Finset ℕ)
    (hGF : ∀ k, k ∈ G ↔ Nat.pair n k ∈ F) :
    combineComponent 𝒜 n '' JFA.mrowkaNeighborhood (𝒜 n) A G =
      JFA.mrowkaNeighborhood (combinedFamily 𝒜) (combinedMember 𝒜 n A) F := by
  ext p
  constructor
  · rintro ⟨q, (rfl | ⟨k, hk, hkG, rfl⟩), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.pair n k, ⟨k, hk, rfl⟩, fun h => hkG ((hGF k).mpr h), rfl⟩
  · rintro (rfl | ⟨l, ⟨k, hk, rfl⟩, hlF, rfl⟩)
    · exact ⟨Sum.inr A, Or.inl rfl, rfl⟩
    · exact ⟨Sum.inl k, Or.inr ⟨k, hk, fun h => hlF ((hGF k).mp h), rfl⟩, rfl⟩

theorem combineComponent_isOpenMap (n : ℕ) : IsOpenMap (combineComponent 𝒜 n) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hp, rfl⟩
  cases p with
  | inl k =>
    apply Filter.mem_of_superset ((isolated_open (combinedFamily 𝒜) (Nat.pair n k)).mem_nhds
      (Set.mem_singleton _))
    rintro q rfl
    exact ⟨Sum.inl k, hp, rfl⟩
  | inr A =>
    obtain ⟨G, hG⟩ := JFA.mrowka_open_contains_tail hU A hp
    have he := combineComponent_image_tail 𝒜 n A G (G.image (Nat.pair n))
      (fun k => by simp [Finset.mem_image, Nat.pair_eq_pair])
    apply Filter.mem_of_superset
      ((neighborhood_open (combinedFamily 𝒜) (combinedMember 𝒜 n A)
        (G.image (Nat.pair n))).mem_nhds (Or.inl rfl))
    rw [← he]
    exact Set.image_mono hG

theorem combinePoint_isOpenMap : IsOpenMap (combinePoint 𝒜) := by
  intro U hU
  have he : combinePoint 𝒜 '' U =
      ⋃ n, combineComponent 𝒜 n ''
        ((@Sigma.mk ℕ (fun n => Mrowka (𝒜 n)) n) ⁻¹' U) := by
    ext p
    constructor
    · rintro ⟨⟨n, q⟩, hq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, q, hq, rfl⟩
    · intro hp
      obtain ⟨n, q, hq, heq⟩ := Set.mem_iUnion.mp hp
      exact ⟨⟨n, q⟩, hq, heq⟩
  rw [he]
  exact isOpen_iUnion (fun n => combineComponent_isOpenMap 𝒜 n _
    ((isOpen_sigma_iff.mp hU) n))

theorem combinePoint_continuous (h𝒜 : ∀ n, IsAlmostDisjoint (𝒜 n)) :
    Continuous (combinePoint 𝒜) := by
  apply continuous_generateFrom_iff.mpr
  rintro U (⟨k, rfl⟩ | ⟨B, F, rfl⟩)
  · let n := (Nat.unpair k).1
    let l := (Nat.unpair k).2
    have he : combinePoint 𝒜 '' {⟨n, Sum.inl l⟩} = {Sum.inl k} := by
      simp only [Set.image_singleton, combinePoint]
      rw [Nat.pair_unpair]
    rw [← he, Set.preimage_image_eq _ (combinePoint_injective 𝒜 h𝒜)]
    have hopen := isOpenMap_sigmaMk (σ := fun n => Mrowka (𝒜 n)) (i := n) _
      (isolated_open (𝒜 n) l)
    simpa only [Set.image_singleton] using hopen
  · obtain ⟨⟨n, A⟩, hA⟩ := B.property
    have hB : B = combinedMember 𝒜 n A := Subtype.ext hA.symm
    subst B
    let G := F.preimage (Nat.pair n) (pair_left_injective n).injOn
    have he : combinePoint 𝒜 '' (Sigma.mk n '' JFA.mrowkaNeighborhood (𝒜 n) A G) =
        JFA.mrowkaNeighborhood (combinedFamily 𝒜) (combinedMember 𝒜 n A) F := by
      rw [Set.image_image]
      exact combineComponent_image_tail 𝒜 n A G F (fun k => Finset.mem_preimage)
    rw [← he, Set.preimage_image_eq _ (combinePoint_injective 𝒜 h𝒜)]
    exact isOpenMap_sigmaMk (σ := fun n => Mrowka (𝒜 n)) (i := n) _
      (neighborhood_open (𝒜 n) A G)

/-- The homeomorphism uses exactly the relabelling by the partition into paired rows. -/
def combinedHomeomorph (h𝒜 : ∀ n, IsAlmostDisjoint (𝒜 n)) :
    Mrowka (combinedFamily 𝒜) ≃ₜ (Σ n, Mrowka (𝒜 n)) :=
  ((Equiv.ofBijective (combinePoint 𝒜)
    ⟨combinePoint_injective 𝒜 h𝒜, combinePoint_surjective 𝒜⟩).toHomeomorphOfContinuousOpen
      (combinePoint_continuous 𝒜 h𝒜) (combinePoint_isOpenMap 𝒜)).symm

end Posets
