import Posets.AlspachCounterexampleRankLimit
import Posets.AlspachCounterexampleCompactRows

/-! The concrete finite Alspach spaces have characteristic rank ω(n+1).
Both their point spaces and their row-index spaces have the distinguished
point as their sole survivor at that rank. -/

noncomputable section
open Set Topology Order ThesisCommon
open scoped Ordinal OnePoint
namespace Posets
universe u v
variable {𝕜 : Type v} [RCLike 𝕜]

theorem AlspachCompactRows.successor_point_ordinalDerived
    (F G : AlspachCompactRows.{u, v} 𝕜) (β γ : Ordinal.{0})
    (hF : ordinalDerived (univ : Set F.Point) γ = {F.rows.point})
    (hG : ordinalDerived (univ : Set G.Point) β = {G.rows.point}) :
    ordinalDerived (univ : Set (F.successor G).Point) (β + γ) =
      {(F.successor G).rows.point} := by
  have h := alspachCompactGraft_ordinalDerived_add
    (Prod.fst : F.Point × F.Index → F.Point) (fun _ => G.Point) (fun _ => G.rows.point)
    β γ (fun _ => hG) (fun x => ⟨(x, F.rows.index), rfl⟩)
  rw [hF, image_singleton] at h
  exact h

theorem AlspachCompactRows.successor_index_ordinalDerived
    (F G : AlspachCompactRows.{u, v} 𝕜) (β γ : Ordinal.{0})
    (hF : ordinalDerived (univ : Set F.Index) γ = {F.rows.index})
    (hG : ordinalDerived (univ : Set G.Index) β = {G.rows.index}) :
    ordinalDerived (univ : Set (F.successor G).Index) (β + γ) =
      {(F.successor G).rows.index} := by
  have h := alspachCompactGraft_ordinalDerived_add
    (id : F.Index → F.Index) (fun _ => G.Index) (fun _ => G.rows.index)
    β γ (fun _ => hG) Function.surjective_id
  rw [hF, image_singleton] at h
  exact h

theorem alspachFiniteCompactRows_ordinalDerived
    (B : Type u) [TopologicalSpace B] [CompactSpace B] [T2Space B] [Countable B]
    (p : B) (hB : ordinalDerived (univ : Set B) (ω : Ordinal.{0}) = {p}) (n : ℕ) :
    ordinalDerived (univ : Set (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).Point)
      ((ω : Ordinal.{0}) * (n + 1 : ℕ)) = {(alspachFiniteCompactRows (𝕜 := 𝕜) B p n).rows.point} ∧
    ordinalDerived (univ : Set (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).Index)
      ((ω : Ordinal.{0}) * (n + 1 : ℕ)) = {(alspachFiniteCompactRows (𝕜 := 𝕜) B p n).rows.index} := by
  induction n with
  | zero => simpa only [Nat.zero_add, Nat.cast_one, mul_one] using And.intro hB hB
  | succ n ih =>
      have he : (ω * ((n + 1 : ℕ) : Ordinal.{0}) + ω) = ω * ((n + 1 + 1 : ℕ) : Ordinal.{0}) := by
        simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      constructor
      · rw [← he]
        exact AlspachCompactRows.successor_point_ordinalDerived
          (AlspachCompactRows.base B p) (alspachFiniteCompactRows B p n) _ _ hB ih.1
      · rw [← he]
        exact AlspachCompactRows.successor_index_ordinalDerived
          (AlspachCompactRows.base B p) (alspachFiniteCompactRows B p n) _ _ hB ih.2

end Posets
