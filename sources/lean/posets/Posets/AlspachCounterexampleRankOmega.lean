import Posets.AlspachCounterexampleRankFinite

/-! Both compact spaces in the ω-stage Alspach construction have a
singleton ω²-th derivative. This calculates the actual topological rank. -/

noncomputable section
open Set Topology Order ThesisCommon
open scoped Ordinal OnePoint
namespace Posets
universe u v
variable {𝕜 : Type v} [RCLike 𝕜]

theorem alspach_omega_sq_eq_mul :
    (ω ^ (2 : Ordinal.{0})) = ω * ω := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, Ordinal.opow_add, Ordinal.opow_one]

theorem alspach_finite_ranks_lt (n : ℕ) :
    (ω : Ordinal.{0}) * (n + 1 : ℕ) < ω ^ (2 : Ordinal.{0}) := by
  rw [alspach_omega_sq_eq_mul]
  exact mul_lt_mul_of_pos_left (Ordinal.nat_lt_omega0 (n + 1)) Ordinal.omega0_pos

theorem alspach_finite_ranks_cofinal (γ : Ordinal.{0}) (hγ : γ < ω ^ (2 : Ordinal.{0})) :
    ∃ n : ℕ, γ ≤ (ω : Ordinal.{0}) * (n + 1 : ℕ) := by
  rw [alspach_omega_sq_eq_mul] at hγ
  obtain ⟨δ, hδ, hγδ⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hγ
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hδ
  exact ⟨n, hγδ.le.trans (mul_le_mul_left' (by exact_mod_cast Nat.le_succ n) _)⟩

theorem alspachOmegaCompactRows_ordinalDerived
    (B : Type u) [TopologicalSpace B] [CompactSpace B] [T2Space B] [Countable B]
    (p : B) (hB : ordinalDerived (univ : Set B) (ω : Ordinal.{0}) = {p}) :
    ordinalDerived (univ : Set (alspachOmegaCompactRows (𝕜 := 𝕜) B p).Point)
      (ω ^ (2 : Ordinal.{0})) = {(alspachOmegaCompactRows (𝕜 := 𝕜) B p).rows.point} ∧
    ordinalDerived (univ : Set (alspachOmegaCompactRows (𝕜 := 𝕜) B p).Index)
      (ω ^ (2 : Ordinal.{0})) = {(alspachOmegaCompactRows (𝕜 := 𝕜) B p).rows.index} := by
  have hlim : IsSuccLimit (ω ^ (2 : Ordinal.{0})) := by
    rw [alspach_omega_sq_eq_mul]
    exact Ordinal.isSuccLimit_mul Ordinal.omega0_pos Ordinal.isSuccLimit_omega0
  constructor
  · exact alspachOnePoint_ordinalDerived_limit
      (fun n => (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).Point)
      (fun n => (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).rows.point)
      (fun n => ω * (n + 1 : ℕ)) _ hlim alspach_finite_ranks_lt
      alspach_finite_ranks_cofinal (fun n => (alspachFiniteCompactRows_ordinalDerived B p hB n).1)
  · exact alspachOnePoint_ordinalDerived_limit
      (fun n => (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).Index)
      (fun n => (alspachFiniteCompactRows (𝕜 := 𝕜) B p n).rows.index)
      (fun n => ω * (n + 1 : ℕ)) _ hlim alspach_finite_ranks_lt
      alspach_finite_ranks_cofinal (fun n => (alspachFiniteCompactRows_ordinalDerived B p hB n).2)

end Posets
