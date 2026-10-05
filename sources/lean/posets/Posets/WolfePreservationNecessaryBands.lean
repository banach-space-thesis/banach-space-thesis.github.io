import Posets.AlspachCounterexampleRankShift
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Separation.Regular

/-! Finite-band pruning for an actual lower-semicontinuous weight. Passing to
one band of width η costs at most multiplication of the requested derivative
rank by the number of bands. This records the ordinal loss explicitly. -/

noncomputable section
open Set Filter Topology ThesisCommon
universe u
namespace Posets
variable {Y : Type*} [TopologicalSpace Y] [T1Space Y]

theorem wolfe_ordinalDerived_closed_neighborhood_core [RegularSpace Y]
    {A U : Set Y} (hA : IsClosed A) (hU : IsOpen U) (α : Ordinal.{u})
    {x : Y} (hx : x ∈ ordinalDerived A α) (hxU : x ∈ U) :
    ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧ B ⊆ U ∧ x ∈ ordinalDerived B α := by
  obtain ⟨V, hVx, hV, hVU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
  have hxV : x ∈ interior V := mem_interior_iff_mem_nhds.mpr hVx
  have he : A = (A ∩ V) ∪ (A ∩ (interior V)ᶜ) := by
    ext y
    constructor
    · intro hy
      by_cases hyV : y ∈ V
      · exact Or.inl ⟨hy, hyV⟩
      · exact Or.inr ⟨hy, fun hi => hyV (interior_subset hi)⟩
    · rintro (hy | hy) <;> exact hy.1
  have hright : IsClosed (A ∩ (interior V)ᶜ) := hA.inter isOpen_interior.isClosed_compl
  have hnot : x ∉ ordinalDerived (A ∩ (interior V)ᶜ) α := by
    intro h
    have hs : ordinalDerived (A ∩ (interior V)ᶜ) α ⊆ A ∩ (interior V)ᶜ := by
      simpa using ordinalDerived_antitone hright (show (0 : Ordinal.{u}) ≤ α from bot_le)
    exact (hs h).2 hxV
  rw [he, ordinalDerived_union (hA.inter hV) hright] at hx
  exact ⟨A ∩ V, hA.inter hV, inter_subset_left,
    fun _ h => hVU h.2, hx.resolve_right hnot⟩

theorem wolfe_closed_chain_rank_step
    (A : ℕ → Set Y) (hA : ∀ n, IsClosed (A n)) (hzero : A 0 = ∅)
    (β : Ordinal.{u}) (N : ℕ)
    (hrank : (ordinalDerived (A N) (β * (N : Ordinal))).Nonempty) :
    ∃ j < N, ∃ x, x ∈ ordinalDerived (A (j + 1)) β ∧ x ∉ A j := by
  classical
  by_contra hnone
  push_neg at hnone
  have hstep : ∀ j < N, ordinalDerived (A (j + 1)) β ⊆ A j := by
    intro j hj x hx
    exact hnone j hj x hx
  have hall : ∀ n ≤ N, ordinalDerived (A n) (β * (n : Ordinal)) ⊆ A 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro hn
        have he : β * ((n + 1 : ℕ) : Ordinal) = β + β * (n : Ordinal) := by
          rw [show n + 1 = 1 + n by omega, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        rw [he, alspach_ordinalDerived_add (hA (n + 1))]
        exact (ordinalDerived_mono (hstep n (by omega)) _).trans (ih (by omega))
  obtain ⟨x, hx⟩ := hrank
  have h := hall N le_rfl hx
  simp [hzero] at h

theorem wolfe_lowerSemicontinuous_band_core [RegularSpace Y]
    {A : Set Y} (hA : IsClosed A) (q : Y → ℝ) (hq : LowerSemicontinuous q)
    {η : ℝ} (_hη : 0 < η) (N : ℕ)
    (hpos : ∀ x ∈ A, 0 < q x) (hbound : ∀ x ∈ A, q x ≤ N * η)
    (β : Ordinal.{u})
    (hrank : (ordinalDerived A (β * (N : Ordinal))).Nonempty) :
    ∃ j < N, ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧
      (ordinalDerived B β).Nonempty ∧
      ∀ x ∈ B, (j : ℝ) * η < q x ∧ q x ≤ (j + 1 : ℕ) * η := by
  let F (j : ℕ) := A ∩ {x | q x ≤ j * η}
  have hF (j : ℕ) : IsClosed (F j) := hA.inter (hq.isClosed_preimage (j * η))
  have hFzero : F 0 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxA, hxq⟩
    have hx := hpos x hxA
    simp only [Nat.cast_zero, zero_mul, mem_setOf_eq] at hxq
    linarith
  have hFN : F N = A := by
    apply Subset.antisymm inter_subset_left
    intro x hx
    exact ⟨hx, hbound x hx⟩
  obtain ⟨j, hj, x, hx, hxn⟩ := wolfe_closed_chain_rank_step F hF hFzero β N
    (by simpa only [hFN] using hrank)
  obtain ⟨B, hB, hBF, hBn, hxB⟩ := wolfe_ordinalDerived_closed_neighborhood_core
    (hF (j + 1)) (hF j).isOpen_compl β hx hxn
  refine ⟨j, hj, B, hB, fun x hx => (hBF hx).1, ⟨x, hxB⟩, ?_⟩
  intro y hy
  refine ⟨?_, (hBF hy).2⟩
  by_contra hn
  exact hBn hy ⟨(hBF hy).1, le_of_not_gt hn⟩

end Posets
