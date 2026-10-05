import Posets.WolfePreservationNecessaryClopen
import Posets.WolfePreservationNecessaryCore
import Mathlib.Topology.ShrinkingLemma

/-! Finite open-cover shrinking retains a closed parameter set of the original
Cantor--Bendixson rank. Applied to finitely many disjoint clopen target pieces,
it gives one piece with a uniform mass lower bound on that closed parameter set.
This statement concerns one selection step, not iterated preservation. -/

noncomputable section
open Set Filter Topology ThesisCommon
universe u
namespace Posets

theorem wolfe_closed_core_of_finite_open_cover {Y I : Type*}
    [TopologicalSpace Y] [T1Space Y] [NormalSpace Y] [Finite I]
    {A : Set Y} (hA : IsClosed A) (α : Ordinal.{u})
    (hα : (ordinalDerived A α).Nonempty)
    (U : I → Set Y) (hU : ∀ i, IsOpen (U i)) (hcover : A ⊆ ⋃ i, U i) :
    ∃ i : I, ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧ B ⊆ U i ∧
      (ordinalDerived B α).Nonempty := by
  classical
  obtain ⟨V, hAV, hV, hVU⟩ := exists_subset_iUnion_closed_subset hA hU
    (fun _ _ => Set.toFinite _) hcover
  have he : A = ⋃ i, A ∩ V i := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hAV hx)
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
    · exact iUnion_subset fun _ => inter_subset_left
  obtain ⟨x, hx⟩ := hα
  rw [he, ordinalDerived_iUnion_finite (fun i => A ∩ V i)
    (fun i => hA.inter (hV i))] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨i, A ∩ V i, hA.inter (hV i), inter_subset_left,
    fun _ hx => hVU i hx.2, x, hi⟩

theorem wolfe_large_mass_color_closed_core
    {𝕜 K Y : Type*} [RCLike 𝕜] [TopologicalSpace K]
    [LocallyCompactSpace K] [T2Space K] [TopologicalSpace Y]
    [T1Space Y] [NormalSpace Y]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (μ : Y → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (hμ : Continuous μ)
    {A : Set Y} (hA : IsClosed A) (α : Ordinal.{u})
    (hα : (ordinalDerived A α).Nonempty)
    {N : ℕ} (hN : 0 < N) (U : Fin N → Set K) (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {d : ℝ} (hd : 0 < d) (hmass : ∀ x ∈ A, d ≤ wolfeMass M (μ x) (⋃ i, U i)) :
    ∃ i : Fin N, ∃ B : Set Y, IsClosed B ∧ B ⊆ A ∧
      (ordinalDerived B α).Nonempty ∧
      ∀ x ∈ B, d / (2 * N) < wolfeMass M (μ x) (U i) := by
  let V (i : Fin N) := {x | d / (2 * N) < wolfeMass M (μ x) (U i)}
  have hV (i : Fin N) : IsOpen (V i) :=
    (isOpen_wolfeMass_gt M hK (hU i) _).preimage hμ
  have hcover : A ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := wolfeMass_exists_large_color M (μ x) hN U hdisj (hmass x hx)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change d / (2 * N) < wolfeMass M (μ x) (U i)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hlt : d / (2 * N) < d / N := by
      apply div_lt_div_of_pos_left hd hNr
      linarith
    exact hlt.trans_le hi
  obtain ⟨i, B, hB, hBA, hBV, hBα⟩ :=
    wolfe_closed_core_of_finite_open_cover hA α hα V hV hcover
  exact ⟨i, B, hB, hBA, hBα, fun _ hx => hBV hx⟩

end Posets
