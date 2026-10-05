import ThesisCommon.Analysis.ALFragmentNonatom
import Mathlib.Order.Zorn

/-! Atomless positive vectors in complete AL-lattices have fragments of every
prescribed norm, including an exact equal-halves decomposition. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ u v : E, 0 ≤ u → 0 ≤ v → ‖u+v‖ = ‖u‖+‖v‖)

theorem IsPositiveFragment.of_tendsto {x y : E} {u : ℕ → E}
    (hu : ∀ n, IsPositiveFragment (u n) x) (hlim : Tendsto u atTop (𝓝 y)) :
    IsPositiveFragment y x := by
  refine ⟨ge_of_tendsto' hlim (fun n => (hu n).1),
    le_of_tendsto' hlim (fun n => (hu n).2.1), ?_⟩
  have hc : Continuous (fun z : E => z ⊓ (x-z)) :=
    continuous_id.inf (continuous_const.sub continuous_id)
  apply tendsto_nhds_unique ((hc.tendsto y).comp hlim)
  change Tendsto (fun n => u n ⊓ (x-u n)) atTop (𝓝 0)
  simp_rw [(hu _).2.2]
  exact tendsto_const_nhds

include hAL

theorem al_exists_fragment_of_norm {x : E} (hx : 0 ≤ x)
    (hno : NoPositiveAtomsBelow x) {r : ℝ} (hr0 : 0 ≤ r) (hrx : r ≤ ‖x‖) :
    ∃ y : E, IsPositiveFragment y x ∧ ‖y‖ = r := by
  let s : Set E := {y | IsPositiveFragment y x ∧ ‖y‖ ≤ r}
  have hzero : (0 : E) ∈ s := ⟨IsPositiveFragment.zero hx, by simpa using hr0⟩
  have hchain : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ b ∈ s, ∀ z ∈ c, z ≤ b := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hcn
    · exact ⟨0,hzero,by simp⟩
    · have hpos : ∀ z ∈ c, 0 ≤ z := fun z hz => (hcs hz).1.1
      have hbound : BddAbove (norm '' c) := by
        refine ⟨r,?_⟩
        rintro _ ⟨z,hz,rfl⟩
        exact (hcs hz).2
      obtain ⟨b,hb,u,hu,hlim,_⟩ := al_exists_isLUB_of_directed_norm_bdd hAL hcn hpos
        hc.directedOn hbound
      exact ⟨b, ⟨IsPositiveFragment.of_tendsto (fun n => (hcs (hu n)).1) hlim,
        le_of_tendsto' hlim.norm (fun n => (hcs (hu n)).2)⟩, fun z hz => hb.1 hz⟩
  obtain ⟨y,hy,hmax⟩ := zorn_le₀ s hchain
  refine ⟨y,hy.1,le_antisymm hy.2 ?_⟩
  by_contra hlt
  have hyr : ‖y‖ < r := lt_of_not_ge hlt
  have hres0 : 0 ≤ x-y := sub_nonneg.mpr hy.1.2.1
  have hresne : x-y ≠ 0 := by
    intro heq
    have hxy : x = y := sub_eq_zero.mp heq
    rw [hxy] at hrx
    linarith
  obtain ⟨z,hz,hzne,hznorm⟩ := al_exists_arbitrarily_small_fragment hAL hres0 hresne
    (hno.mono (sub_le_self x hy.1.1)) (sub_pos.mpr hyr)
  have hsum : ‖y+z‖ = ‖y‖+‖z‖ := hAL y z hy.1.1 hz.1
  have hmem : y+z ∈ s := ⟨hy.1.add_compl hz, by rw [hsum]; linarith⟩
  have hle : y+z ≤ y := hmax hmem (le_add_of_nonneg_right hz.1)
  exact hzne (le_antisymm (by simpa using hle) hz.1)

theorem al_exists_half_fragment {x : E} (hx : 0 ≤ x) (hno : NoPositiveAtomsBelow x) :
    ∃ y : E, IsPositiveFragment y x ∧ ‖y‖ = ‖x‖/2 ∧ ‖x-y‖ = ‖x‖/2 ∧
      NoPositiveAtomsBelow y ∧ NoPositiveAtomsBelow (x-y) := by
  obtain ⟨y,hy,hnorm⟩ := al_exists_fragment_of_norm hAL hx hno
    (r := ‖x‖/2) (by positivity) (by have := norm_nonneg x; linarith)
  have hsum := hAL y (x-y) hy.1 (sub_nonneg.mpr hy.2.1)
  have heq : y+(x-y) = x := by abel
  rw [heq,hnorm] at hsum
  exact ⟨y,hy,hnorm,by linarith,hy.noAtoms_children hno⟩

end ThesisCommon
