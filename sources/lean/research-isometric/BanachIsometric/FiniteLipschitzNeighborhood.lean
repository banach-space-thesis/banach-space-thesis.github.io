import BanachIsometric.CompactLocalLipschitz

/-! Local Lipschitz bounds at finitely many points of a compact metric space
produce one actual compact neighborhood on which the map is Lipschitz. This
is the compact germ set needed for exact relative sphere approximation. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology NNReal

theorem exists_compact_lipschitzOn_neighborhood_of_finite
    {P W : Type*} [PseudoMetricSpace P] [CompactSpace P] [PseudoMetricSpace W]
    (f : P → W) (s : Finset P)
    (hlocal : ∀ x ∈ s, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L f U) :
    ∃ A : Set P, IsCompact A ∧ (∀ x ∈ s, x ∈ interior A) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L f A := by
  classical
  have hballs : ∀ i : s, ∃ L : ℝ≥0, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith L f (ball i.val r) := by
    intro i
    obtain ⟨L, U, hU, hLip⟩ := hlocal i.val i.property
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
    exact ⟨L, r, hr, hLip.mono hsub⟩
  choose L r hr hLip using hballs
  let A : Set P := ⋃ i : s, closedBall i.val (r i / 2)
  have hAc : IsCompact A := isCompact_iUnion (fun i => isClosed_closedBall.isCompact)
  have hinside : ∀ x ∈ s, x ∈ interior A := by
    intro x hx
    let i : s := ⟨x, hx⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (closedBall_mem_nhds x (half_pos (hr i)))
      (subset_iUnion (fun i : s => closedBall i.val (r i / 2)) i)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  let U : s → Set A := fun i => Subtype.val ⁻¹' ball i.val (r i)
  have hU : ∀ i, IsOpen (U i) := fun i => isOpen_ball.preimage continuous_subtype_val
  have hcover : (⋃ i, U i) = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨i, hi⟩ := mem_iUnion.mp a.property
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change dist a.val i.val < r i
    exact (mem_closedBall.mp hi).trans_lt (half_lt_self (hr i))
  have hUl : ∀ i, LipschitzOnWith (L i) (fun a : A => f a.val) (U i) := by
    intro i
    simpa only [mul_one] using
      (hLip i).comp (LipschitzWith.subtype_val _).lipschitzOnWith (fun _ ha => ha)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_finite_open_cover
    (fun a : A => f a.val) U hU hcover L hUl
  exact ⟨A, hAc, hinside, K, lipschitzOnWith_iff_restrict.mpr hK⟩

end BanachIsometric
