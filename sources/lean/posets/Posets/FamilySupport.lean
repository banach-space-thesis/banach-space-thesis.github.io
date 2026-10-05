import Posets.MrowkaTopology

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace Posets

/-- A compact set meets only finitely many family points. -/
theorem compact_familyPoints_finite (𝒜 : Set (Set ℕ)) {C : Set (Mrowka 𝒜)}
    (hC : IsCompact C) : {A : 𝒜 | (Sum.inr A : Mrowka 𝒜) ∈ C}.Finite := by
  classical
  let U : Mrowka 𝒜 → Set (Mrowka 𝒜) := fun p =>
    match p with
    | .inl n => {Sum.inl n}
    | .inr A => JFA.mrowkaNeighborhood 𝒜 A ∅
  have hopen : ∀ p, IsOpen (U p) := by
    intro p
    cases p with
    | inl n => exact isolated_open 𝒜 n
    | inr A => exact neighborhood_open 𝒜 A ∅
  have hcover : C ⊆ ⋃ p, U p := by
    intro p _
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    cases p with
    | inl n => exact Set.mem_singleton _
    | inr A => exact Or.inl rfl
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover U hopen hcover
  apply (F.finite_toSet.preimage (show Function.Injective (Sum.inr : 𝒜 → Mrowka 𝒜)
    from Sum.inr_injective).injOn).subset
  intro A hA
  obtain ⟨p, hpF, hp⟩ := Set.mem_iUnion₂.mp (hF hA)
  cases p with
  | inl n => cases hp
  | inr B =>
    have hAB : A = B := by
      rcases hp with h | ⟨_, _, _, h⟩
      · exact Sum.inr.inj h
      · cases h
    simpa only [hAB] using hpF

variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem family_levelSet_finite (f : Space 𝕜 𝒜) {ε : ℝ} (hε : 0 < ε) :
    {A : 𝒜 | ε ≤ ‖f (Sum.inr A)‖}.Finite := by
  obtain ⟨C, hC, hsmall⟩ := hasBasis_cocompact.mem_iff.mp
    ((Metric.tendsto_nhds.mp (zero_at_infty f)) ε hε)
  apply (compact_familyPoints_finite 𝒜 hC).subset
  intro A hA
  by_contra hnot
  have hs := hsmall hnot
  exact (not_lt_of_ge hA) (by simpa using hs)

theorem familySupport_countable (f : Space 𝕜 𝒜) : (familySupport 𝕜 f).Countable := by
  have hc : (⋃ n : ℕ, {A : 𝒜 | 1 / ((n : ℝ) + 1) ≤ ‖f (Sum.inr A)‖}).Countable :=
    Set.countable_iUnion fun n => (family_levelSet_finite f (by positivity)).countable
  apply hc.mono
  intro A hA
  have hpos : 0 < ‖f (Sum.inr A)‖ := norm_pos_iff.mpr hA
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

/-- The forward direction of Lemma 4.3 does not require closedness or linearity. -/
theorem familySupportSet_countable_of_separable (X : Set (Space 𝕜 𝒜))
    [TopologicalSpace.SeparableSpace X] : (familySupportSet 𝕜 X).Countable := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense X
  letI := hD.to_subtype
  have hc : (⋃ f : D, familySupport 𝕜 f.val.val).Countable :=
    Set.countable_iUnion fun f => familySupport_countable f.val.val
  apply hc.mono
  rintro A ⟨f, hfX, hfA⟩
  have hcont : Continuous (fun g : X => g.val (Sum.inr A)) :=
    BoundedContinuousFunction.continuous_eval_const.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp continuous_subtype_val)
  have hopen : IsOpen {g : X | g.val (Sum.inr A) ≠ 0} :=
    isClosed_singleton.isOpen_compl.preimage hcont
  obtain ⟨g, hgD, hgA⟩ := hdense.exists_mem_open hopen ⟨⟨f, hfX⟩, hfA⟩
  exact Set.mem_iUnion.mpr ⟨⟨g, hgD⟩, hgA⟩

end Posets
