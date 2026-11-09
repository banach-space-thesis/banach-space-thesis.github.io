import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Continuous Cantor lifting

A continuous map on a Polish space whose image is uncountable admits a
continuous Cantor lifting on which its image map is injective. Applied to
projection from a closed factorisation relation, this gives the continuous
factor selection used in the paper without measurable uniformisation.
-/

noncomputable section

open Set Function Filter Topology TopologicalSpace
open scoped ENNReal

namespace CKEUPFP

private theorem exists_image_condensation_kernel
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (f : X → Y) {C : Set X} (hC : IsClosed C) (hunc : ¬ (f '' C).Countable) :
    ∃ D : Set X, IsClosed D ∧ D ⊆ C ∧ ¬ (f '' D).Countable ∧
      ∀ x ∈ D, ∀ U ∈ 𝓝 x, ¬ (f '' (U ∩ D)).Countable := by
  classical
  obtain ⟨b, hbcount, _, hbbasis⟩ := exists_countable_basis X
  let v := {U ∈ b | (f '' (U ∩ C)).Countable}
  let V := ⋃ U ∈ v, U
  let D := C \ V
  have hVcount : (f '' (V ∩ C)).Countable := by
    simp only [V, iUnion_inter, image_iUnion]
    apply Set.Countable.biUnion
    · exact hbcount.mono inter_subset_left
    · exact fun U hU => hU.2
  have hDclosed : IsClosed D := by
    refine hC.sdiff (isOpen_biUnion fun U hU => ?_)
    exact hbbasis.isOpen hU.1
  have hDunc : ¬ (f '' D).Countable := by
    intro h
    apply hunc
    apply (h.union hVcount).mono
    rintro y ⟨x, hx, rfl⟩
    by_cases hxV : x ∈ V
    · exact Or.inr ⟨x, ⟨hxV, hx⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx, hxV⟩, rfl⟩
  refine ⟨D, hDclosed, diff_subset, hDunc, ?_⟩
  intro x hx U hU hcount
  obtain ⟨B, hBb, hxB, hBU⟩ := hbbasis.mem_nhds_iff.mp hU
  have hBcount : (f '' (B ∩ C)).Countable := by
    apply (hcount.union hVcount).mono
    rintro y ⟨z, ⟨hzB, hzC⟩, rfl⟩
    by_cases hzV : z ∈ V
    · exact Or.inr ⟨z, ⟨hzV, hzC⟩, rfl⟩
    · exact Or.inl ⟨z, ⟨hBU hzB, ⟨hzC, hzV⟩⟩, rfl⟩
  exact hx.2 (mem_biUnion ⟨hBb, hBcount⟩ hxB)

private theorem uncountable_image_small_splitting
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T25Space Y]
    (f : X → Y) (hf : Continuous f) {C : Set X}
    (hC : IsClosed C) (hunc : ¬ (f '' C).Countable)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C₀ C₁ : Set X,
      (IsClosed C₀ ∧ C₀ ⊆ C ∧ ¬ (f '' C₀).Countable ∧ EMetric.diam C₀ ≤ ε) ∧
      (IsClosed C₁ ∧ C₁ ⊆ C ∧ ¬ (f '' C₁).Countable ∧ EMetric.diam C₁ ≤ ε) ∧
      Disjoint (f '' C₀) (f '' C₁) := by
  classical
  obtain ⟨D, hDclosed, hDC, hDunc, hDlocal⟩ :=
    exists_image_condensation_kernel f hC hunc
  have hDnon : D.Nonempty := by
    by_contra h
    have hDempty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hDempty, image_empty] at hDunc
    exact hDunc Set.countable_empty
  obtain ⟨x, hx⟩ := hDnon
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ D, f x ≠ f y := by
    by_contra! h
    apply hDunc
    apply (Set.countable_singleton (f x)).mono
    rintro z ⟨y, hy, rfl⟩
    exact Set.mem_singleton_iff.mpr (h y hy).symm
  obtain ⟨U, hxU, hUopen, W, hyW, hWopen, hUW⟩ :=
    exists_open_nhds_disjoint_closure hxy
  have hrad : 0 < ε / 2 := by
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt hε, by simp⟩
  have make_child (z : X) (hz : z ∈ D) (O : Set Y) (hzO : f z ∈ O)
      (hOopen : IsOpen O) :
      ∃ C' : Set X, IsClosed C' ∧ C' ⊆ C ∧ ¬ (f '' C').Countable ∧
        EMetric.diam C' ≤ ε ∧ f '' C' ⊆ closure O := by
    let N := EMetric.ball z (ε / 2) ∩ f ⁻¹' O
    have hNopen : IsOpen N := EMetric.isOpen_ball.inter (hOopen.preimage hf)
    have hzN : z ∈ N := ⟨EMetric.mem_ball_self hrad, hzO⟩
    let C' := closure (N ∩ D)
    refine ⟨C', isClosed_closure, ?_, ?_, ?_, ?_⟩
    · exact (hDclosed.closure_subset_iff.mpr inter_subset_right).trans hDC
    · intro hcount
      exact hDlocal z hz N (hNopen.mem_nhds hzN)
        (hcount.mono (image_mono subset_closure))
    · rw [EMetric.diam_closure]
      calc
        EMetric.diam (N ∩ D) ≤ EMetric.diam (EMetric.ball z (ε / 2)) :=
          EMetric.diam_mono (inter_subset_left.trans inter_subset_left)
        _ ≤ ε := by
          convert EMetric.diam_ball (x := z)
          rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num
    · apply image_subset_iff.mpr
      apply (isClosed_closure.preimage hf).closure_subset_iff.mpr
      exact fun z hz => subset_closure hz.1.2
  obtain ⟨C₀, h₀closed, h₀C, h₀unc, h₀diam, h₀U⟩ := make_child x hx U hxU hUopen
  obtain ⟨C₁, h₁closed, h₁C, h₁unc, h₁diam, h₁W⟩ := make_child y hy W hyW hWopen
  exact ⟨C₀, C₁, ⟨h₀closed, h₀C, h₀unc, h₀diam⟩,
    ⟨h₁closed, h₁C, h₁unc, h₁diam⟩, hUW.mono h₀U h₁W⟩

/-- A continuous map on a Polish space with uncountable image admits a
continuous lift of a Cantor subset of that image. In particular, the image
coordinates of the lift are pairwise distinct. -/
theorem continuous_cantor_lift_of_uncountable_range
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T25Space Y]
    (f : X → Y) (hf : Continuous f) (hunc : ¬ (Set.range f).Countable) :
    ∃ g : (ℕ → Bool) → X, Continuous g ∧ Function.Injective (f ∘ g) := by
  classical
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let P := {C : Set X // IsClosed C ∧ ¬ (f '' C).Countable}
  choose C₀ C₁ h₀ h₁ hdisjoint using
    fun {C : Set X} (hC : IsClosed C) (hCu : ¬ (f '' C).Countable)
      {ε : ℝ≥0∞} (hε : 0 < ε) =>
        uncountable_image_small_splitting f hf hC hCu hε
  let DP : List Bool → P := fun l => by
    induction l with
    | nil => exact ⟨Set.univ, isClosed_univ, by simpa only [image_univ] using hunc⟩
    | cons a l ih =>
      cases a
      · exact ⟨C₀ ih.property.1 ih.property.2 (upos (l.length + 1)),
          (h₀ _ _ _).1, (h₀ _ _ _).2.2.1⟩
      · exact ⟨C₁ ih.property.1 ih.property.2 (upos (l.length + 1)),
          (h₁ _ _ _).1, (h₁ _ _ _).2.2.1⟩
  let D : List Bool → Set X := fun l => (DP l).val
  have hanti : CantorScheme.ClosureAntitone D := by
    refine CantorScheme.Antitone.closureAntitone ?_ fun l => (DP l).property.1
    intro l a
    cases a
    · exact (h₀ _ _ _).2.1
    · exact (h₁ _ _ _).2.1
  have hdiam : CantorScheme.VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m hm => ?_⟩
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm) with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert (h₀ _ _ _).2.2.2
      rw [PiNat.res_length]
    · convert (h₁ _ _ _).2.2.2
      rw [PiNat.res_length]
  have hnonempty : ∀ l, (D l).Nonempty := by
    intro l
    by_contra h
    have hempty : D l = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h := (DP l).property.2
    change ¬ (f '' D l).Countable at h
    rw [hempty, image_empty] at h
    exact h Set.countable_empty
  have hdom : ∀ {x : ℕ → Bool}, x ∈ (CantorScheme.inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam hnonempty]
    apply mem_univ
  let g := fun x => (CantorScheme.inducedMap D).2 ⟨x, hdom⟩
  refine ⟨g, hdiam.map_continuous.comp (by fun_prop), ?_⟩
  intro x y hxy
  apply PiNat.res_injective
  ext n : 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [PiNat.res_succ, List.cons.injEq]
    refine ⟨?_, ih⟩
    by_contra hne
    have hsplit : Disjoint (f '' D (x n :: PiNat.res x n))
        (f '' D (y n :: PiNat.res x n)) := by
      cases hx : x n <;> cases hy : y n <;> simp_all only [not_true_eq_false]
      · exact hdisjoint _ _ _
      · exact (hdisjoint _ _ _).symm
    apply Set.disjoint_left.mp hsplit
    · exact ⟨g x, CantorScheme.map_mem ⟨x, hdom⟩ (n + 1), rfl⟩
    · refine ⟨g y, ?_, ?_⟩
      · rw [ih, ← PiNat.res_succ]
        exact CantorScheme.map_mem ⟨y, hdom⟩ (n + 1)
      · exact hxy.symm

/-- A closed relation between Polish spaces with uncountable projection has
continuous choices on an embedded Cantor set in the first coordinate. -/
theorem closed_relation_continuous_cantor_selection
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    {Γ : Set (X × Y)} (hΓ : IsClosed Γ)
    (hunc : ¬ (Prod.fst '' Γ).Countable) :
    ∃ (e : (ℕ → Bool) → X) (s : (ℕ → Bool) → Y),
      Continuous e ∧ Function.Injective e ∧ Continuous s ∧
      ∀ x, (e x, s x) ∈ Γ := by
  letI : PolishSpace Γ := hΓ.polishSpace
  let p : Γ → X := fun z => z.val.1
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hpu : ¬ (Set.range p).Countable := by
    have hpimage : Set.range p = Prod.fst '' Γ := by
      ext x
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.val, z.property, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    rwa [hpimage]
  obtain ⟨g, hg, hginj⟩ := continuous_cantor_lift_of_uncountable_range p hp hpu
  refine ⟨fun x => (g x).val.1, fun x => (g x).val.2,
    hp.comp hg, hginj, ?_, fun x => (g x).property⟩
  exact continuous_snd.comp (continuous_subtype_val.comp hg)

/-- A Borel map from an uncountable Polish space is continuous after
restriction along some Cantor embedding. This is the exact refinement needed
for the paper's Borel diagonal atom field. -/
theorem measurable_continuous_on_cantor
    {X Y : Type*} [t : TopologicalSpace X] [PolishSpace X] [Uncountable X]
    [MeasurableSpace X] [BorelSpace X]
    [tY : TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ e : (ℕ → Bool) → X,
      Continuous e ∧ Function.Injective e ∧ Continuous (f ∘ e) := by
  obtain ⟨t', hle, hf', hpolish⟩ := hf.exists_continuous
  have hid : @Continuous X X t' t id := continuous_id_of_le hle
  have hunc : ¬ (Set.range (id : X → X)).Countable := by
    simpa only [Set.range_id] using Set.not_countable_univ (α := X)
  obtain ⟨e, he, heinj⟩ :=
    @continuous_cantor_lift_of_uncountable_range X X t' hpolish t inferInstance
      id hid hunc
  exact ⟨e,
    @Continuous.comp (ℕ → Bool) X X _ t' t e id hid he,
    heinj,
    @Continuous.comp (ℕ → Bool) X Y _ t' tY e f hf' he⟩

/-- The perfect set theorem for analytic sets, expressed as a continuous
Cantor injection whose image lies in the given analytic set. -/
theorem analytic_set_contains_cantor
    {X : Type*} [TopologicalSpace X] [T25Space X]
    {S : Set X} (hS : MeasureTheory.AnalyticSet S) (hunc : ¬ S.Countable) :
    ∃ e : (ℕ → Bool) → X,
      Continuous e ∧ Function.Injective e ∧ Set.range e ⊆ S := by
  obtain ⟨Z, tZ, hZpolish, f, hf, hfrange⟩ :=
    MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hS
  letI : TopologicalSpace Z := tZ
  letI : PolishSpace Z := hZpolish
  have hfu : ¬ (Set.range f).Countable := by rwa [hfrange]
  obtain ⟨g, hg, hginj⟩ := continuous_cantor_lift_of_uncountable_range f hf hfu
  refine ⟨f ∘ g, hf.comp hg, hginj, ?_⟩
  rintro x ⟨z, rfl⟩
  rw [← hfrange]
  exact ⟨g z, rfl⟩

/-- A Borel map is continuous on some Cantor subset of any uncountable Borel
set in its Polish domain. This directly supplies the paper's simultaneous
Borel-set and diagonal-field refinement. -/
theorem measurable_continuous_on_cantor_subset
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [T3Space Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : X → Y) (hf : Measurable f)
    {S : Set X} (hS : MeasurableSet S) (hunc : ¬ S.Countable) :
    ∃ e : (ℕ → Bool) → X,
      Continuous e ∧ Function.Injective e ∧ Continuous (f ∘ e) ∧ Set.range e ⊆ S := by
  classical
  let q : X → X × Y := fun x => (x, f x)
  have hq : Measurable q := measurable_id.prodMk hf
  have hgraph : MeasureTheory.AnalyticSet (q '' S) := hS.analyticSet_image hq
  have hgraphunc : ¬ (q '' S).Countable := by
    intro h
    apply hunc
    have hprojection : Prod.fst '' (q '' S) = S := by
      rw [← image_comp]
      exact image_id S
    rw [← hprojection]
    exact h.image Prod.fst
  obtain ⟨g, hg, hginj, hgS⟩ := analytic_set_contains_cantor hgraph hgraphunc
  have hgs (x : ℕ → Bool) : g x ∈ q '' S := hgS ⟨x, rfl⟩
  have hgfst (x : ℕ → Bool) : (g x).1 ∈ S := by
    obtain ⟨z, hz, hzg⟩ := hgs x
    simpa only [← hzg] using hz
  have hgsnd (x : ℕ → Bool) : (g x).2 = f (g x).1 := by
    obtain ⟨z, hz, hzg⟩ := hgs x
    rw [← hzg]
  refine ⟨Prod.fst ∘ g, continuous_fst.comp hg, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hginj
    apply Prod.ext hxy
    rw [hgsnd x, hgsnd y]
    exact congrArg f hxy
  · have heq : f ∘ (Prod.fst ∘ g) = Prod.snd ∘ g := by
      ext x
      exact (hgsnd x).symm
    rw [heq]
    exact continuous_snd.comp hg
  · rintro x ⟨z, rfl⟩
    exact hgfst z

end CKEUPFP
