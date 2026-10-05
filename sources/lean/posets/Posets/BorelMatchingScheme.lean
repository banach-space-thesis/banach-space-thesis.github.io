import Posets.BorelMatchingSmall
import Mathlib.Topology.MetricSpace.Perfect

/-! Cantor schemes whose sibling branches have disjoint sets of coordinate values. -/
noncomputable section
open Set Filter Topology CantorScheme
open scoped ENNReal
namespace Posets

section SchemeMap
variable {Z Y : Type*}

def totalSchemeMap (D : List Bool → Set Z) (hdom : ∀ x, x ∈ (inducedMap D).1)
    (x : ℕ → Bool) : Z := (inducedMap D).2 ⟨x, hdom x⟩

theorem totalSchemeMap_mem (D : List Bool → Set Z) (hdom : ∀ x, x ∈ (inducedMap D).1)
    (x : ℕ → Bool) (n : ℕ) : totalSchemeMap D hdom x ∈ D (PiNat.res x n) :=
  CantorScheme.map_mem ⟨x, hdom x⟩ n

theorem coordinateDisjointScheme_pairwise (p q : Z → Y) (D : List Bool → Set Z)
    (hdom : ∀ x, x ∈ (inducedMap D).1)
    (hdisj : ∀ l : List Bool, Pairwise fun a b =>
      Disjoint (coordinateImage p q (D (a :: l))) (coordinateImage p q (D (b :: l)))) :
    Pairwise fun x y => Disjoint
      ({p (totalSchemeMap D hdom x), q (totalSchemeMap D hdom x)} : Set Y)
      {p (totalSchemeMap D hdom y), q (totalSchemeMap D hdom y)} := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro a hax hay
  apply hxy
  apply PiNat.res_injective
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [PiNat.res_succ, List.cons.injEq]
    refine ⟨?_, ih⟩
    by_contra hbit
    have hx := totalSchemeMap_mem D hdom x (n + 1)
    have hy := totalSchemeMap_mem D hdom y (n + 1)
    rw [PiNat.res_succ] at hx
    rw [PiNat.res_succ, ← ih] at hy
    exact Set.disjoint_left.mp (hdisj (PiNat.res x n) hbit)
      (coordinatePair_subset_coordinateImage hx hax)
      (coordinatePair_subset_coordinateImage hy hay)

end SchemeMap

section Splitting
variable {Z Y : Type*} [MetricSpace Z] [TopologicalSpace Y] [T1Space Y] [NormalSpace Y]

theorem small_open_refinement {U : Set Z} (hU : IsOpen U) {x : Z} (hx : x ∈ U)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set Z, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧ EMetric.diam V ≤ ε := by
  obtain ⟨W, ⟨hxW, hWo⟩, hWU⟩ :=
    (hasBasis_opens_closure x).mem_iff.mp (hU.mem_nhds hx)
  have hball : x ∈ EMetric.ball x (ε / 2) := by
    apply EMetric.mem_ball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt hε, by simp⟩
  refine ⟨W ∩ EMetric.ball x (ε / 2), hWo.inter EMetric.isOpen_ball,
    ⟨hxW, hball⟩, (closure_mono inter_subset_left).trans hWU, ?_⟩
  apply le_trans (EMetric.diam_mono inter_subset_right)
  convert EMetric.diam_ball (x := x)
  rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num

theorem coordinate_separated_open_split {p q : Z → Y} (hp : Continuous p) (hq : Continuous q)
    {U : Set Z} (hU : IsOpen U) (hn : U.Nonempty) (hs : ¬ CountablyCoordinateCovered p q U)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ U₀ U₁ : Set Z,
      (IsOpen U₀ ∧ U₀.Nonempty ∧ closure U₀ ⊆ U ∧ EMetric.diam U₀ ≤ ε) ∧
      (IsOpen U₁ ∧ U₁.Nonempty ∧ closure U₁ ⊆ U ∧ EMetric.diam U₁ ≤ ε) ∧
      Disjoint (coordinateImage p q U₀) (coordinateImage p q U₁) := by
  classical
  obtain ⟨x, hx⟩ := hn
  obtain ⟨y, hy, hxy⟩ := exists_disjoint_coordinate_pair hs x
  obtain ⟨V₀, V₁, hV₀, hV₁, hxV, hyV, hVV⟩ := normal_separation
    (((Set.finite_singleton (q x)).insert (p x)).isClosed)
    (((Set.finite_singleton (q y)).insert (p y)).isClosed) hxy
  have hO₀ : IsOpen (U ∩ p ⁻¹' V₀ ∩ q ⁻¹' V₀) :=
    (hU.inter (hV₀.preimage hp)).inter (hV₀.preimage hq)
  have hO₁ : IsOpen (U ∩ p ⁻¹' V₁ ∩ q ⁻¹' V₁) :=
    (hU.inter (hV₁.preimage hp)).inter (hV₁.preimage hq)
  obtain ⟨U₀, hU₀, hx₀, hcl₀, hd₀⟩ := small_open_refinement hO₀
    (show x ∈ U ∩ p ⁻¹' V₀ ∩ q ⁻¹' V₀ from
      ⟨⟨hx, hxV (by simp)⟩, hxV (by simp)⟩) hε
  obtain ⟨U₁, hU₁, hy₁, hcl₁, hd₁⟩ := small_open_refinement hO₁
    (show y ∈ U ∩ p ⁻¹' V₁ ∩ q ⁻¹' V₁ from
      ⟨⟨hy, hyV (by simp)⟩, hyV (by simp)⟩) hε
  refine ⟨U₀, U₁, ⟨hU₀, ⟨x, hx₀⟩, ?_, hd₀⟩,
    ⟨hU₁, ⟨y, hy₁⟩, ?_, hd₁⟩, ?_⟩
  · exact hcl₀.trans (inter_subset_left.trans inter_subset_left)
  · exact hcl₁.trans (inter_subset_left.trans inter_subset_left)
  · apply hVV.mono
    · rintro a (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact (hcl₀ (subset_closure hz)).1.2
      · exact (hcl₀ (subset_closure hz)).2
    · rintro a (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact (hcl₁ (subset_closure hz)).1.2
      · exact (hcl₁ (subset_closure hz)).2

end Splitting

/-- If no nonempty open set has a countable coordinate cover, a complete metric
parameter space contains a continuously parametrised Cantor family of disjoint edges. -/
theorem exists_cantor_coordinate_matching {Z Y : Type*} [MetricSpace Z] [CompleteSpace Z]
    [Nonempty Z] [TopologicalSpace Y] [T1Space Y] [NormalSpace Y]
    (p q : Z → Y) (hp : Continuous p) (hq : Continuous q)
    (hlarge : ∀ U : Set Z, IsOpen U → U.Nonempty → ¬ CountablyCoordinateCovered p q U) :
    ∃ f : (ℕ → Bool) → Z, Continuous f ∧
      Pairwise fun x y => Disjoint ({p (f x), q (f x)} : Set Y) {p (f y), q (f y)} := by
  classical
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let O := {U : Set Z // IsOpen U ∧ U.Nonempty}
  choose C₀ C₁ h₀ h₁ hsep using
    fun {U : Set Z} (hU : IsOpen U) (hn : U.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) =>
      coordinate_separated_open_split hp hq hU hn (hlarge U hU hn) hε
  let DP : List Bool → O := fun l => by
    induction l with
    | nil => exact ⟨univ, isOpen_univ, Set.univ_nonempty⟩
    | cons a l ih =>
      cases a
      · exact ⟨C₀ ih.property.1 ih.property.2 (upos (l.length + 1)),
          (h₀ _ _ _).1, (h₀ _ _ _).2.1⟩
      · exact ⟨C₁ ih.property.1 ih.property.2 (upos (l.length + 1)),
          (h₁ _ _ _).1, (h₁ _ _ _).2.1⟩
  let D : List Bool → Set Z := fun l => (DP l).val
  have hanti : ClosureAntitone D := by
    intro l a
    cases a
    · exact (h₀ _ _ _).2.2.1
    · exact (h₁ _ _ _).2.2.1
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m (hm : 1 ≤ m) => ?_⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    dsimp
    cases x n
    · convert (h₀ _ _ _).2.2.2
      rw [PiNat.res_length]
    · convert (h₁ _ _ _).2.2.2
      rw [PiNat.res_length]
  have hsepD : ∀ l : List Bool, Pairwise fun a b =>
      Disjoint (coordinateImage p q (D (a :: l))) (coordinateImage p q (D (b :: l))) := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hsep _ _ _
    · exact (hsep _ _ _).symm
  have hdom : ∀ x : ℕ → Bool, x ∈ (inducedMap D).1 := by
    intro x
    rw [hanti.map_of_vanishingDiam hdiam (fun l => (DP l).property.2)]
    trivial
  refine ⟨totalSchemeMap D hdom, ?_, coordinateDisjointScheme_pairwise p q D hdom hsepD⟩
  apply hdiam.map_continuous.comp
  fun_prop

end Posets
