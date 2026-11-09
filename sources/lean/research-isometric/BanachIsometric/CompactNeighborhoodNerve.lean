import BanachIsometric.FiniteNervePolyhedron
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Homotopy.Basic

/-! Actual finite-nerve domination of a compact neighborhood retract.
Finite small balls, an actual partition of unity and retracted affine
interpolation construct the two maps and their literal homotopy. No CW,
cohomology, rational comparison or finite-type premise is used. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open Set Metric
open scoped Topology unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Set E}

open Classical in
def coverComplex (c : ι → s) (ε : ℝ) : Complex ι where
  faces := Finset.univ.filter (fun a => a.Nonempty ∧
    ∃ x : s, ∀ i ∈ a, dist (c i : E) (x : E) < ε)
  nonempty := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2.1
  downward := by
    intro a ha b hba hb
    obtain ⟨_hne, x, hx⟩ := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, x, fun i hi => hx i (hba hi)⟩

omit [NormedSpace ℝ E] in
theorem mem_coverComplex_space_iff (c : ι → s) (ε : ℝ) (w : ι → ℝ) :
    w ∈ (coverComplex c ε).space ↔
      w ∈ stdSimplex ℝ ι ∧ ∃ x : s, ∀ i, w i ≠ 0 → dist (c i : E) (x : E) < ε := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha, hw⟩ := (Complex.mem_space_iff _ _).mp h
    obtain ⟨_hne, x, hx⟩ := (Finset.mem_filter.mp ha).2
    refine ⟨hw.1, x, ?_⟩
    intro i hi
    exact hx i (by by_contra hia; exact hi (hw.2 i hia))
  · rintro ⟨hw, x, hx⟩
    let a := Finset.univ.filter (fun i => w i ≠ 0)
    have ha : a.Nonempty := by
      by_contra h
      have hz : ∀ i, w i = 0 := by
        intro i
        by_contra hi
        exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have hh := hw.2
      simp only [hz, Finset.sum_const_zero] at hh
      exact zero_ne_one hh
    apply (Complex.mem_space_iff _ _).mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, x, ?_⟩, hw, ?_⟩
    · intro i hi
      exact hx i (Finset.mem_filter.mp hi).2
    · intro i hi
      by_contra hwi
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩)

def evaluate (c : ι → E) (w : ι → ℝ) : E := ∑ i, w i • c i

omit [DecidableEq ι] in
theorem continuous_evaluate (c : ι → E) : Continuous (evaluate c) :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

omit [DecidableEq ι] in
theorem evaluate_mem_ball (c : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    {x : E} {ε : ℝ} (hε : 0 < ε)
    (hnear : ∀ i, w i ≠ 0 → dist (c i) x < ε) : evaluate c w ∈ ball x ε := by
  classical
  let z : ι → E := fun i => if w i = 0 then x else c i
  have hz : ∀ i, z i ∈ ball x ε := by
    intro i
    by_cases hi : w i = 0
    · simpa only [z, if_pos hi, mem_ball, dist_self] using hε
    · simpa only [z, if_neg hi, mem_ball] using hnear i hi
  have heq : ∑ i, w i • z i = evaluate c w := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : w i = 0 <;> simp [z, hi]
  rw [← heq]
  exact (convex_ball x ε).sum_mem (fun i _ => hw.1 i) hw.2 (fun i _ => hz i)

omit [NormedSpace ℝ E] in
theorem exists_finite_ball_centers {s : Set E} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ c : Fin n → s, ∀ x : s, ∃ i, dist (c i : E) (x : E) < ε := by
  classical
  obtain ⟨t, hts, ht, hcover⟩ := hs.finite_cover_balls hε
  letI : Fintype t := ht.fintype
  let e := Fintype.equivFin t
  let c : Fin (Fintype.card t) → s := fun i => ⟨(e.symm i).val, hts (e.symm i).property⟩
  refine ⟨Fintype.card t, c, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover x.property)
  refine ⟨e ⟨y, hy⟩, ?_⟩
  simpa only [c, e.symm_apply_apply, mem_ball, dist_comm] using hxy

def barycentricMap (c : ι → s) (ε : ℝ) (ρ : PartitionOfUnity ι s univ)
    (hnear : ∀ x : s, ∀ i, ρ i x ≠ 0 → dist (c i : E) (x : E) < ε) :
    C(s, (coverComplex c ε).space) where
  toFun x := ⟨fun i => ρ i x, (mem_coverComplex_space_iff c ε _).mpr
    ⟨⟨fun i => ρ.nonneg i x, by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)⟩,
      x, hnear x⟩⟩
  continuous_toFun := (continuous_pi fun i => (ρ i).continuous).subtype_mk _

/-- A compact subset of a real normed space which is an actual neighborhood
retract is dominated by a genuine finite coordinate simplicial polyhedron.
The maps and the actual homotopy are constructed here. -/
theorem exists_finite_nerve_domination {s U : Set E}
    (hs : IsCompact s) (hU : IsOpen U) (hsU : s ⊆ U)
    (r : E → E) (hr : ContinuousOn r U) (hrange : ∀ x ∈ U, r x ∈ s)
    (hfix : ∀ x ∈ s, r x = x) :
    ∃ n : ℕ, ∃ K : Complex (Fin n), ∃ f : C(s, K.space), ∃ g : C(K.space, s),
      Nonempty ((g.comp f).Homotopy (ContinuousMap.id s)) := by
  classical
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  obtain ⟨ε, hε, htube⟩ := hs.exists_cthickening_subset_open hU hsU
  obtain ⟨n, c, hcover⟩ := exists_finite_ball_centers hs hε
  let V : Fin n → Set s := fun i => Subtype.val ⁻¹' ball (c i : E) ε
  have hV : ∀ i, IsOpen (V i) := fun i => isOpen_ball.preimage continuous_subtype_val
  have hcov : (univ : Set s) ⊆ ⋃ i, V i := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, by simpa only [V, mem_preimage, mem_ball, dist_comm] using hi⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ V hV hcov
  have hnear (x : s) (i : Fin n) (hi : ρ i x ≠ 0) : dist (c i : E) (x : E) < ε := by
    have hx := hρ i (subset_closure (show x ∈ Function.support (ρ i) from hi))
    simpa only [V, mem_preimage, mem_ball, dist_comm] using hx
  let K := coverComplex c ε
  let f : C(s, K.space) := barycentricMap c ε ρ hnear
  have hevalU (w : K.space) : evaluate (fun i => (c i : E)) w.val ∈ U := by
    obtain ⟨hw, x, hx⟩ := (mem_coverComplex_space_iff c ε w.val).mp w.property
    have hn := evaluate_mem_ball (fun i => (c i : E)) hw hε hx
    exact htube (mem_cthickening_of_dist_le _ x.val ε s x.property hn.le)
  let g : C(K.space, s) :=
    ⟨fun w => ⟨r (evaluate (fun i => (c i : E)) w.val), hrange _ (hevalU w)⟩,
      (hr.comp_continuous ((continuous_evaluate _).comp continuous_subtype_val) hevalU).subtype_mk _⟩
  let B : s → E := fun x => evaluate (fun i => (c i : E)) (f x).val
  have hB : Continuous B :=
    (continuous_evaluate _).comp (continuous_subtype_val.comp f.continuous)
  have hBnear (x : s) : B x ∈ ball x.val ε :=
    evaluate_mem_ball (fun i => (c i : E))
      ⟨fun i => ρ.nonneg i x, by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)⟩
      hε (hnear x)
  let J : unitInterval × s → E := fun z => (1 - (z.1 : ℝ)) • B z.2 + (z.1 : ℝ) • z.2.val
  have hJ : Continuous J := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hB.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd))
  have hJU (z : unitInterval × s) : J z ∈ U := by
    have hball : J z ∈ ball z.2.val ε :=
      (convex_ball z.2.val ε) (hBnear z.2) (mem_ball_self hε)
        (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)
    exact htube (mem_cthickening_of_dist_le _ z.2.val ε s z.2.property hball.le)
  refine ⟨n, K, f, g, ⟨{
    toFun := fun z => ⟨r (J z), hrange _ (hJU z)⟩
    continuous_toFun := (hr.comp_continuous hJ hJU).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    apply Subtype.ext
    change r ((1 - (0 : ℝ)) • B x + (0 : ℝ) • x.val) = r (B x)
    simp
  · intro x
    apply Subtype.ext
    change r ((1 - (1 : ℝ)) • B x + (1 : ℝ) • x.val) = x.val
    simpa using hfix x.val x.property

end BanachIsometric.FiniteNerve
