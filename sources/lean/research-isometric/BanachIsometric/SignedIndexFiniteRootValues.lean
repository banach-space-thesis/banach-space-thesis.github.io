import BanachIsometric.SignedIndexRootBoxes

/-!
# The global actual index is the sum of its actual local root indices

Disjoint root boxes and compact source excision are constructed internally.
Finite additivity is the proved identity for actual signed counts. Local
values on sufficiently small root boxes are the only input to this gluing
lemma; the regular-value theorem supplies those values by linearization.
-/

namespace BanachIsometric

open MeasureTheory Set Metric Filter
open scoped Topology NNReal BigOperators

noncomputable section

abbrev ActualBoxFiber {n : ℕ} (f : PiolaSpace n → PiolaSpace n) (a b c : PiolaSpace n) :=
  {x : PiolaSpace n // x ∈ Icc a b ∧ f x = c}

theorem localSignedIndex_eq_sum_of_local_root_values
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b c : PiolaSpace n) (hab : a ≤ b)
    (hc : c ∉ f '' piolaBoxBoundary a b) [Fintype (ActualBoxFiber f a b c)]
    (d : ActualBoxFiber f a b c → ℤ)
    (hloc : ∀ x : ActualBoxFiber f a b c, ∃ r > 0, ∀ s : ℝ, 0 < s → s ≤ r →
      localSignedIndex f (x.val - s • (1 : PiolaSpace n)) (x.val + s • 1) c = d x) :
    localSignedIndex f a b c = ∑ x : ActualBoxFiber f a b c, d x := by
  classical
  let R := ActualBoxFiber f a b c
  choose r hr hlocal using hloc
  have hfin : {x : PiolaSpace n | x ∈ Icc a b ∧ f x = c}.Finite := by
    apply finite_coe_iff.mp
    change Finite (ActualBoxFiber f a b c)
    infer_instance
  obtain ⟨s, hs, hinside, hdis, δ, hδ, hsource⟩ := exists_disjoint_compact_fiber_balls
    hf.continuous isCompact_Icc c hfin
    (fun x hx hxc => root_mem_interior_of_avoids_boxBoundary f a b c hc ⟨x, hx, hxc⟩) r hr
  have hsub (x : R) : closedBall x.val (s x) ⊆ Icc a b :=
    fun z hz => interior_subset (hinside x hz)
  have havoid (x : R) : c ∉ f '' piolaBoxBoundary
      (x.val - s x • (1 : PiolaSpace n)) (x.val + s x • 1) :=
    root_ball_boundary_avoids_target f (Icc a b) c s (fun y => (hs y).1) hsub hdis x
  have hlocalIndex (x : R) : IsLocalSignedIndex f
      (x.val - s x • (1 : PiolaSpace n)) (x.val + s x • 1) c (d x) := by
    have h := localSignedIndex_spec hf
      (x.val - s x • (1 : PiolaSpace n)) (x.val + s x • 1)
      (piola_centeredBox_lower_le_upper x.val (hs x).1.le) c (havoid x)
    rw [hlocal x (s x) (hs x).1 (hs x).2] at h
    exact h
  choose ε hε hcount using hlocalIndex
  have hballs (x : R) : ∀ᵐ y, y ∈ ball c (ε x) →
      signedFiberCount f (fderiv ℝ f) (closedBall x.val (s x)) y = d x := by
    simpa only [closedBall_piola_eq_Icc x.val (s x) (hs x).1.le] using hcount x
  have hcounts : ∀ᵐ y, ∀ x : R, y ∈ ball c (ε x) →
      signedFiberCount f (fderiv ℝ f) (closedBall x.val (s x)) y = d x :=
    Filter.eventually_all.mpr hballs
  have hnear : {y | ∀ x : R, y ∈ ball c (ε x)} ∈ 𝓝 c :=
    Filter.eventually_all.mpr (fun x => ball_mem_nhds c (hε x))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hadd := ae_signedFiberCount_fintype_union_of_disjoint volume hf
    (fun x : R => closedBall x.val (s x)) (fun _ => isCompact_closedBall _ _) hdis
  apply localSignedIndex_eq_of_ae_eq_on_ball hf a b hab c hc (lt_min hδ hη)
  filter_upwards [hadd, hcounts] with y hyadd hycounts
  intro hy
  have hyδ : y ∈ ball c δ := ball_subset_ball (min_le_left δ η) hy
  have hyη : y ∈ ball c η := ball_subset_ball (min_le_right δ η) hy
  rw [signedFiberCount_congr_source_on_fiber f (fderiv ℝ f) y
    (fun z hzy => hsource y hyδ z hzy), hyadd]
  exact Finset.sum_congr rfl (fun x _ => hycounts x (hηsub hyη x))

end

end BanachIsometric
