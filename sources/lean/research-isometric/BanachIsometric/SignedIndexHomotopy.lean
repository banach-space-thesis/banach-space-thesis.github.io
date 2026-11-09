import BanachIsometric.SignedIndexIntegral
import BanachIsometric.LipschitzHomotopyIntegral

/-!
# Actual homotopy invariance of the canonical local signed index

A common unit-mass smooth target bump fits inside both endpoint index
neighborhoods and avoids the compact total boundary image. The proved
Lipschitz homotopy integral identity then equates the two actual integer
indices. No degree or invariance property is assumed.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

theorem localSignedIndex_homotopy_eq_of_lipschitz
    {P : Type*} [PseudoMetricSpace P] [CompactSpace P] [PreconnectedSpace P]
    {n : ℕ} [NeZero n] (H : P → PiolaSpace n → PiolaSpace n)
    (hLip : ∀ p, ∃ C : ℝ≥0, LipschitzWith C (H p))
    (a b : PiolaSpace n) (hab : a ≤ b)
    (hH : Continuous (fun z : P × piolaBoxBoundary a b => H z.1 z.2))
    (c : PiolaSpace n) (hboundary : ∀ p, c ∉ H p '' piolaBoxBoundary a b)
    (p q : P) : localSignedIndex (H p) a b c = localSignedIndex (H q) a b c := by
  letI : CompactSpace (piolaBoxBoundary a b) :=
    isCompact_iff_compactSpace.mp (isCompact_piolaBoxBoundary a b)
  let F : P × piolaBoxBoundary a b → PiolaSpace n := fun z => H z.1 z.2
  have hF : Continuous F := hH
  have hc : c ∉ Set.range F := by
    rintro ⟨⟨u, x⟩, hux⟩
    exact hboundary u ⟨x.val, x.property, hux⟩
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp
    (isCompact_range hF).isClosed.isOpen_compl c hc
  have hsep : ∀ u, ∀ x ∈ piolaBoxBoundary a b, δ ≤ dist (H u x) c := by
    intro u x hx
    apply le_of_not_gt
    intro hdist
    exact hδball (mem_ball.mpr hdist) ⟨(u, ⟨x, hx⟩), rfl⟩
  obtain ⟨Cp, hCp⟩ := hLip p
  obtain ⟨Cq, hCq⟩ := hLip q
  obtain ⟨r, hr, hp⟩ := exists_localSignedIndex_integral_radius hCp a b hab c (hboundary p)
  obtain ⟨s, hs, hq⟩ := exists_localSignedIndex_integral_radius hCq a b hab c (hboundary q)
  let R : ℝ := min δ (min r s)
  have hR : 0 < R := lt_min hδ (lt_min hr hs)
  let φ : ContDiffBump c := ⟨R / 4, R / 2, by positivity, by linarith⟩
  have hφδ : φ.rOut < δ := by
    have hle : R ≤ δ := min_le_left _ _
    change R / 2 < δ
    linarith
  have hφr : φ.rOut ≤ r := by
    have hle : R ≤ r := (min_le_right δ (min r s)).trans (min_le_left r s)
    change R / 2 ≤ r
    linarith
  have hφs : φ.rOut ≤ s := by
    have hle : R ≤ s := (min_le_right δ (min r s)).trans (min_le_right r s)
    change R / 2 ≤ s
    linarith
  have hψboundary : ∀ u, ∀ x ∈ piolaBoxBoundary a b, H u x ∉ tsupport (φ.normed volume) := by
    intro u x hx hmem
    rw [φ.tsupport_normed_eq] at hmem
    have hle := mem_closedBall.mp hmem
    have hge := hsep u x hx
    linarith
  have hIp := hp (φ.normed volume) φ.continuous_normed (by
    rw [φ.support_normed_eq]
    exact ball_subset_ball hφr)
  have hIq := hq (φ.normed volume) φ.continuous_normed (by
    rw [φ.support_normed_eq]
    exact ball_subset_ball hφs)
  rw [φ.integral_normed, mul_one] at hIp hIq
  have hhom := integral_signedJacobian_homotopy_eq_of_lipschitz H hLip a b hab hH
    (φ.contDiff_normed (n := 1)) hψboundary p q
  have hcast : (localSignedIndex (H p) a b c : ℝ) = (localSignedIndex (H q) a b c : ℝ) :=
    hIp.symm.trans (hhom.trans hIq)
  exact_mod_cast hcast

end BanachIsometric
