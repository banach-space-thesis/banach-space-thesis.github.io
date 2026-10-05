import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

/-! A concrete concave envelope on the nonnegative half-line, defined
by the convex hull of the positive hypograph. For functions between zero
and the identity, every vertical fiber is nonempty and bounded. -/
noncomputable section
namespace ThesisCommon

def positiveHypograph (H : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ H p.1}

def concaveEnvelopeValues (H : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | (x, y) ∈ convexHull ℝ (positiveHypograph H)}

def positiveConcaveEnvelope (H : ℝ → ℝ) (x : ℝ) : ℝ := sSup (concaveEnvelopeValues H x)

theorem positiveHypograph_hull_bounds {H : ℝ → ℝ}
    (hH : ∀ x, 0 ≤ x → H x ≤ x) {p : ℝ × ℝ}
    (hp : p ∈ convexHull ℝ (positiveHypograph H)) :
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1 := by
  have hc : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1} := by
    rintro ⟨x, u⟩ ⟨hx, hu, hux⟩ ⟨y, v⟩ ⟨hy, hv, hvy⟩ a b ha hb _
    change 0 ≤ a * x + b * y ∧ 0 ≤ a * u + b * v ∧ a * u + b * v ≤ a * x + b * y
    exact ⟨add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy),
      add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hv),
      add_le_add (mul_le_mul_of_nonneg_left hux ha) (mul_le_mul_of_nonneg_left hvy hb)⟩
  have hs : positiveHypograph H ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1} :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans (hH p.1 hp.1)⟩
  exact convexHull_min hs hc hp

theorem concaveEnvelopeValues_nonempty {H : ℝ → ℝ}
    (hH : ∀ x, 0 ≤ x → 0 ≤ H x) {x : ℝ} (hx : 0 ≤ x) :
    (concaveEnvelopeValues H x).Nonempty :=
  ⟨H x, subset_convexHull ℝ _ ⟨hx, hH x hx, le_rfl⟩⟩

theorem concaveEnvelopeValues_bddAbove {H : ℝ → ℝ}
    (hH : ∀ x, 0 ≤ x → H x ≤ x) (x : ℝ) : BddAbove (concaveEnvelopeValues H x) :=
  ⟨x, fun _ hy => (positiveHypograph_hull_bounds hH hy).2.2⟩

theorem le_positiveConcaveEnvelope {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    {x : ℝ} (hx : 0 ≤ x) : H x ≤ positiveConcaveEnvelope H x :=
  le_csSup (concaveEnvelopeValues_bddAbove hH1 x)
    (subset_convexHull ℝ _ ⟨hx, hH0 x hx, le_rfl⟩)

theorem positiveConcaveEnvelope_nonneg {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ positiveConcaveEnvelope H x :=
  (hH0 x hx).trans (le_positiveConcaveEnvelope hH0 hH1 hx)

theorem positiveConcaveEnvelope_le_id {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x)
    {x : ℝ} (hx : 0 ≤ x) : positiveConcaveEnvelope H x ≤ x :=
  csSup_le (concaveEnvelopeValues_nonempty hH0 hx)
    (fun _ hy => (positiveHypograph_hull_bounds hH1 hy).2.2)

theorem positiveConcaveEnvelope_le_of_concave {H U : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hU : ConcaveOn ℝ (Set.Ici 0) U)
    (hHU : ∀ x, 0 ≤ x → H x ≤ U x) {x : ℝ} (hx : 0 ≤ x) :
    positiveConcaveEnvelope H x ≤ U x := by
  apply csSup_le (concaveEnvelopeValues_nonempty hH0 hx)
  intro y hy
  have hs : positiveHypograph H ⊆ {p : ℝ × ℝ | p.1 ∈ Set.Ici 0 ∧ p.2 ≤ U p.1} :=
    fun p hp => ⟨hp.1, hp.2.2.trans (hHU p.1 hp.1)⟩
  exact (convexHull_min hs hU.convex_hypograph hy).2

theorem affine_csSup_le {S : Set ℝ} (hS : S.Nonempty) {a b c : ℝ}
    (ha : 0 ≤ a) (h : ∀ x ∈ S, a * x + b ≤ c) : a * sSup S + b ≤ c := by
  rcases ha.eq_or_lt with rfl | ha
  · obtain ⟨x, hx⟩ := hS
    simpa using h x hx
  · have hs : sSup S ≤ (c - b) / a := by
      apply csSup_le hS
      intro x hx
      apply (le_div_iff₀ ha).mpr
      nlinarith [h x hx]
    have hh := (le_div_iff₀ ha).mp hs
    nlinarith

theorem positiveConcaveEnvelope_concaveOn {H : ℝ → ℝ}
    (hH0 : ∀ x, 0 ≤ x → 0 ≤ H x) (hH1 : ∀ x, 0 ≤ x → H x ≤ x) :
    ConcaveOn ℝ (Set.Ici 0) (positiveConcaveEnvelope H) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change a * positiveConcaveEnvelope H x + b * positiveConcaveEnvelope H y ≤
    positiveConcaveEnvelope H (a * x + b * y)
  have hpair : ∀ u ∈ concaveEnvelopeValues H x, ∀ v ∈ concaveEnvelopeValues H y,
      a * u + b * v ≤ positiveConcaveEnvelope H (a * x + b * y) := by
    intro u hu v hv
    apply le_csSup (concaveEnvelopeValues_bddAbove hH1 _)
    exact (convex_convexHull ℝ (positiveHypograph H)) hu hv ha hb hab
  apply affine_csSup_le (concaveEnvelopeValues_nonempty hH0 hx) ha
  intro u hu
  have hv := affine_csSup_le (concaveEnvelopeValues_nonempty hH0 hy) hb
    (fun v hv => by simpa only [add_comm] using hpair u hu v hv)
  simpa only [add_comm] using hv

end ThesisCommon
