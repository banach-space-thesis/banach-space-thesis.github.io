import Posets.WolfePreservationNecessaryRealMass
import ThesisCommon.Analysis.OrdinalBakerLocality
import ThesisCommon.Analysis.OrdinalExtension

/-! Quantile relations for a continuous nearly positive kernel on an ordered
compact space. A positive gap makes each relation single-valued; testing all
clopen initial segments makes it closed. A finite grid of levels covers every
sufficiently large atomic coefficient. -/

noncomputable section
open Set Topology
universe u
namespace Posets

section Ordered
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LinearOrder L] [TopologicalSpace L] [CompactSpace L]

def wolfeQuantileRelation (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) : Set (K × L) :=
  {p | ∀ a : L,
    (p.2 ≤ a → t + e ≤ RCLike.re (ν p.1 (wolfeSourceBlock (Iic a) (hcut a)))) ∧
    (a < p.2 → RCLike.re (ν p.1 (wolfeSourceBlock (Iic a) (hcut a))) ≤ t - e)}

theorem wolfeQuantileRelation_isClosed
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (hν : Continuous ν)
    (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) :
    IsClosed (wolfeQuantileRelation ν hcut t e) := by
  have heq : wolfeQuantileRelation ν hcut t e =
      ⋂ a : L, ((Prod.snd ⁻¹' Iic a) ∩
        {p | t + e ≤ RCLike.re (ν p.1 (wolfeSourceBlock (Iic a) (hcut a)))}) ∪
      ((Prod.snd ⁻¹' (Iic a)ᶜ) ∩
        {p | RCLike.re (ν p.1 (wolfeSourceBlock (Iic a) (hcut a))) ≤ t - e}) := by
    ext p
    simp only [wolfeQuantileRelation, mem_setOf_eq, mem_iInter, mem_union,
      mem_inter_iff, mem_preimage, mem_Iic, mem_compl_iff, not_le]
    apply forall_congr'
    intro a
    by_cases h : p.2 ≤ a
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [heq]
  apply isClosed_iInter
  intro a
  have hc : Continuous (fun p : K × L =>
      RCLike.re (ν p.1 (wolfeSourceBlock (Iic a) (hcut a)))) :=
    RCLike.continuous_re.comp ((WeakDual.eval_continuous _).comp (hν.comp continuous_fst))
  exact (((hcut a).isClosed.preimage continuous_snd).inter (isClosed_le continuous_const hc)).union
    (((hcut a).compl.isClosed.preimage continuous_snd).inter (isClosed_le hc continuous_const))

theorem wolfeQuantileRelation_single
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) (t : ℝ) {e : ℝ} (he : 0 < e)
    (y : K) (x z : L) (hx : (y, x) ∈ wolfeQuantileRelation ν hcut t e)
    (hz : (y, z) ∈ wolfeQuantileRelation ν hcut t e) : x = z := by
  rcases lt_trichotomy x z with h | h | h
  · have h1 := (hx x).1 le_rfl
    have h2 := (hz x).2 h
    linarith
  · exact h
  · have h1 := (hz z).1 le_rfl
    have h2 := (hx z).2 h
    linarith

theorem wolfeQuantileRelation_mem_of_atom
    (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) (y : K) (x : L) {τ d t e : ℝ}
    (hdefect : ‖WeakDual.toStrongDual (ν y)‖ -
      RCLike.re (ν y (wolfeSourceBlock univ isClopen_univ)) ≤ τ)
    (hatom : d ≤ ‖N.representation (WeakDual.toStrongDual (ν y)) x‖)
    (htlo : wolfeRealMass N (ν y) (Iio x) + τ + e ≤ t)
    (hthi : t + e ≤ wolfeRealMass N (ν y) (Iio x) + d - 2 * τ) :
    (y, x) ∈ wolfeQuantileRelation ν hcut t e := by
  have hic : wolfeRealMass N (ν y) (Iic x) =
      wolfeRealMass N (ν y) (Iio x) +
        RCLike.re (N.representation (WeakDual.toStrongDual (ν y)) x) := by
    have heq : Iic x = Iio x ∪ {x} := by ext z; simp [le_iff_lt_or_eq]
    rw [heq, wolfeRealMass_union N (ν y) (by simp), wolfeRealMass_singleton]
  have hr := wolfeRealMass_lower_of_defect N (ν y) hdefect {x}
  rw [wolfeMass_singleton, wolfeRealMass_singleton] at hr
  intro a
  constructor
  · intro hxa
    have h := wolfeRealMass_mono_with_defect N (ν y) hdefect (Iic_subset_Iic.mpr hxa)
    rw [hic, wolfeRealMass_clopen N (ν y) (Iic a) (hcut a)] at h
    linarith
  · intro hax
    have h := wolfeRealMass_mono_with_defect N (ν y) hdefect
      (show Iic a ⊆ Iio x from fun z hz => hz.trans_lt hax)
    rw [wolfeRealMass_clopen N (ν y) (Iic a) (hcut a)] at h
    linarith

end Ordered

theorem wolfe_exists_finite_quantile_grid {C τ d e : ℝ}
    (hC : 0 ≤ C) (hgap : 3 * τ + 2 * e < d) :
    ∃ s : Finset ℝ, s.Nonempty ∧ ∀ a ∈ Icc (-C) C,
      ∃ t ∈ s, a + τ + e < t ∧ t + e < a + d - 2 * τ := by
  classical
  let U (t : ℝ) : Set ℝ := {a | a + τ + e < t ∧ t + e < a + d - 2 * τ}
  have hU (t : ℝ) : IsOpen (U t) :=
    (isOpen_lt ((continuous_id.add continuous_const).add continuous_const) continuous_const).inter
      (isOpen_lt continuous_const ((continuous_id.add continuous_const).sub continuous_const))
  have hcover : Icc (-C) C ⊆ ⋃ t : ℝ, U t := by
    intro a _
    refine mem_iUnion.mpr ⟨a + d / 2 - τ / 2, ?_⟩
    change a + τ + e < a + d / 2 - τ / 2 ∧
      a + d / 2 - τ / 2 + e < a + d - 2 * τ
    constructor <;> linarith
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U hU hcover
  have hgrid : ∀ a ∈ Icc (-C) C, ∃ t ∈ s, a + τ + e < t ∧ t + e < a + d - 2 * τ := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := mem_iUnion₂.mp (hs ha)
    exact ⟨t, ht, hta⟩
  have hzero : (0 : ℝ) ∈ Icc (-C) C := ⟨by linarith, hC⟩
  obtain ⟨t, ht, _⟩ := hgrid 0 hzero
  exact ⟨s, ⟨t, ht⟩, hgrid⟩

theorem wolfe_ordinalInterval_isClopen_Iic (κ : Ordinal.{u}) (a : ThesisCommon.OrdinalInterval κ) :
    IsClopen (Iic a) := by
  exact (ThesisCommon.ordinal_isClopen_Iic a.val).preimage continuous_subtype_val

theorem wolfe_quantile_grid_covers_atoms
    {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
    [LinearOrder L] [TopologicalSpace L] [CompactSpace L]
    (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : K → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) {C τ d e : ℝ} (s : Finset ℝ)
    (hgrid : ∀ a ∈ Icc (-C) C, ∃ t ∈ s, a + τ + e < t ∧ t + e < a + d - 2 * τ)
    (hbound : ∀ y, ‖WeakDual.toStrongDual (ν y)‖ ≤ C)
    (hdefect : ∀ y, ‖WeakDual.toStrongDual (ν y)‖ -
      RCLike.re (ν y (wolfeSourceBlock univ isClopen_univ)) ≤ τ)
    (y : K) (x : L) (hatom : d ≤ ‖N.representation (WeakDual.toStrongDual (ν y)) x‖) :
    ∃ t ∈ s, (y, x) ∈ wolfeQuantileRelation ν hcut t e := by
  have habs := (wolfeRealMass_abs_le N (ν y) (Iio x)).trans (hbound y)
  obtain ⟨t, ht, hlo, hhi⟩ := hgrid (wolfeRealMass N (ν y) (Iio x)) (abs_le.mp habs)
  exact ⟨t, ht, wolfeQuantileRelation_mem_of_atom N ν hcut y x
    (hdefect y) hatom hlo.le hhi.le⟩

end Posets
