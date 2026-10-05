import Posets.WolfePreservationNecessaryQuantiles

/-! The quantile relations on a closed good-row domain are genuine closed
relations on the entire target. The measure family remains on the entire
space; it is not restricted to the closed good-row domain. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [CompactSpace K] [T2Space K] [LinearOrder L] [TopologicalSpace L]
  [CompactSpace L] [T2Space L]

def wolfeExtendedQuantileRelation {H : Set K}
    (ν : H → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) : Set (K × L) :=
  (fun p : H × L => (p.1.val, p.2)) '' wolfeQuantileRelation ν hcut t e

theorem wolfeExtendedQuantileRelation_isClosed {H : Set K} (hH : IsClosed H)
    (ν : H → WeakDual 𝕜 (JLMS.CZero 𝕜 L)) (hν : Continuous ν)
    (hcut : ∀ a : L, IsClopen (Iic a)) (t e : ℝ) :
    IsClosed (wolfeExtendedQuantileRelation ν hcut t e) := by
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact ((wolfeQuantileRelation_isClosed ν hν hcut t e).isCompact.image
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).isClosed

theorem wolfeExtendedQuantileRelation_single {H : Set K}
    (ν : H → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) (t : ℝ) {e : ℝ} (he : 0 < e)
    (y : K) (x z : L) (hx : (y, x) ∈ wolfeExtendedQuantileRelation ν hcut t e)
    (hz : (y, z) ∈ wolfeExtendedQuantileRelation ν hcut t e) : x = z := by
  obtain ⟨⟨v, a⟩, hv, hva⟩ := hx
  obtain ⟨⟨w, b⟩, hw, hwb⟩ := hz
  obtain ⟨hvy, hax⟩ := Prod.mk.inj hva
  obtain ⟨hwy, hbz⟩ := Prod.mk.inj hwb
  have hvw : v = w := Subtype.ext (hvy.trans hwy.symm)
  subst w
  exact hax.symm.trans ((wolfeQuantileRelation_single ν hcut t he v a b hv hw).trans hbz)

theorem wolfe_extended_quantile_grid_covers_atoms {H : Set K}
    (N : JLMS.AtomicDualModel 𝕜 L)
    (ν : H → WeakDual 𝕜 (JLMS.CZero 𝕜 L))
    (hcut : ∀ a : L, IsClopen (Iic a)) {C τ d e : ℝ} (s : Finset ℝ)
    (hgrid : ∀ a ∈ Icc (-C) C, ∃ t ∈ s, a + τ + e < t ∧ t + e < a + d - 2 * τ)
    (hbound : ∀ y, ‖WeakDual.toStrongDual (ν y)‖ ≤ C)
    (hdefect : ∀ y, ‖WeakDual.toStrongDual (ν y)‖ -
      RCLike.re (ν y (wolfeSourceBlock univ isClopen_univ)) ≤ τ)
    (y : K) (hy : y ∈ H) (x : L)
    (hatom : d ≤ ‖N.representation (WeakDual.toStrongDual (ν ⟨y, hy⟩)) x‖) :
    y ∈ ⋃ t : s, {z | (z, x) ∈ wolfeExtendedQuantileRelation ν hcut t.val e} := by
  obtain ⟨t, ht, hp⟩ := wolfe_quantile_grid_covers_atoms N ν hcut s hgrid hbound hdefect ⟨y, hy⟩ x hatom
  exact mem_iUnion.mpr ⟨⟨t, ht⟩, ⟨(⟨y, hy⟩, x), hp, rfl⟩⟩

end Posets
