import Posets.OrdinalFiniteBandRankExtraction

/-! An actual operator splitting selects a finite band colour whose compact
core has the full source rank. Padded levels then produce genuine continuous
coordinates containing the target ordinal power, uniformly for every colour. -/
noncomputable section
namespace Posets
open Set Topology
open ThesisCommon
universe u
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

def ordinalPaddedBandLevels (b : Ordinal.{u}) (N : ℕ) (n : ℕ) :
    Iic (b * ((2*N+2 : ℕ) : Ordinal)) :=
  ⟨b * ((2 * min n (N+1) : ℕ) : Ordinal),
    mul_le_mul_left' (by exact_mod_cast (show 2 * min n (N+1) ≤ 2*N+2 by omega)) b⟩

theorem ordinalPaddedBandLevels_monotone (b : Ordinal.{u}) (N : ℕ) :
    Monotone (ordinalPaddedBandLevels b N) := by
  intro i j hij
  change b * ((2 * min i (N+1) : ℕ) : Ordinal) ≤
    b * ((2 * min j (N+1) : ℕ) : Ordinal)
  exact mul_le_mul_left' (by exact_mod_cast (Nat.mul_le_mul_left 2 (min_le_min hij le_rfl))) b

theorem ordinalPaddedBandLevels_apply (b : Ordinal.{u}) (N n : ℕ) (hn : n ≤ N+1) :
    (ordinalPaddedBandLevels b N n).val = b * ((2*n : ℕ) : Ordinal) := by
  change b * ((2 * min n (N+1) : ℕ) : Ordinal) = _
  rw [Nat.min_eq_left hn]

theorem ordinalPaddedBand_top_level (b : Ordinal.{u}) (hb : b ≠ 0) (N : ℕ) :
    Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)) ∈
      ordinalTowerLevel (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))
        (b * ((2*N+2 : ℕ) : Ordinal)) := by
  rw [ordinalTowerLevel, ordinalDerived_Iic_power_self
    (mul_ne_zero hb (by exact_mod_cast (show 2*N+2 ≠ 0 by omega)))]
  exact mem_singleton _

theorem ordinalPaddedBand_operator_coloured_geometry
    {𝕜 : Type*} [RCLike 𝕜]
    (b : Ordinal.{u}) (hb : b ≠ 0) (habs : 1+b = b) (N : ℕ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))))
    (T S : JLMS.CZero 𝕜 (Iic (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))) →L[𝕜]
      JLMS.CZero 𝕜 (Iic (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) :
    ∃ i : Fin N × Bool,
      Nonempty (OrdinalSeparatedBandCoreGeometry
        (Subtype.val '' closure (ordinalClosedCoreBandLeaves
          (ordinalPaddedBand_top_level b hb N) M T S (ordinalPaddedBandLevels b N)
          i.1.val i.2 ε))
        (Ordinal.omega0 ^ (b * ((2*N+2 : ℕ) : Ordinal)))
        (b * ((2*i.1.val+2 : ℕ) : Ordinal)) (b * ((2*i.1.val : ℕ) : Ordinal)) b) := by
  let γ := b * ((2*N+2 : ℕ) : Ordinal)
  let θ := Ordinal.omega0 ^ γ
  have hθ : θ ∈ ordinalTowerLevel θ γ := ordinalPaddedBand_top_level b hb N
  have ht : (⟨θ, show θ ≤ θ from le_rfl⟩ : Iic θ) ∈ ordinalDerived (univ : Set (Iic θ)) γ := by
    have he := ordinalDerived_image_closedEmbedding
      (isClosed_Iic : IsClosed (Iic θ)).isClosedEmbedding_subtypeVal univ γ
    rw [image_univ, Subtype.range_coe] at he
    change θ ∈ ordinalDerived (Iic θ) γ at hθ
    rw [he] at hθ
    obtain ⟨x, hx, heq⟩ := hθ
    have heq' : x = (⟨θ, show θ ≤ θ from le_rfl⟩ : Iic θ) := Subtype.ext heq
    exact heq' ▸ hx
  obtain ⟨i, hi⟩ := ordinalClosedCore_exists_coloured_band hθ M T S hTS
    (ordinalPaddedBandLevels b N) (ordinalPaddedBandLevels_monotone b N) hN γ ht
  refine ⟨i, ordinal_finite_band_exists_geometry b hb habs N i.1.val i.1.isLt.le _ ?_ ?_ ?_⟩
  · exact (ordinalClosedCoreBandLeaves_isCompact hθ M T S
      (ordinalPaddedBandLevels b N) i.1.val i.2 ε).image continuous_subtype_val
  · rintro x ⟨y, _, rfl⟩
    exact y.property
  · rw [ordinalDerived_image_closedEmbedding
      (isClosed_Iic : IsClosed (Iic θ)).isClosedEmbedding_subtypeVal]
    exact (show (ordinalDerived (closure (ordinalClosedCoreBandLeaves hθ M T S
      (ordinalPaddedBandLevels b N) i.1.val i.2 ε)) γ).Nonempty from ⟨_, hi⟩).image Subtype.val

end Posets
