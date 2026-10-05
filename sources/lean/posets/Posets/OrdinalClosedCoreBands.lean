import Posets.CountableOrdinalPFPBandColours
import ThesisCommon.Analysis.OrdinalFiniteCover
import JLMS.OrdinalScattered

/-! Initial finite-band selection using actual closed colour cores.
The ordinal interval and its Cantor--Bendixson ranks may be uncountable;
isolated points are dense and finite closed unions preserve every rank. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

theorem scattered_isolatedPoints_dense {K : Type*} [TopologicalSpace K]
    (hK : JLMS.IsScattered K) : Dense {x : K | IsOpen ({x} : Set K)} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hx, V, hV, he⟩ := hK U hne
  refine ⟨x, hx, ?_⟩
  change IsOpen ({x} : Set K)
  rw [← he]
  exact hU.inter hV

theorem ordinalClosedCore_isOpen_singleton_of_set_eq {K : Type*} [TopologicalSpace K]
    {A B : Set K} (hAB : A = B) (x : K) (hA : x ∈ A) (hB : x ∈ B)
    (ho : IsOpen ({⟨x, hB⟩} : Set B)) : IsOpen ({⟨x, hA⟩} : Set A) := by
  subst B
  exact ho

def ordinalTowerIsolatedNode {θ γ : Ordinal.{u}} (x : Iic θ)
    (hx : IsOpen ({x} : Set (Iic θ))) : OrdinalTowerNode θ γ where
  level := ⟨0, Ordinal.zero_le _⟩
  point := x
  mem_level := by simpa only [ordinalTowerLevel, ordinalDerived_zero] using x.property
  isolated := by
    exact ordinalClosedCore_isOpen_singleton_of_set_eq
      (show ordinalTowerLevel θ 0 = Iic θ by simp only [ordinalTowerLevel, ordinalDerived_zero])
      x.val _ x.property hx

theorem ordinalClosedCore_interval_compact (θ : Ordinal.{u}) : IsCompact (Iic θ) := by
  have heq : Icc (0 : Ordinal.{u}) θ = Iic θ := by ext x; simp
  rw [← heq]
  exact isCompact_Icc

variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

def ordinalClosedCoreBandLeaves (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ) : Set (Iic θ) :=
  {x | ∃ p : OrdinalTowerNode θ γ, p.level.val = 0 ∧ p.point = x ∧
    p ∈ ordinalTowerBandColour hθ M T S a n b ε}

theorem ordinalClosedCoreBandLeaves_isCompact (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ) :
    IsCompact (closure (ordinalClosedCoreBandLeaves hθ M T S a n b ε)) := by
  letI : CompactSpace (Iic θ) := isCompact_iff_compactSpace.mp (ordinalClosedCore_interval_compact θ)
  exact isClosed_closure.isCompact

theorem ordinalClosedCoreBandLeaves_dense_union (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) :
    Dense (⋃ i : Fin N × Bool, ordinalClosedCoreBandLeaves hθ M T S a i.1.val i.2 ε) := by
  apply (scattered_isolatedPoints_dense (JLMS.scattered_subtype JLMS.scattered_ordinal (Iic θ))).mono
  intro x hx
  let p : OrdinalTowerNode θ γ := ordinalTowerIsolatedNode x hx
  obtain ⟨i, hi⟩ := ordinalTowerNode_exists_band_colour hθ M T S hTS a ha hN p rfl
  exact mem_iUnion.mpr ⟨i, p, rfl, rfl, hi⟩

/-- Every retained ordinal rank occurs in the closure of one actual band
colour, with the same original point. -/
theorem ordinalClosedCore_exists_coloured_band (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (ρ : Ordinal.{v}) {x : Iic θ}
    (hx : x ∈ ordinalDerived (univ : Set (Iic θ)) ρ) :
    ∃ i : Fin N × Bool, x ∈ ordinalDerived
      (closure (ordinalClosedCoreBandLeaves hθ M T S a i.1.val i.2 ε)) ρ := by
  have hd := ordinalClosedCoreBandLeaves_dense_union hθ M T S hTS a ha hN
  have hcover : (univ : Set (Iic θ)) =
      ⋃ i : Fin N × Bool, closure (ordinalClosedCoreBandLeaves hθ M T S a i.1.val i.2 ε) := by
    rw [← closure_iUnion_of_finite]
    exact hd.closure_eq.symm
  rw [hcover, ordinalDerived_iUnion_finite _ (fun _ => isClosed_closure)] at hx
  exact mem_iUnion.mp hx

end Posets
