import Posets.OrdinalClosedCoreBands

/-! Finite-band colours for the actual rows of an operator on an ambient
`C₀` space.  A compact open ordinal block is parametrized by an open embedding;
all its band cells are mapped into that block before variation is measured. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
variable {θ γ : Ordinal.{u}}

def ordinalAmbientBandCell (e : Iic θ → K) (p : OrdinalTowerNode θ γ)
    (β : Iic γ) : Set K := e '' p.bandCell β

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalAmbientBandCell_monotone (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (p : OrdinalTowerNode θ γ) :
    Monotone (ordinalAmbientBandCell e p) := by
  intro β δ hβδ
  exact image_mono (p.bandCell_monotone hθ hβδ)

omit [T2Space K] in
theorem ordinalAmbientBandCell_isCompact (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (p : OrdinalTowerNode θ γ)
    (β : Iic γ) (hp : p.level.val ≤ β.val) :
    IsCompact (ordinalAmbientBandCell e p β) :=
  (p.bandCell_isCompact hθ β hp).image he.continuous

theorem ordinalAmbientBandCell_isClopen (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (p : OrdinalTowerNode θ γ)
    (β : Iic γ) (hp : p.level.val ≤ β.val) :
    IsClopen (ordinalAmbientBandCell e p β) :=
  ⟨(ordinalAmbientBandCell_isCompact hθ e he p β hp).isClosed,
    he.isOpenMap _ (p.bandCell_isClopen hθ β hp).isOpen⟩

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalAmbientBandCell_mem (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (p : OrdinalTowerNode θ γ)
    (β : Iic γ) (hp : p.level.val ≤ β.val) :
    e p.point ∈ ordinalAmbientBandCell e p β :=
  mem_image_of_mem e (p.point_mem_bandCell hθ β hp)

omit [TopologicalSpace K] [T2Space K] in
theorem ordinalAmbientBandCell_subset_range (e : Iic θ → K)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) :
    ordinalAmbientBandCell e p β ⊆ range e := image_subset_range _ _

def ordinalAmbientBandColour (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ) : Set (OrdinalTowerNode θ γ) :=
  {p | wolfeMass M (wolfeOperatorRow T (e p.point))
      (ordinalAmbientBandCell e p (a (n+1)) \ ordinalAmbientBandCell e p (a n)) < ε ∧
    wolfeMass M (wolfeOperatorRow S (e p.point))
      (ordinalAmbientBandCell e p (a (n+1)) \ ordinalAmbientBandCell e p (a n)) < ε ∧
    ∃ hp : p.level.val ≤ (a n).val,
      (1 / 2 : ℝ) ≤ RCLike.re (wolfeOperatorRow (if b then T else S) (e p.point)
        (JLMS.clopenIndicator (ordinalAmbientBandCell e p (a n))
          (ordinalAmbientBandCell_isClopen hθ e he p (a n) hp)
          (ordinalAmbientBandCell_isCompact hθ e he p (a n) hp)))}

theorem ordinalAmbientBand_exists_colour (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (p : OrdinalTowerNode θ γ) (hp0 : p.level.val = 0) :
    ∃ i : Fin N × Bool, p ∈ ordinalAmbientBandColour hθ e he M T S a i.1.val i.2 ε := by
  obtain ⟨n, hn, hT, hS⟩ := wolfeOperatorRows_small_band M T S
    (fun n => ordinalAmbientBandCell e p (a n))
    ((ordinalAmbientBandCell_monotone hθ e p).comp ha) (e p.point) hN
  have hp : p.level.val ≤ (a n).val := by rw [hp0]; exact Ordinal.zero_le _
  have hd := wolfeOperatorRows_diagonal_dichotomy T S hTS
    (ordinalAmbientBandCell_isClopen hθ e he p (a n) hp)
    (ordinalAmbientBandCell_isCompact hθ e he p (a n) hp)
    (ordinalAmbientBandCell_mem hθ e p (a n) hp)
  rcases hd with hd | hd
  · exact ⟨(⟨n, hn⟩, true), hT, hS, hp, hd⟩
  · exact ⟨(⟨n, hn⟩, false), hT, hS, hp, hd⟩

def ordinalAmbientBandLeaves (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (a : ℕ → Iic γ) (n : ℕ) (b : Bool) (ε : ℝ) : Set (Iic θ) :=
  {x | ∃ p : OrdinalTowerNode θ γ, p.level.val = 0 ∧ p.point = x ∧
    p ∈ ordinalAmbientBandColour hθ e he M T S a n b ε}

theorem ordinalAmbientBandLeaves_dense_union (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) :
    Dense (⋃ i : Fin N × Bool, ordinalAmbientBandLeaves hθ e he M T S a i.1.val i.2 ε) := by
  apply (scattered_isolatedPoints_dense (JLMS.scattered_subtype JLMS.scattered_ordinal (Iic θ))).mono
  intro x hx
  let p : OrdinalTowerNode θ γ := ordinalTowerIsolatedNode x hx
  obtain ⟨i, hi⟩ := ordinalAmbientBand_exists_colour hθ e he M T S hTS a ha hN p rfl
  exact mem_iUnion.mpr ⟨i, p, rfl, rfl, hi⟩

/-- Finite band colours preserve every actual source rank, with global rows. -/
theorem ordinalAmbientCore_exists_coloured_band (hθ : θ ∈ ordinalTowerLevel θ γ)
    (e : Iic θ → K) (he : IsOpenEmbedding e) (M : JLMS.AtomicDualModel 𝕜 K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (ρ : Ordinal.{v}) {x : Iic θ}
    (hx : x ∈ ordinalDerived (univ : Set (Iic θ)) ρ) :
    ∃ i : Fin N × Bool, x ∈ ordinalDerived
      (closure (ordinalAmbientBandLeaves hθ e he M T S a i.1.val i.2 ε)) ρ := by
  have hd := ordinalAmbientBandLeaves_dense_union hθ e he M T S hTS a ha hN
  have hcover : (univ : Set (Iic θ)) = ⋃ i : Fin N × Bool,
      closure (ordinalAmbientBandLeaves hθ e he M T S a i.1.val i.2 ε) := by
    rw [← closure_iUnion_of_finite]
    exact hd.closure_eq.symm
  rw [hcover, ordinalDerived_iUnion_finite _ (fun _ => isClosed_closure)] at hx
  exact mem_iUnion.mp hx

end Posets
