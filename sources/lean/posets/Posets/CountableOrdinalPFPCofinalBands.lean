import Posets.CountableOrdinalPFPBandLength
import Mathlib.SetTheory.Ordinal.Principal

/-! Disjoint cofinal norming bands for one of T and I−T. Their ordinal
widths remain increasing and cofinal after the finite operator choice. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

theorem ordinalTower_exists_disjoint_nodes
    (hcθ : θ.card ≤ Cardinal.aleph0) (hγ : IsSuccLimit γ)
    (hθ : θ ∈ ordinalTowerLevel θ γ) (a : ℕ → Iio γ) :
    ∃ p : ℕ → OrdinalTowerNode θ γ,
      (∀ n, (p n).level.val = (a n).val) ∧ Pairwise (fun n m => Disjoint (p n).cell (p m).cell) := by
  have hacc (n : ℕ) : θ ∈ derivedSet (ordinalTowerLevel θ (a n).val) := by
    rw [ordinalTowerLevel, ← ordinalDerived_succ]
    exact ordinalDerived_antitone isClosed_Iic (hγ.succ_lt (a n).property).le hθ
  obtain ⟨y, hy, _, hd, _, _⟩ := ordinal_exists_canonical_children θ
    (fun n => ordinalTowerLevel θ (a n).val) (fun n => ordinalTowerLevel_isCompact θ (a n).val)
    (fun n => ordinalTowerLevel_antitone θ (a n).property.le hθ)
    ⟨θ, show θ ≤ θ from le_rfl⟩ hcθ hacc isClopen_univ (mem_univ _)
  choose hm hi using fun n => (hy n).2
  let p : ℕ → OrdinalTowerNode θ γ := fun n =>
    ⟨⟨(a n).val, show (a n).val ≤ γ from (a n).property.le⟩, y n, hm n, hi n⟩
  exact ⟨p, fun _ => rfl, hd⟩

theorem ordinalTower_exists_cofinal_norming_bands
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hγ : IsSuccLimit γ) (hθ : θ ∈ ordinalTowerLevel θ γ)
    (hmul : ∀ β < γ, ∀ N : ℕ, β * N < γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) {ε : ℝ} (hε : 0 < ε) :
    ∃ (b : Bool) (β : ℕ → Iio γ), StrictMono (fun n => (β n).val) ∧
      (∀ δ < γ, ∃ n, δ ≤ (β n).val) ∧
      ∃ (lower : ℕ → Iic γ)
        (F : ∀ n, OrdinalTowerNormingBand M (if b then T else S) (lower n) ε),
        (∀ n, (F n).top.level.val = (lower n).val + (β n).val) ∧
        Pairwise (fun n m => Disjoint (F n).top.cell (F m).top.cell) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖T‖ + ‖S‖) / ε)
  have hnorm : ‖T‖ + ‖S‖ < N * ε := (div_lt_iff₀ hε).mp hN
  obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hγ hcγ
  let c : ℕ → Iio γ := fun n => ⟨(a n).val * N, hmul (a n).val (a n).property N⟩
  obtain ⟨p, hp, hd⟩ := ordinalTower_exists_disjoint_nodes hcθ hγ hθ c
  have hex (n : ℕ) := ordinalTower_exists_norming_band_length hcθ hcγ hθ M T S hTS
    hε hnorm (p n) (a n).val (by rw [hp n])
  choose b lower F hgap hcell using hex
  obtain ⟨b', k, hk, hb⟩ := wolfe_finiteColor_subsequence b
  have hex' (n : ℕ) : ∃ (l : Iic γ)
      (D : OrdinalTowerNormingBand M (if b' then T else S) l ε),
      D.top.level.val = l.val + (a (k n)).val ∧ D.top.cell ⊆ (p (k n)).cell := by
    have h : ∃ (l : Iic γ)
        (D : OrdinalTowerNormingBand M (if b (k n) then T else S) l ε),
        D.top.level.val = l.val + (a (k n)).val ∧ D.top.cell ⊆ (p (k n)).cell :=
      ⟨lower (k n), F (k n), hgap (k n), hcell (k n)⟩
    rw [← hb n]
    exact h
  choose l D hDgap hDcell using hex'
  refine ⟨b', a ∘ k, ha.comp hk, ?_, l, D, hDgap, ?_⟩
  · intro δ hδ
    obtain ⟨n, hn⟩ := hcof δ hδ
    exact ⟨n, hn.trans (ha.monotone (hk.id_le n))⟩
  · intro n m hnm
    exact (hd (fun h => hnm (hk.injective h))).mono (hDcell n) (hDcell m)

end Posets
