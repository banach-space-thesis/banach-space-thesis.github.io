import Posets.ConvergentBandReadback
import JLMS.Definitions
import Mathlib.SetTheory.Cardinal.Cofinality

/-! Cofinality ω, rather than countability of the ordinal, suffices for
the actual centered readback into a countable c₀ sum. -/
noncomputable section
namespace Posets
open Set Filter Topology Ordinal
universe u

theorem ordinal_cof_aleph0_exists_strictMono_cofinal
    (θ : Ordinal.{u}) (hθ : θ.cof = Cardinal.aleph0) :
    ∃ a : ℕ → Iio θ, StrictMono (fun n => (a n).val) ∧
      ∀ β < θ, ∃ n, β < (a n).val := by
  obtain ⟨f, hf⟩ := Ordinal.exists_fundamental_sequence θ
  have hc : θ.cof.ord = Ordinal.omega0 := by simp only [hθ, Cardinal.ord_aleph0]
  have hn (n : ℕ) : (n : Ordinal.{u}) < θ.cof.ord := by
    rw [hc]
    exact Ordinal.nat_lt_omega0 n
  let a : ℕ → Iio θ := fun n => ⟨f n (hn n), hf.lt (hn n)⟩
  have ha : StrictMono (fun n => (a n).val) := by
    intro m n hmn
    exact hf.strict_mono (hn m) (hn n) (by exact_mod_cast hmn)
  refine ⟨a, ha, ?_⟩
  intro β hβ
  rw [← hf.blsub_eq, Ordinal.lt_blsub_iff] at hβ
  obtain ⟨i, hi, hbi⟩ := hβ
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (hc ▸ hi)
  exact ⟨n + 1, hbi.trans_lt (ha (Nat.lt_succ_self n))⟩

theorem ordinal_cofinal_maps_converge_uniform
    (θ : Ordinal.{u}) (a : ℕ → Iio θ)
    (ha : Monotone (fun n => (a n).val))
    (hcof : ∀ β < θ, ∃ n, β < (a n).val)
    {L : ℕ → Type*} [∀ n, TopologicalSpace (L n)]
    (q : ∀ n, C(L n, JLMS.OrdinalInterval θ))
    (haq : ∀ n x, (a n).val ≤ (q n x).val) :
    ∀ U ∈ 𝓝 (⟨θ, Ordinal.zero_le θ, le_rfl⟩ : JLMS.OrdinalInterval θ),
      ∀ᶠ n in cofinite, ∀ x, q n x ∈ U := by
  have hpos : 0 < θ := (Ordinal.zero_le (a 0).val).trans_lt (a 0).property
  letI : Nontrivial (JLMS.OrdinalInterval θ) :=
    ⟨⟨⟨0, le_rfl, hpos.le⟩, ⟨θ, hpos.le, le_rfl⟩, by
      intro heq
      exact hpos.ne (congrArg Subtype.val heq)⟩⟩
  letI : OrderTop (JLMS.OrdinalInterval θ) :=
    { top := ⟨θ, Ordinal.zero_le θ, le_rfl⟩
      le_top := fun x => x.property.2 }
  intro U hU
  obtain ⟨β, hβ, hβU⟩ := nhds_top_basis.mem_iff.mp hU
  have hβ' : β.val < θ := hβ
  obtain ⟨N, hN⟩ := hcof β.val hβ'
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N] with n hn
  intro x
  apply hβU
  exact hN.trans_le ((ha hn).trans (haq n x))

variable {𝕜 : Type*} [RCLike 𝕜]
  {L : ℕ → Type*} [∀ n, TopologicalSpace (L n)] [∀ n, CompactSpace (L n)]

def ordinalCofinalBandReadback (θ : Ordinal.{u}) (a : ℕ → Iio θ)
    (ha : Monotone (fun n => (a n).val))
    (hcof : ∀ β < θ, ∃ n, β < (a n).val)
    (q : ∀ n, C(L n, JLMS.OrdinalInterval θ))
    (haq : ∀ n x, (a n).val ≤ (q n x).val) :
    JLMS.CZero 𝕜 (JLMS.OrdinalInterval θ) →L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n => C(L n, 𝕜)) :=
  convergentBandReadback q ⟨θ, Ordinal.zero_le θ, le_rfl⟩
    (ordinal_cofinal_maps_converge_uniform θ a ha hcof q haq)

@[simp] theorem ordinalCofinalBandReadback_apply (θ : Ordinal.{u}) (a : ℕ → Iio θ)
    (ha : Monotone (fun n => (a n).val))
    (hcof : ∀ β < θ, ∃ n, β < (a n).val)
    (q : ∀ n, C(L n, JLMS.OrdinalInterval θ))
    (haq : ∀ n x, (a n).val ≤ (q n x).val)
    (f : JLMS.CZero 𝕜 (JLMS.OrdinalInterval θ)) (n : ℕ) (x : L n) :
    ordinalCofinalBandReadback θ a ha hcof q haq f n x =
      f (q n x) - f ⟨θ, Ordinal.zero_le θ, le_rfl⟩ :=
  convergentBandReadback_apply _ _ _ _ _ _

theorem norm_ordinalCofinalBandReadback_le (θ : Ordinal.{u}) (a : ℕ → Iio θ)
    (ha : Monotone (fun n => (a n).val))
    (hcof : ∀ β < θ, ∃ n, β < (a n).val)
    (q : ∀ n, C(L n, JLMS.OrdinalInterval θ))
    (haq : ∀ n x, (a n).val ≤ (q n x).val) :
    ‖ordinalCofinalBandReadback (𝕜 := 𝕜) θ a ha hcof q haq‖ ≤ 2 :=
  norm_convergentBandReadback_le _ _ _

end Posets
