import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Posets.OrdinalClosedCopyInitialPowers
import Posets.OrdinalPrincipalTransfiniteSequence

/-! Actual cofinal power rank units with a strict bound on every preceding
padded source.  A shifted fundamental sequence supplies a gap even at limit
indices.  The construction is independent of all operators. -/

noncomputable section
open Set Order
universe u
namespace Posets

structure OrdinalTransfiniteRankUnits (Λ γ : Ordinal.{u}) (s : ℕ) where
  infinite : Ordinal.omega0 ≤ Λ
  unit : Iio Λ → Ordinal.{u}
  unit_large : ∀ i, Λ < unit i
  unit_below : ∀ i, unit i < γ
  source_below : ∀ i, unit i * (s : Ordinal) < γ
  strictMono : StrictMono unit
  source_strictMono : StrictMono (fun i => unit i * (s : Ordinal))
  cofinal : ∀ β < γ, ∃ i, β < unit i
  source_gap : ∀ i, ∃ r < unit i, ∀ j : Iio Λ, j < i → unit j * (s : Ordinal) ≤ r

theorem exists_ordinalTransfiniteRankUnits
    (Λ δ : Ordinal.{u}) (hΛ : Ordinal.omega0 ≤ Λ)
    (hΛδ : Λ < δ) (hcf : δ.cof.ord = Λ) (s : ℕ) (hs : 0 < s) :
    Nonempty (OrdinalTransfiniteRankUnits Λ (Ordinal.omega0 ^ δ) s) := by
  have hc : Cardinal.aleph0 ≤ δ.cof := by
    rw [← Cardinal.omega0_le_ord, hcf]
    exact hΛ
  have hlim : IsSuccLimit Λ := by
    simpa only [hcf] using Cardinal.isSuccLimit_ord hc
  have hP : Ordinal.Principal (· + ·) Λ := by
    simpa only [hcf] using Ordinal.principal_add_ord hc
  obtain ⟨f, hf⟩ := Ordinal.exists_fundamental_sequence δ
  let F : Iio Λ → Ordinal.{u} := fun i => f i.val (by simpa only [hcf] using i.property)
  have hF : StrictMono F := fun _ _ hij => hf.strict_mono _ _ hij
  have hFlt (i : Iio Λ) : F i < δ := hf.lt _
  have hFcofinal : ∀ β < δ, ∃ i : Iio Λ, β < F i := by
    intro β hβ
    have hh : β < Ordinal.blsub δ.cof.ord f := by rwa [hf.blsub_eq]
    obtain ⟨i, hi, hβi⟩ := Ordinal.lt_blsub_iff.mp hh
    have hiΛ : i < Λ := by simpa only [hcf] using hi
    let j : Iio Λ := ⟨succ i, hlim.succ_lt hiΛ⟩
    exact ⟨j, hβi.trans_lt (hf.strict_mono hi _ (Order.lt_succ i))⟩
  obtain ⟨a, ha⟩ := hFcofinal Λ hΛδ
  let shift : Iio Λ → Iio Λ := fun i =>
    ⟨a.val + succ i.val, hP a.property (hlim.succ_lt i.property)⟩
  let base : Iio Λ → Iio Λ := fun i => ⟨a.val + i.val, hP a.property i.property⟩
  have hshift : StrictMono shift := by
    intro i j hij
    exact (Ordinal.isNormal_add_right a.val).strictMono (succ_lt_succ hij)
  have hbase_shift (i : Iio Λ) : base i < shift i :=
    (Ordinal.isNormal_add_right a.val).strictMono (Order.lt_succ i.val)
  have hprior (i j : Iio Λ) (hji : j < i) : shift j ≤ base i :=
    (Ordinal.isNormal_add_right a.val).monotone (succ_le_of_lt hji)
  let σ : Iio Λ → Ordinal.{u} := F ∘ shift
  have hσ : StrictMono σ := hF.comp hshift
  have hσlt (i : Iio Λ) : σ i < δ := hFlt (shift i)
  have hσlarge (i : Iio Λ) : Λ < σ i :=
    ha.trans_le (hF.monotone (Ordinal.le_add_right a.val (succ i.val)))
  have hσcofinal : ∀ β < δ, ∃ i, β < σ i := by
    intro β hβ
    obtain ⟨i, hi⟩ := hFcofinal β hβ
    have his : i ≤ shift i :=
      (Order.le_succ i.val).trans (Ordinal.le_add_left (succ i.val) a.val)
    exact ⟨i, hi.trans_le (hF.monotone his)⟩
  let ρ : Iio Λ → Ordinal.{u} := fun i => Ordinal.omega0 ^ σ i
  have hρ : StrictMono ρ :=
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.comp hσ
  have hρlarge (i : Iio Λ) : Λ < ρ i :=
    (hσlarge i).trans_le (Ordinal.right_le_opow (σ i) Ordinal.one_lt_omega0)
  have hsource_before (i j : Iio Λ) (hij : i < j) : ρ i * (s : Ordinal) < ρ j :=
    Ordinal.omega0_opow_mul_nat_lt (hσ hij) s
  have hρle_source (i : Iio Λ) : ρ i ≤ ρ i * (s : Ordinal) :=
    Ordinal.le_mul_left _ (by exact_mod_cast hs)
  have hsource : StrictMono (fun i => ρ i * (s : Ordinal)) :=
    fun i j hij => (hsource_before i j hij).trans_le (hρle_source j)
  have hρcofinal : ∀ β < Ordinal.omega0 ^ δ, ∃ i, β < ρ i := by
    intro β hβ
    obtain ⟨α, hαδ, hβα⟩ :=
      (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero (Ordinal.aleph0_le_cof.mp hc)).mp hβ
    obtain ⟨i, hi⟩ := hσcofinal α hαδ
    exact ⟨i, hβα.trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hi)⟩
  exact ⟨{
    infinite := hΛ
    unit := ρ
    unit_large := hρlarge
    unit_below := fun i => (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hσlt i)
    source_below := fun i => Ordinal.omega0_opow_mul_nat_lt (hσlt i) s
    strictMono := hρ
    source_strictMono := hsource
    cofinal := hρcofinal
    source_gap := fun i => by
      refine ⟨Ordinal.omega0 ^ F (base i) * (s : Ordinal),
        Ordinal.omega0_opow_mul_nat_lt (hF (hbase_shift i)) s, ?_⟩
      intro j hji
      exact mul_le_mul_right'
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hF.monotone (hprior i j hji))) _ }⟩

namespace OrdinalTransfiniteRankUnits
variable {Λ γ : Ordinal.{u}} {s : ℕ} (R : OrdinalTransfiniteRankUnits Λ γ s)

theorem unit_infinite (i : Iio Λ) : Ordinal.omega0 ≤ R.unit i :=
  R.infinite.trans (R.unit_large i).le

theorem source_power_strictMono :
    StrictMono (fun i => Ordinal.omega0 ^ (R.unit i * (s : Ordinal))) :=
  (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.comp R.source_strictMono

theorem source_power_bound (i : Iio Λ) :
    Ordinal.omega0 ^ (R.unit i * (s : Ordinal)) < Ordinal.omega0 ^ γ :=
  (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (R.source_below i)

theorem source_cofinal (hs : 0 < s) :
    ∀ β < γ, ∃ i, β < R.unit i * (s : Ordinal) := by
  intro β hβ
  obtain ⟨i, hi⟩ := R.cofinal β hβ
  exact ⟨i, hi.trans_le (Ordinal.le_mul_left _ (by exact_mod_cast hs))⟩

theorem target_power_cofinal (hγ : IsSuccLimit γ) :
    ∀ β < Ordinal.omega0 ^ γ, ∃ i, β < Ordinal.omega0 ^ R.unit i := by
  intro β hβ
  obtain ⟨α, hαγ, hβα⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hγ).mp hβ
  obtain ⟨i, hi⟩ := R.cofinal α hαγ
  exact ⟨i, hβα.trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hi)⟩

theorem source_power_cofinal (hγ : IsSuccLimit γ) (hs : 0 < s) :
    ∀ β < Ordinal.omega0 ^ γ, ∃ i,
      β < Ordinal.omega0 ^ (R.unit i * (s : Ordinal)) := by
  intro β hβ
  obtain ⟨α, hαγ, hβα⟩ :=
    (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hγ).mp hβ
  obtain ⟨i, hi⟩ := R.source_cofinal hs α hαγ
  exact ⟨i, hβα.trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hi)⟩

theorem source_power_gap (hs : 0 < s) (i : Iio Λ) :
    ∃ b < Ordinal.omega0 ^ (R.unit i * (s : Ordinal)),
      ∀ j : Iio Λ, j < i → Ordinal.omega0 ^ (R.unit j * (s : Ordinal)) < b := by
  obtain ⟨r, hri, hr⟩ := R.source_gap i
  have hle : R.unit i ≤ R.unit i * (s : Ordinal) :=
    Ordinal.le_mul_left _ (by exact_mod_cast hs)
  have hlt : Ordinal.omega0 ^ r < Ordinal.omega0 ^ (R.unit i * (s : Ordinal)) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hri.trans_le hle)
  have hu : R.unit i * (s : Ordinal) ≠ 0 :=
    (Ordinal.omega0_pos.trans_le (R.infinite.trans (R.unit_large i).le)).ne'
      |> fun h => mul_ne_zero h (by exact_mod_cast hs.ne')
  refine ⟨succ (Ordinal.omega0 ^ r),
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hu).succ_lt hlt, ?_⟩
  intro j hji
  exact (Ordinal.opow_le_opow_right Ordinal.omega0_pos (hr j hji)).trans_lt (Order.lt_succ _)

theorem target_power_gap (hs : 0 < s) (i : Iio Λ) :
    ∃ b < Ordinal.omega0 ^ R.unit i,
      ∀ j : Iio Λ, j < i → Ordinal.omega0 ^ R.unit j < b := by
  obtain ⟨r, hri, hr⟩ := R.source_gap i
  have hlt : Ordinal.omega0 ^ r < Ordinal.omega0 ^ R.unit i :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hri
  have hu : R.unit i ≠ 0 := (Ordinal.omega0_pos.trans_le (R.unit_infinite i)).ne'
  refine ⟨succ (Ordinal.omega0 ^ r),
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hu).succ_lt hlt, ?_⟩
  intro j hji
  have hj : R.unit j ≤ r :=
    (Ordinal.le_mul_left _ (by exact_mod_cast hs)).trans (hr j hji)
  exact (Ordinal.opow_le_opow_right Ordinal.omega0_pos hj).trans_lt (Order.lt_succ _)

def asSourceSequence (hs : 0 < s) (hγ : IsSuccLimit γ) :
    OrdinalPrincipalTransfiniteSequence Λ (Ordinal.omega0 ^ γ) where
  infinite := R.infinite
  endpoint := fun i => Ordinal.omega0 ^ (R.unit i * (s : Ordinal))
  strictMono := R.source_power_strictMono
  principal := fun i => Ordinal.principal_add_omega0_opow (R.unit i * (s : Ordinal))
  head_large := by
    apply (R.unit_large _).trans_le
    exact (Ordinal.le_mul_left _ (by exact_mod_cast hs)).trans
      (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
  bound := R.source_power_bound
  cofinal := R.source_power_cofinal hγ hs
  gap := R.source_power_gap hs

@[simp] theorem asSourceSequence_endpoint (hs : 0 < s) (hγ : IsSuccLimit γ) (i : Iio Λ) :
    (R.asSourceSequence hs hγ).endpoint i =
      Ordinal.omega0 ^ (R.unit i * (s : Ordinal)) := rfl

def baseTargetSequence (hs : 0 < s) (hγ : IsSuccLimit γ) :
    OrdinalPrincipalTransfiniteSequence Λ (Ordinal.omega0 ^ γ) where
  infinite := R.infinite
  endpoint := fun i => Ordinal.omega0 ^ R.unit i
  strictMono := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.comp R.strictMono
  principal := fun i => Ordinal.principal_add_omega0_opow (R.unit i)
  head_large := (R.unit_large _).trans_le (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
  bound := fun i => (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (R.unit_below i)
  cofinal := R.target_power_cofinal hγ
  gap := R.target_power_gap hs

@[simp] theorem baseTargetSequence_endpoint (hs : 0 < s) (hγ : IsSuccLimit γ) (i : Iio Λ) :
    (R.baseTargetSequence hs hγ).endpoint i = Ordinal.omega0 ^ R.unit i := rfl

end OrdinalTransfiniteRankUnits

theorem ordinal_power_exponent_limit_of_uncountable_cofinality
    {δ : Ordinal.{u}} (hc : Cardinal.aleph0 < (Ordinal.omega0 ^ δ).cof) :
    IsSuccLimit δ := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨η, rfl⟩ | hδ
  · rw [Ordinal.opow_zero, ← Ordinal.succ_zero, Ordinal.cof_succ] at hc
    exact (Cardinal.one_lt_aleph0.not_ge hc.le).elim
  · have he : (Ordinal.omega0 ^ succ η).cof = Cardinal.aleph0 := by
      rw [Ordinal.opow_succ]
      exact ((Ordinal.isNormal_mul_right (Ordinal.opow_pos η Ordinal.omega0_pos)).cof_eq
        Ordinal.isSuccLimit_omega0).trans Ordinal.cof_omega0
    exact (hc.ne he.symm).elim
  · exact hδ

theorem exists_ordinalPrincipalTransfiniteRankUnits
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (hgap : γ.cof.ord < γ)
    (s : ℕ) (hs : 0 < s) :
    Nonempty (OrdinalTransfiniteRankUnits γ.cof.ord γ s) := by
  rcases Ordinal.principal_add_iff_zero_or_omega0_opow.mp hP with rfl | ⟨δ, rfl⟩
  · simp only [Ordinal.cof_zero] at hc
    exact (Cardinal.aleph0_pos.not_ge hc.le).elim
  · have hδ := ordinal_power_exponent_limit_of_uncountable_cofinality hc
    have hcof : (Ordinal.omega0 ^ δ).cof = δ.cof :=
      (Ordinal.isNormal_opow Ordinal.one_lt_omega0).cof_eq hδ
    have hδlarge : (Ordinal.omega0 ^ δ).cof.ord < δ := by
      by_contra hn
      have hle : δ ≤ (Ordinal.omega0 ^ δ).cof.ord := le_of_not_gt hn
      have hp : Ordinal.omega0 ^ δ ≤ (Ordinal.omega0 ^ δ).cof.ord := by
        calc
          Ordinal.omega0 ^ δ ≤ Ordinal.omega0 ^ (Ordinal.omega0 ^ δ).cof.ord :=
            Ordinal.opow_le_opow_right Ordinal.omega0_pos hle
          _ = _ := ordinal_uncountable_initial_omega_power hc
      exact hgap.not_ge hp
    exact exists_ordinalTransfiniteRankUnits _ δ (Cardinal.omega0_le_ord.mpr hc.le)
      hδlarge (congrArg Cardinal.ord hcof.symm) s hs

theorem ordinalPrincipal_initial_or_transfiniteRankUnits
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hc : Cardinal.aleph0 < γ.cof) (s : ℕ) (hs : 0 < s) :
    γ = γ.cof.ord ∨ Nonempty (OrdinalTransfiniteRankUnits γ.cof.ord γ s) := by
  by_cases hγ : γ = γ.cof.ord
  · exact Or.inl hγ
  · exact Or.inr (exists_ordinalPrincipalTransfiniteRankUnits γ hP hc
      (lt_of_le_of_ne (Ordinal.ord_cof_le γ) (Ne.symm hγ)) s hs)
end Posets



