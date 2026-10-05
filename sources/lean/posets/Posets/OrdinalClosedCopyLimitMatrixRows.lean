import Posets.OrdinalClosedCopyLimitClubs
import Posets.OrdinalClosedCopyCutRows
import JLMS.OrdinalMatrixFamilyBlocks

/-! A single closed copy simultaneously selects genuinely scalar limit
rows in every regular-cardinal bottom block. The chosen copy preserves
all ordinal junctions. No lower bound on the scalar coefficients, and no
coherent choice between an operator and its complement, is presumed. -/

noncomputable section
namespace Posets
open JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordinalClosedCopy_limitMatrixRows {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (T : Ordinal.{u} → ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ∃ τ : Ordinal.{u} → Ordinal.{u}, (∀ q, τ q < c.ord) ∧
      ∃ g : C(OrdinalInterval (c.ord * η), OrdinalInterval (c.ord * η)),
        StrictMono g ∧ IsClosed (Set.range g) ∧
        (∀ q (hq : q ≤ η),
          g ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ =
            ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩) ∧
        (∀ x, (g x).val / c.ord = x.val / c.ord) ∧
        (∀ x, x.val % c.ord ≠ 0 → ∃ δ : OrdinalInterval c.ord,
          δ.val = (g x).val % c.ord ∧ τ (x.val / c.ord) < δ.val ∧
          δ.val < c.ord ∧ Order.IsSuccLimit δ.val ∧
          (∀ n, IsOrdinalMatrixCut (T (x.val / c.ord) n) (τ (x.val / c.ord)) δ.val) ∧
          (∀ n (f : OrdinalC 𝕜 c.ord),
            (∀ y : OrdinalInterval c.ord, y.val ≤ τ (x.val / c.ord) → f y = 0) →
            f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 →
            T (x.val / c.ord) n f δ =
              ordinalOperatorMatrix c.ord (T (x.val / c.ord) n) δ δ * f δ)) := by
  classical
  have hκomega : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
  have hκ : c.ord ≠ 0 := (Ordinal.omega0_pos.trans_le hκomega).ne'
  have hκone : (1 : Ordinal.{u}) < c.ord := Ordinal.one_lt_omega0.trans_le hκomega
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  choose β hβ hrow using fun q => exists_ordinalOperatorEndpointRows_cutoff hcf (T q)
  let τ (q : Ordinal.{u}) := Order.succ (β q)
  have hτ (q : Ordinal.{u}) : τ q < c.ord := (Cardinal.isSuccLimit_ord hu.le).succ_lt (hβ q)
  have hτrow (q : Ordinal.{u}) (n : ℕ) (y : OrdinalInterval c.ord)
      (hy : τ q ≤ y.val) (hyκ : y.val < c.ord) :
      ordinalOperatorMatrix c.ord (T q n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0 :=
    hrow q n y ((Order.lt_succ (β q)).trans_le hy) hyκ
  let s (q : Ordinal.{u}) := ordinalMatrixFamilyCuts (T q) (τ q)
  have hs (q : Ordinal.{u}) : IsClosed (s q) := isClosed_ordinalMatrixFamilyCuts (T q) (τ q)
  have hcofinal (q b : Ordinal.{u}) (hb : b < c.ord) :
      ∃ δ < c.ord, b < δ ∧ δ ∈ s q :=
    exists_initialOrdinalMatrix_familyCut hc hu (T q) (τ q) (hτ q) (hτrow q) b hb
  let g := ordinalClosedCopyFromLimitClubs hc hu η s hs hcofinal
  have hg : StrictMono g := ordinalBlockwiseContinuousMap_strictMono _ _ _ _ _ _
  have hgclosed : IsClosed (Set.range g) := ordinalBlockwiseContinuousMap_range_closed _ _ _ _ _ _
  have hgjunction (q : Ordinal.{u}) (hq : q ≤ η) :
      g ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ =
        ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ :=
    Subtype.ext (ordinalBlockwiseSelector_junction hκ _
      (fun q => ordinalLimitClubSelector_zero c.ord (s q)) q)
  have hgquot (x : OrdinalInterval (c.ord * η)) : (g x).val / c.ord = x.val / c.ord := by
    have hlt := ordinalLimitClubSelector_lt hc hu (hs (x.val / c.ord))
      (hcofinal (x.val / c.ord)) (Ordinal.mod_lt x.val hκ)
    change (c.ord * (x.val / c.ord) +
      ordinalLimitClubSelector c.ord (s (x.val / c.ord)) (x.val % c.ord)) / c.ord = _
    rw [Ordinal.mul_add_div _ hκ, Ordinal.div_eq_zero_of_lt hlt, add_zero]
  refine ⟨τ, hτ, g, hg, hgclosed, hgjunction, hgquot, ?_⟩
  intro x hx
  let q := x.val / c.ord
  have hr := Ordinal.mod_lt x.val hκ
  have hd := ordinalLimitClubSelector_data hc hu (hs q) (hcofinal q)
    (Ordinal.pos_iff_ne_zero.mpr hx) hr
  have he : (g x).val % c.ord = ordinalLimitClubSelector c.ord (s q) (x.val % c.ord) :=
    ordinalClosedCopyFromLimitClubs_remainder hc hu η s hs hcofinal x
  have hdlt : (g x).val % c.ord < c.ord := Ordinal.mod_lt (g x).val hκ
  let δ : OrdinalInterval c.ord := ⟨(g x).val % c.ord, Ordinal.zero_le _, hdlt.le⟩
  have hδlim : Order.IsSuccLimit δ.val := by
    change Order.IsSuccLimit ((g x).val % c.ord)
    rw [he]
    exact hd.2.1
  have hcut (n : ℕ) : IsOrdinalMatrixCut (T q n) (τ q) δ.val := by
    change IsOrdinalMatrixCut (T q n) (τ q) ((g x).val % c.ord)
    rw [he]
    exact hd.1 n
  have hfirst : ordinalClubSelector c.ord (s q) 1 ∈ s q :=
    ordinalClubSelector_mem hc (hs q) (hcofinal q) (by simp) hκone
  have hτδ : τ q < δ.val := by
    change τ q < (g x).val % c.ord
    rw [he]
    exact (hfirst 0).1.trans_lt hd.2.2
  refine ⟨δ, rfl, hτδ, hdlt, hδlim, hcut, ?_⟩
  intro n f hhead htop
  exact ordinalMatrixCut_limitRow_scalar (T q n) (hcut n) hτδ hδlim hdlt f hhead htop

end Posets
