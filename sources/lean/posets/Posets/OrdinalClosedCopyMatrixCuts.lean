import Posets.OrdinalClosedCopyClubs
import JLMS.OrdinalMatrixFamilyBlocks

/-! Arbitrary countable operator families in every bottom ordinal block
have common matrix cuts on one globally continuous closed ordinal copy.
There is no operator-preservation hypothesis: row support and ordinary
column continuity supply the clubs.  Junction rows are retained, rather
than being identified to a single point. -/

noncomputable section
namespace Posets
open JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordinalClosedCopy_matrixCuts {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (η : Ordinal.{u})
    (T : Ordinal.{u} → ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ∃ τ : Ordinal.{u} → Ordinal.{u}, (∀ q, τ q < c.ord) ∧
      ∃ g : C(OrdinalInterval (c.ord * η), OrdinalInterval (c.ord * η)),
        StrictMono g ∧ IsClosed (Set.range g) ∧
        (∀ q (hq : q ≤ η),
          g ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩ =
            ⟨c.ord * q, Ordinal.zero_le _, mul_le_mul_left' hq _⟩) ∧
        (∀ x, (g x).val / c.ord = x.val / c.ord) ∧
        (∀ x, x.val % c.ord ≠ 0 → ∀ n,
          IsOrdinalMatrixCut (T (x.val / c.ord) n) (τ (x.val / c.ord))
            ((g x).val % c.ord)) := by
  classical
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
  let g := ordinalClosedCopyFromClubs hc hu η s hs hcofinal
  refine ⟨τ, hτ, g, ordinalClosedCopyFromClubs_strictMono hc hu η s hs hcofinal,
    ordinalClosedCopyFromClubs_range_closed hc hu η s hs hcofinal,
    ordinalClosedCopyFromClubs_junction hc hu η s hs hcofinal,
    ordinalClosedCopyFromClubs_quotient hc hu η s hs hcofinal, ?_⟩
  intro x hx n
  exact ordinalClosedCopyFromClubs_mem hc hu η s hs hcofinal x hx n

end Posets
