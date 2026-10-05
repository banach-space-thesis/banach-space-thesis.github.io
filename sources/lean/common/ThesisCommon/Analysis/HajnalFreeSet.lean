import ThesisCommon.Analysis.HajnalBlocks
import ThesisCommon.Analysis.SingularCardinalSequence

/-! Hajnal's free-set theorem with its full singular-cardinal generality.
The regular case uses the maximal-free-family argument. The singular case
uses a cofinal sequence of regular free blocks followed by the partition and
tail thinning construction. No cofinality hypothesis is added to the theorem.

The argument follows the standard proof recorded in the set-mapping appendix
to Juhász, *Cardinal functions in topology* (Mathematical Centre Tracts 34),
A3.4--A3.5. The manuscript's Proposition 4.21 cites the full Hajnal theorem.
-/
noncomputable section
open scoped Cardinal
open Order
namespace ThesisCommon
universe u
variable {Γ : Type u}

theorem hajnal_of_singular (F : Γ → Set Γ) (μ : Cardinal.{u})
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hsing : ¬ (Cardinal.mk Γ).IsRegular) (hμ : μ < Cardinal.mk Γ)
    (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧ IsSetMappingFree F H := by
  let κ := Cardinal.mk Γ
  have hδ : κ.ord.cof < κ := by
    refine lt_of_le_of_ne (Ordinal.cof_ord_le κ) ?_
    intro heq
    exact hsing ⟨hΓ, heq.ge⟩
  have hδInf : Cardinal.aleph0 ≤ κ.ord.cof :=
    Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hΓ)
  let ν := succ (max μ κ.ord.cof)
  have hbaseInf : Cardinal.aleph0 ≤ max μ κ.ord.cof := hδInf.trans (le_max_right _ _)
  have hν : ν.IsRegular := Cardinal.isRegular_succ hbaseInf
  have hνκ : ν < κ := succ_lt_of_singular hsing (max_lt hμ hδ) hbaseInf
  have hμν : μ < ν := (le_max_left _ _).trans_lt (lt_succ _)
  have hδν : κ.ord.cof < ν := (le_max_right _ _).trans_lt (lt_succ _)
  obtain ⟨s, hsreg, hsν, hsκ, hsmono, hscof⟩ :=
    exists_regular_cofinal_cardinalSequence κ ν hsing hν.aleph0_le hνκ
  have hindex : Cardinal.mk κ.ord.cof.ord.toType < ν := by
    simpa only [Cardinal.mk_ord_toType] using hδν
  obtain ⟨B, hBcard, hBfree, hBdisj, hBforward⟩ :=
    exists_oneWay_regular_free_blocks F μ s hΓ hsreg
      (fun i => hμν.trans (hsν i)) (fun i => hindex.trans (hsν i))
      (fun i => (hsκ i).le) hsmono hF
  obtain ⟨H, hHfree, hHlarge⟩ := hajnal_thin_regular_blocks F ν hν hindex B hBdisj
    (fun i => by simpa only [hBcard i] using hsreg i)
    (fun i => by simpa only [hBcard i] using hsν i)
    hBfree hBforward (fun x => (hF x).trans hμν)
  refine ⟨H, ?_, hHfree⟩
  apply (Cardinal.mk_set_le H).antisymm
  by_contra hnot
  obtain ⟨i, hi⟩ := hscof (Cardinal.mk H) (lt_of_not_ge hnot)
  exact hi.not_ge (by simpa only [hBcard i] using hHlarge i)

/-- Hajnal's free-set theorem. A mapping with values uniformly bounded
strictly below an infinite ambient cardinal has a free subset of full size,
including at singular ambient cardinals. The convention of freeness excludes
diagonal pairs, so this helper does not require a separate diagonal condition. -/
theorem hajnal_free_set (F : Γ → Set Γ) (μ : Cardinal.{u})
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ) (hμ : μ < Cardinal.mk Γ)
    (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧ IsSetMappingFree F H := by
  by_cases hreg : (Cardinal.mk Γ).IsRegular
  · exact hajnal_of_isRegular F μ hreg hμ hF
  · exact hajnal_of_singular F μ hΓ hreg hμ hF

end ThesisCommon
