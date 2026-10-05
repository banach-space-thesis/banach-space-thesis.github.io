import ThesisCommon.Analysis.GowersMaureyCodedPairFamilies

/-! Appending a genuinely selected pair preserves the exact recursive
special-sequence data, all earlier growth controls, and both cross estimates. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {seed n : ℕ} {G : C00 𝕜 → ℝ}

def CodedDetectingFamily.append (d : CodedDetectingFamily T ε η seed n G)
    (p : DetectingPair T ε)
    (hsize : p.size = if n = 0 then D.j (2*seed+1)
      else D.sigma (List.ofFn (fun i => (d.pair i).functional)))
    (hcode : CodingDomain (List.ofFn (fun i => (d.pair i).functional) ++ [p.functional]))
    (hnext : p.size < D.sigma (List.ofFn (fun i => (d.pair i).functional) ++ [p.functional]))
    (hcut : pairingSpreadCutoff p.functional p.vector <
      D.sigma (List.ofFn (fun i => (d.pair i).functional) ++ [p.functional]))
    (hG : G ((∑ i, (d.pair i).vector) + p.vector) <
      logarithmicWeight (D.sigma (List.ofFn (fun i => (d.pair i).functional) ++ [p.functional])))
    (hcross : ∀ i, Before (d.pair i).vector p.vector ∧
      ‖completedPairing D (d.pair i).functional (T p.inSubspace)‖ < η ∧
      ‖completedPairing D p.functional (T (d.pair i).inSubspace)‖ < η ∧
      ∀ z ∈ spreadParameterSquare (d.pair i).size,
        pairing (d.pair i).functional (spread z.1 z.2 p.vector) = 0 ∧
        pairing p.functional (spread z.1 z.2 (d.pair i).vector) = 0) :
    CodedDetectingFamily T ε η seed (n+1) G := by
  classical
  have holdsize (i : Fin n) : (d.pair i).size < p.size := by
    have hn : n ≠ 0 := by have := i.isLt; omega
    rw [hsize,if_neg hn]
    exact d.next_size i
  have holdcut (i : Fin n) : pairingSpreadCutoff (d.pair i).functional (d.pair i).vector < p.size := by
    have hn : n ≠ 0 := by have := i.isLt; omega
    rw [hsize,if_neg hn]
    exact d.next_cutoff i
  refine {
    pair := Fin.snoc d.pair p
    code_domain := ?_
    successive := ?_
    size_rule := ?_
    size_strict := ?_
    growth := ?_
    cutoff := ?_
    cross_image := ?_
    cross_spread := ?_
    next_size := ?_
    next_cutoff := ?_
    next_growth := ?_
  }
  · rw [map_snoc,ofFn_snoc]
    exact hcode
  · exact relation_snoc d.pair p (fun a b => Before a.vector b.vector)
      d.successive (fun i => (hcross i).1)
  · intro i
    rw [map_snoc]
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last,Fin.val_last,initialSegment_snoc_last] using hsize
    | cast i => simpa only [Fin.snoc_castSucc,Fin.coe_castSucc,initialSegment_snoc_castSucc]
        using d.size_rule i
  · exact relation_snoc d.pair p (fun a b => a.size < b.size) d.size_strict holdsize
  · intro i hi
    rw [map_snoc]
    induction i using Fin.lastCases with
    | last =>
      change 0 < n at hi
      rw [prefixSum_snoc_last,Fin.snoc_last,hsize,if_neg (Nat.ne_of_gt hi)]
      exact d.next_growth hi
    | cast i => simpa only [prefixSum_snoc_castSucc,Fin.snoc_castSucc] using d.growth i hi
  · exact relation_snoc d.pair p
      (fun a b => pairingSpreadCutoff a.functional a.vector < b.size) d.cutoff holdcut
  · exact relation_snoc d.pair p
      (fun a b => ‖completedPairing D a.functional (T b.inSubspace)‖ < η ∧
        ‖completedPairing D b.functional (T a.inSubspace)‖ < η)
      d.cross_image (fun i => ⟨(hcross i).2.1,(hcross i).2.2.1⟩)
  · exact relation_snoc d.pair p
      (fun a b => ∀ z ∈ spreadParameterSquare a.size,
        pairing a.functional (spread z.1 z.2 b.vector) = 0 ∧
        pairing b.functional (spread z.1 z.2 a.vector) = 0)
      d.cross_spread (fun i => (hcross i).2.2.2)
  · intro i
    rw [map_snoc,ofFn_snoc]
    induction i using Fin.lastCases with
    | last => simpa using hnext
    | cast i => simpa using (holdsize i).trans hnext
  · intro i
    rw [map_snoc,ofFn_snoc]
    induction i using Fin.lastCases with
    | last => simpa using hcut
    | cast i => simpa using (holdcut i).trans hnext
  · intro _
    rw [map_snoc,map_snoc,ofFn_snoc,Fin.sum_univ_castSucc]
    simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hG

end ThesisCommon.GowersMaurey
