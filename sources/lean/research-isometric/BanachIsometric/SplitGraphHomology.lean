import BanachIsometric.HomologicalClutchingCycle
import BanachIsometric.RawPointHomology
import BanachIsometric.SmallChainSubdivision
import BanachIsometric.SubdivisionCycleFilling

/-! Two self-maps with separated supports split a graph class into its
horizontal and vertical parts. The chain identity is checked on the actual
subdivided singular simplices. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open scoped Topology

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]

def rawVerticalGraph (x₀ : X) : C(G, X × G) :=
  (ContinuousMap.const G x₀).prodMk (ContinuousMap.id G)

theorem rawChainMap_split_graph_small
    (a b : C(X, X)) (g : C(X, G)) (x₀ : X) (U : Bool → Set X)
    (ha : ∀ x ∈ U false, a x = x₀) (hb : ∀ x ∈ U true, b x = x₀)
    (n : ℕ) (c : RawRationalChains X n) (hc : c ∈ rawSmallChainCarrier U n) :
    rawChainMap (a.prodMk (g.comp b)) n c =
      rawChainMap ((rawGraphMap (ContinuousMap.const X (g x₀))).comp a) n c +
        rawChainMap ((rawVerticalGraph x₀).comp (g.comp b)) n c -
          rawChainMap (ContinuousMap.const X (x₀, g x₀)) n c := by
  let f := a.prodMk (g.comp b)
  let horizontal := (rawGraphMap (ContinuousMap.const X (g x₀))).comp a
  let vertical := (rawVerticalGraph x₀).comp (g.comp b)
  let constant := ContinuousMap.const X (x₀, g x₀)
  let difference := rawChainMap f n -
    (rawChainMap horizontal n + rawChainMap vertical n - rawChainMap constant n)
  have hs : rawSmallChainCarrier U n ≤ LinearMap.ker difference := by
    rw [rawSmallChainCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨i, hi⟩, rfl⟩
    change rawChainMap f n (Finsupp.single σ 1) -
      (rawChainMap horizontal n (Finsupp.single σ 1) +
        rawChainMap vertical n (Finsupp.single σ 1) -
          rawChainMap constant n (Finsupp.single σ 1)) = 0
    simp only [rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    cases i with
    | false =>
        have hf : f.comp σ = vertical.comp σ := by
          apply ContinuousMap.ext
          intro t
          change (a (σ t), g (b (σ t))) = (x₀, g (b (σ t)))
          rw [ha _ (hi ⟨t, rfl⟩)]
        have hh : horizontal.comp σ = constant.comp σ := by
          apply ContinuousMap.ext
          intro t
          change (a (σ t), g x₀) = (x₀, g x₀)
          rw [ha _ (hi ⟨t, rfl⟩)]
        rw [hf, hh]
        abel
    | true =>
        have hf : f.comp σ = horizontal.comp σ := by
          apply ContinuousMap.ext
          intro t
          change (a (σ t), g (b (σ t))) = (a (σ t), g x₀)
          rw [hb _ (hi ⟨t, rfl⟩)]
        have hv : vertical.comp σ = constant.comp σ := by
          apply ContinuousMap.ext
          intro t
          change (x₀, g (b (σ t))) = (x₀, g x₀)
          rw [hb _ (hi ⟨t, rfl⟩)]
        rw [hf, hv]
        abel
  exact sub_eq_zero.mp (hs hc)

theorem rawHomologyMap_graph_split
    (a b : C(X, X)) (g : C(X, G)) (x₀ : X) (U : Bool → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (ha : ∀ x ∈ U false, a x = x₀) (hb : ∀ x ∈ U true, b x = x₀)
    (Ha : (ContinuousMap.id X).Homotopy a) (Hb : (ContinuousMap.id X).Homotopy b)
    (n : ℕ) (z : rawCycles X n) :
    rawHomologyMap (rawGraphMap g) n (Submodule.Quotient.mk z) =
      rawHomologyMap (rawGraphMap (ContinuousMap.const X (g x₀))) n (Submodule.Quotient.mk z) +
        rawHomologyMap (rawVerticalGraph x₀) n
          (rawHomologyMap g n (Submodule.Quotient.mk z)) := by
  obtain ⟨k, hk⟩ := exists_rawSubdivision_small_chain U hU hcover (n + 1) z.val
  let zsmall : rawCycles X n := ⟨(rawSubdivision X (n + 1) ^ k) z.val, by
    have h := LinearMap.congr_fun (rawSubdivision_boundary_power X n k) z.val
    change rawBoundary n ((rawSubdivision X (n + 1) ^ k) z.val) =
      (rawSubdivision X n ^ k) (rawBoundary n z.val) at h
    have hz : rawBoundary n z.val = 0 := z.property
    rw [hz, map_zero] at h
    exact h⟩
  have hq : (Submodule.Quotient.mk z : RawPositiveHomology X n) = Submodule.Quotient.mk zsmall := by
    apply (Submodule.Quotient.eq (rawBoundaries X n)).mpr
    refine ⟨rawSubdivisionCycleFilling X n k z.val, ?_⟩
    apply Subtype.ext
    exact rawSubdivisionCycleFilling_boundary X n k z.val z.property
  let f := a.prodMk (g.comp b)
  let horizontal := (rawGraphMap (ContinuousMap.const X (g x₀))).comp a
  let vertical := (rawVerticalGraph x₀).comp (g.comp b)
  let constant := ContinuousMap.const X (x₀, g x₀)
  have hclass : rawHomologyMap f n (Submodule.Quotient.mk zsmall) =
      rawHomologyMap horizontal n (Submodule.Quotient.mk zsmall) +
        rawHomologyMap vertical n (Submodule.Quotient.mk zsmall) -
          rawHomologyMap constant n (Submodule.Quotient.mk zsmall) := by
    change (rawBoundaries (X × G) n).mkQ (rawCyclesMap f n zsmall) =
      (rawBoundaries (X × G) n).mkQ (rawCyclesMap horizontal n zsmall) +
        (rawBoundaries (X × G) n).mkQ (rawCyclesMap vertical n zsmall) -
          (rawBoundaries (X × G) n).mkQ (rawCyclesMap constant n zsmall)
    rw [← map_add, ← map_sub]
    apply congrArg (rawBoundaries (X × G) n).mkQ
    apply Subtype.ext
    exact rawChainMap_split_graph_small a b g x₀ U ha hb (n + 1) zsmall.val hk
  rw [← hq] at hclass
  have Hg : g.Homotopy (g.comp b) := by
    simpa only [ContinuousMap.comp_id] using (ContinuousMap.Homotopy.refl g).comp Hb
  have Hf : (rawGraphMap g).Homotopy f := Ha.prodMk Hg
  have hmapA : rawHomologyMap a n = LinearMap.id := by
    rw [← rawHomologyMap_homotopy Ha n, rawHomologyMap_id]
  have hmapB : rawHomologyMap b n = LinearMap.id := by
    rw [← rawHomologyMap_homotopy Hb n, rawHomologyMap_id]
  simpa only [← rawHomologyMap_homotopy Hf n, horizontal, vertical, constant,
    rawHomologyMap_comp, rawHomologyMap_const, hmapA, hmapB,
    LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_zero] using hclass

end BanachIsometric.SingularPrism
