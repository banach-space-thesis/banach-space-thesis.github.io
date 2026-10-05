import ThesisCommon.Analysis.GowersMaureyCodedNPairExtension
import ThesisCommon.Analysis.GowersMaureySpecialCodeCounts

/-! Data for the finite recursive special-pair construction. Every member
contains an actual normalized RIS and a genuine detecting functional on
the original operator domain. The code rule is the literal source rule. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

structure DetectingPair {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (T : Y →L[𝕜] ShiftSpace D) (ε : ℝ) where
  index : ℕ
  vector : C00 𝕜
  mem : denseEmbedding D vector ∈ Y
  functional : C00 𝕜
  norm_bound : implicitNorm D vector ≤ 4
  ris : ∃ v : Fin (D.j (2*index+1)) → C00 𝕜,
    IsRIS D 1 v ∧ vector = normalizedPairVector v
  interval_bound : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*index+1) : ℝ) →
    intervalNorm D n vector ≤ 8
  averaged : AveragedFunctional (implicitNorm D) (D.j (2*index+1)) functional
  nonzero : functional ≠ 0
  rational : RationalUnitSequence functional
  detected : ε/16 < RCLike.re (completedPairing D functional (T ⟨denseEmbedding D vector,mem⟩))
  orbit_small : ∀ z ∈ spreadParameterSquare (D.j (2*index+1)),
    ‖pairing functional (spread z.1 z.2 vector)‖ ≤ (‖T‖+1) / (D.j (2*index+1) : ℝ)^2

def DetectingPair.size {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    {T : Y →L[𝕜] ShiftSpace D} {ε : ℝ} (p : DetectingPair T ε) : ℕ :=
  D.j (2*p.index+1)

def DetectingPair.inSubspace {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    {T : Y →L[𝕜] ShiftSpace D} {ε : ℝ} (p : DetectingPair T ε) : Y :=
  ⟨denseEmbedding D p.vector,p.mem⟩

structure CodedDetectingFamily {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (T : Y →L[𝕜] ShiftSpace D) (ε η : ℝ) (seed n : ℕ) (G : C00 𝕜 → ℝ) where
  pair : Fin n → DetectingPair T ε
  code_domain : CodingDomain (List.ofFn (fun i => (pair i).functional))
  successive : Successive (fun i => (pair i).vector)
  size_rule : ∀ i, (pair i).size = if i.val = 0 then D.j (2*seed+1)
    else D.sigma (initialSegment (fun j => (pair j).functional) i)
  size_strict : StrictMono (fun i => (pair i).size)
  growth : ∀ i, 0 < i.val → G (prefixSum (fun j => (pair j).vector) i) <
    logarithmicWeight (pair i).size
  cutoff : ∀ i j, i < j → pairingSpreadCutoff (pair i).functional (pair i).vector < (pair j).size
  cross_image : ∀ i j, i < j →
    ‖completedPairing D (pair i).functional (T (pair j).inSubspace)‖ < η ∧
    ‖completedPairing D (pair j).functional (T (pair i).inSubspace)‖ < η
  cross_spread : ∀ i j, i < j → ∀ z ∈ spreadParameterSquare (pair i).size,
    pairing (pair i).functional (spread z.1 z.2 (pair j).vector) = 0 ∧
    pairing (pair j).functional (spread z.1 z.2 (pair i).vector) = 0
  next_size : ∀ i, (pair i).size < D.sigma (List.ofFn (fun j => (pair j).functional))
  next_cutoff : ∀ i, pairingSpreadCutoff (pair i).functional (pair i).vector <
    D.sigma (List.ofFn (fun j => (pair j).functional))
  next_growth : 0 < n → G (∑ i, (pair i).vector) <
    logarithmicWeight (D.sigma (List.ofFn (fun j => (pair j).functional)))

theorem initialSegment_snoc_castSucc {n : ℕ} (a : Fin n → C00 𝕜)
    (b : C00 𝕜) (i : Fin n) :
    initialSegment (Fin.snoc a b) i.castSucc = initialSegment a i := by
  apply congrArg List.ofFn
  funext j
  change Fin.snoc (α := fun _ => C00 𝕜) a b (⟨j.val,j.isLt.trans i.isLt⟩ : Fin n).castSucc = _
  simp [Fin.snoc, j.isLt.trans i.isLt]

theorem initialSegment_snoc_last {n : ℕ} (a : Fin n → C00 𝕜) (b : C00 𝕜) :
    initialSegment (Fin.snoc a b) (Fin.last n) = List.ofFn a := by
  apply congrArg List.ofFn
  funext j
  change Fin.snoc (α := fun _ => C00 𝕜) a b j.castSucc = _
  simp

theorem ofFn_snoc {α : Type*} {n : ℕ} (a : Fin n → α) (b : α) :
    List.ofFn (Fin.snoc a b) = List.ofFn a ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem map_snoc {α β : Type*} {n : ℕ} (a : Fin n → α) (b : α) (f : α → β) :
    (fun i => f (Fin.snoc (α := fun _ => α) a b i)) = Fin.snoc (fun i => f (a i)) (f b) := by
  funext i
  induction i using Fin.lastCases <;> simp

theorem relation_snoc {α : Type*} {n : ℕ} (a : Fin n → α) (b : α)
    (R : α → α → Prop) (hold : ∀ i j, i < j → R (a i) (a j))
    (hnew : ∀ i, R (a i) b) : ∀ i j, i < j → R (Fin.snoc (α := fun _ => α) a b i) (Fin.snoc (α := fun _ => α) a b j) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last => exact ((not_lt.mpr (Fin.le_last j)) hij).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using hnew i
    | cast j => simpa using hold i j hij

theorem prefixSum_snoc_castSucc {n : ℕ} (a : Fin n → C00 𝕜)
    (b : C00 𝕜) (i : Fin n) :
    prefixSum (Fin.snoc a b) i.castSucc = prefixSum a i := by
  classical
  simp only [prefixSum, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [not_lt.mpr (Fin.le_last i.castSucc)]

theorem prefixSum_snoc_last {n : ℕ} (a : Fin n → C00 𝕜) (b : C00 𝕜) :
    prefixSum (Fin.snoc a b) (Fin.last n) = ∑ i, a i := by
  classical
  simp only [prefixSum, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp

theorem CodedDetectingFamily.specialSequence {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} {T : Y →L[𝕜] ShiftSpace D}
    {ε η : ℝ} {k : ℕ} {G : C00 𝕜 → ℝ} (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k G) :
    SpecialSequence D (implicitNorm D) (fun i => (d.pair i).functional) := by
  have hs : Successive (fun i => (d.pair i).functional) :=
    List.pairwise_ofFn.mp d.code_domain.2
  refine ⟨hs,fun i => (d.pair i).rational,?_⟩
  intro i
  have hr := d.size_rule i
  have he : 2*(k-1)+1 = 2*k-1 := by omega
  rw [he] at hr
  rw [← hr]
  exact (d.pair i).averaged

end ThesisCommon.GowersMaurey
