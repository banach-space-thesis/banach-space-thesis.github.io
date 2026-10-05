import ThesisCommon.Analysis.GowersMaureyNormingRIS

/-! Joint selection for finitely many genuinely large-seminorm operators.
Each operator receives an actual length-N RIS. All finite norming functionals
are successive in block order and every off-diagonal entry is small for an
arbitrary specified finite family of operators. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

structure NormingRISFamily (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    {k : ℕ} (T : Fin k → Y →L[𝕜] ShiftSpace D) (r η : ℝ)
    {κ : Type*} (V : κ → Y →L[𝕜] ShiftSpace D) (B N : ℕ) where
  vector : Fin k → Fin N → C00 𝕜
  functional : Fin k → Fin N → C00 𝕜
  mem : ∀ i n, denseEmbedding D (vector i n) ∈ Y
  vector_after : ∀ i n, vector i n ∈ afterCutoff B
  functional_after : ∀ i n, functional i n ∈ afterCutoff B
  ris : ∀ i, IsRIS D 1 (vector i)
  successive : ∀ i, Successive (functional i)
  successive_blocks : ∀ i j, i < j → ∀ s t, Before (functional i s) (functional j t)
  dualUnit : ∀ i n, DualUnit (implicitNorm D) (functional i n)
  detected : ∀ i n, r < RCLike.re (completedPairing D (functional i n)
    (T i ⟨denseEmbedding D (vector i n),mem i n⟩))
  cross : ∀ i j s t, (i,s) ≠ (j,t) → ∀ l,
    ‖completedPairing D (functional i s) (V l ⟨denseEmbedding D (vector j t),mem j t⟩)‖ < η

theorem exists_norming_RIS_family
    (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    {k : ℕ} (T : Fin k → Y →L[𝕜] ShiftSpace D) {r η : ℝ}
    (hr : 0 ≤ r) (hη : 0 < η) (hT : ∀ i, r < blockOperatorSeminorm D Y (T i))
    {κ : Type*} [Fintype κ] (V : κ → Y →L[𝕜] ShiftSpace D) (B N : ℕ) :
    Nonempty (NormingRISFamily D Y T r η V B N) := by
  classical
  induction k with
  | zero =>
    exact ⟨{
      vector := fun i => Fin.elim0 i
      functional := fun i => Fin.elim0 i
      mem := fun i => Fin.elim0 i
      vector_after := fun i => Fin.elim0 i
      functional_after := fun i => Fin.elim0 i
      ris := fun i => Fin.elim0 i
      successive := fun i => Fin.elim0 i
      successive_blocks := fun i => Fin.elim0 i
      dualUnit := fun i => Fin.elim0 i
      detected := fun i => Fin.elim0 i
      cross := fun i => Fin.elim0 i
    }⟩
  | succ k ih =>
    obtain ⟨d⟩ := ih (fun i => T i.castSucc) (fun i => hT i.castSucc)
    obtain ⟨v,a,hv,hvB,haB,has,hRIS,hau,hdet,hbefore,hcross,hinternal⟩ :=
      exists_norming_RIS_of_lt_seminorm D Y (T (Fin.last k)) hr hη (hT (Fin.last k))
        (fun p : Fin k × Fin N => ⟨denseEmbedding D (d.vector p.1 p.2),d.mem p.1 p.2⟩)
        (fun p : Fin k × Fin N => d.functional p.1 p.2) V B N
    let v' : Fin (k+1) → Fin N → C00 𝕜 := Fin.snoc d.vector v
    let a' : Fin (k+1) → Fin N → C00 𝕜 := Fin.snoc d.functional a
    have hmem : ∀ i n, denseEmbedding D (v' i n) ∈ Y := by
      intro i n
      induction i using Fin.lastCases with
      | last => simpa only [v',Fin.snoc_last] using hv n
      | cast i => simpa only [v',Fin.snoc_castSucc] using d.mem i n
    refine ⟨{
      vector := v'
      functional := a'
      mem := hmem
      vector_after := ?_
      functional_after := ?_
      ris := ?_
      successive := ?_
      successive_blocks := ?_
      dualUnit := ?_
      detected := ?_
      cross := ?_
    }⟩
    · intro i n
      induction i using Fin.lastCases with
      | last => simpa only [v',Fin.snoc_last] using hvB n
      | cast i => simpa only [v',Fin.snoc_castSucc] using d.vector_after i n
    · intro i n
      induction i using Fin.lastCases with
      | last => simpa only [a',Fin.snoc_last] using haB n
      | cast i => simpa only [a',Fin.snoc_castSucc] using d.functional_after i n
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [v',Fin.snoc_last] using hRIS
      | cast i => simpa only [v',Fin.snoc_castSucc] using d.ris i
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [a',Fin.snoc_last] using has
      | cast i => simpa only [a',Fin.snoc_castSucc] using d.successive i
    · intro i j hij s t
      induction i using Fin.lastCases with
      | last => exact ((not_lt.mpr (Fin.le_last j)) hij).elim
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa only [a',Fin.snoc_castSucc,Fin.snoc_last] using hbefore (i,s) t
        | cast j => simpa only [a',Fin.snoc_castSucc] using d.successive_blocks i j hij s t
    · intro i n
      induction i using Fin.lastCases with
      | last => simpa only [a',Fin.snoc_last] using hau n
      | cast i => simpa only [a',Fin.snoc_castSucc] using d.dualUnit i n
    · intro i n
      induction i using Fin.lastCases with
      | last => simpa only [v',a',Fin.snoc_last] using hdet n
      | cast i => simpa only [v',a',Fin.snoc_castSucc] using d.detected i n
    · intro i j s t hne l
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          have hst : s ≠ t := fun he => hne (by rw [he])
          simpa only [v',a',Fin.snoc_last] using hinternal s t hst l
        | cast j =>
          simpa only [v',a',Fin.snoc_last,Fin.snoc_castSucc] using (hcross (j,t) s l).2
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simpa only [v',a',Fin.snoc_last,Fin.snoc_castSucc] using (hcross (i,s) t l).1
        | cast j =>
          have hne' : (i,s) ≠ (j,t) := by
            intro he
            exact hne (congrArg (fun p : Fin k × Fin N => (p.1.castSucc,p.2)) he)
          simpa only [v',a',Fin.snoc_castSucc] using d.cross i j s t hne' l

end ThesisCommon.GowersMaurey
