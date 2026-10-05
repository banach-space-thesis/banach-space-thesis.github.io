import ThesisCommon.Analysis.GowersMaureyCodedPairAppend

/-! Genuine finite recursive selection of detecting coded pairs. The proof
chooses every functional and every vector from the actual bad block sequence;
arbitrary prescribed prefix-growth budgets are met by rational perturbation. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_coded_detecting_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖)
    {η : ℝ} (hη : 0 < η) (seed n : ℕ) (G : C00 𝕜 → ℝ) :
    Nonempty (CodedDetectingFamily T ε η seed n G) := by
  classical
  induction n with
  | zero =>
    exact ⟨{
      pair := Fin.elim0
      code_domain := by simp [CodingDomain]
      successive := fun i => Fin.elim0 i
      size_rule := fun i => Fin.elim0 i
      size_strict := fun i => Fin.elim0 i
      growth := fun i => Fin.elim0 i
      cutoff := fun i => Fin.elim0 i
      cross_image := fun i => Fin.elim0 i
      cross_spread := fun i => Fin.elim0 i
      next_size := fun i => Fin.elim0 i
      next_cutoff := fun i => Fin.elim0 i
      next_growth := fun h => (Nat.not_lt_zero _ h).elim
    }⟩
  | succ n ih =>
    obtain ⟨d⟩ := ih
    obtain ⟨m,hm⟩ : ∃ m, D.j (2*m+1) = if n = 0 then D.j (2*seed+1)
        else D.sigma (List.ofFn (fun i => (d.pair i).functional)) := by
      by_cases hn : n = 0
      · exact ⟨seed,by simp [hn]⟩
      · obtain ⟨m,hm⟩ := D.sigma_even _ d.code_domain
        exact ⟨m,by simpa [hn] using hm.symm⟩
    let R := Finset.univ.sup (fun i => (d.pair i).size)
    obtain ⟨x,hx,a,hxB,haB,hxn,hRIS,hinterval,havg,ha0,hr,hcode,hM,hcut,hG,hdet,horbit,hcross⟩ :=
      exists_coded_detecting_NPair_after_family u hne T q hq hε hsep
        (fun i => (d.pair i).vector) (fun i => (d.pair i).functional)
        (fun i => (d.pair i).mem) d.code_domain m 0 (D.j (2*m+1)) R
        (fun x => G ((∑ i, (d.pair i).vector)+x)) hη
    let p : DetectingPair T ε := {
      index := m
      vector := x
      mem := hx
      functional := a
      norm_bound := hxn
      ris := hRIS
      interval_bound := hinterval
      averaged := havg
      nonzero := ha0
      rational := hr
      detected := hdet
      orbit_small := horbit
    }
    refine ⟨d.append p hm hcode hM hcut hG ?_⟩
    intro i
    refine ⟨(hcross i).1,(hcross i).2.2.1,(hcross i).2.2.2.1,?_⟩
    intro z hz
    exact (hcross i).2.2.2.2 z (spreadParameterSquare_mono
      (Finset.le_sup (f := fun i => (d.pair i).size) (Finset.mem_univ i)) hz)

theorem exists_detecting_special_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖)
    {η : ℝ} (hη : 0 < η) (k : ℕ) (hk : 0 < k) (G : C00 𝕜 → ℝ) :
    ∃ d : CodedDetectingFamily T ε η (k-1) k G,
      SpecialSequence D (implicitNorm D) (fun i => (d.pair i).functional) := by
  obtain ⟨d⟩ := exists_coded_detecting_family u hne T q hq hε hsep hη (k-1) k G
  exact ⟨d,d.specialSequence hk⟩

end ThesisCommon.GowersMaurey
