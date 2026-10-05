import ThesisCommon.Analysis.GowersMaureyDetailedCodedDetectingNPairs
import ThesisCommon.Analysis.GowersMaureyNPairFunctionalBounds

/-! Extension of an actual finite coded family by a detecting N-pair.
Both operator cross terms are made small on the original subspace. The
finite spread cross terms vanish exactly. No extension of the operator,
shrinking-basis assumption, or extra growth condition on the code is used. -/
noncomputable section
open Filter
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_coded_detecting_NPair_after_family
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖)
    {l : ℕ} (x₀ a₀ : Fin l → C00 𝕜)
    (hx₀ : ∀ i, denseEmbedding D (x₀ i) ∈ Y)
    (hcode : CodingDomain (List.ofFn a₀))
    (m B₀ M R : ℕ) (W : C00 𝕜 → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ x : C00 𝕜, ∃ hx : denseEmbedding D x ∈ Y, ∃ a : C00 𝕜,
      x ∈ afterCutoff B₀ ∧ a ∈ afterCutoff B₀ ∧ implicitNorm D x ≤ 4 ∧
      (∃ v : Fin (D.j (2*m+1)) → C00 𝕜, IsRIS D 1 v ∧ x = normalizedPairVector v) ∧
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) →
        intervalNorm D n x ≤ 8) ∧
      AveragedFunctional (implicitNorm D) (D.j (2*m+1)) a ∧ a ≠ 0 ∧
      RationalUnitSequence a ∧ CodingDomain (List.ofFn a₀ ++ [a]) ∧
      M < D.sigma (List.ofFn a₀ ++ [a]) ∧
      pairingSpreadCutoff a x < D.sigma (List.ofFn a₀ ++ [a]) ∧
      W x < logarithmicWeight (D.sigma (List.ofFn a₀ ++ [a])) ∧
      ε/16 < RCLike.re (completedPairing D a (T ⟨denseEmbedding D x,hx⟩)) ∧
      (∀ z ∈ spreadParameterSquare (D.j (2*m+1)),
        ‖pairing a (spread z.1 z.2 x)‖ ≤ (‖T‖+1) / (D.j (2*m+1) : ℝ)^2) ∧
      ∀ i, Before (x₀ i) x ∧ Before (a₀ i) a ∧
        ‖completedPairing D (a₀ i) (T ⟨denseEmbedding D x,hx⟩)‖ < η ∧
        ‖completedPairing D a (T ⟨denseEmbedding D (x₀ i),hx₀ i⟩)‖ < η ∧
        ∀ z ∈ spreadParameterSquare R,
          pairing (a₀ i) (spread z.1 z.2 x) = 0 ∧
          pairing a (spread z.1 z.2 (x₀ i)) = 0 := by
  classical
  let N := D.j (2*m+1)
  have hN : 0 < N := D.j_positive _
  have hf : 0 < logarithmicWeight N :=
    zero_lt_one.trans_le (one_le_logarithmicWeight hN)
  let K₀ := max B₀ (Finset.univ.sup (fun i : Fin l =>
    max ((x₀ i).support.sup id) (max ((a₀ i).support.sup id + R)
      ((spreadParameterSquare R).sup (fun z => (spread z.1 z.2 (x₀ i)).support.sup id)))))
  have htail : ∀ᶠ K : ℕ in atTop, K₀ ≤ K ∧ ∀ i : Fin l,
      ∀ a : C00 𝕜, a ∈ afterCutoff K → DualUnit (implicitNorm D) a →
        ‖completedPairing D a (T ⟨denseEmbedding D (x₀ i),hx₀ i⟩)‖ < η := by
    apply (eventually_ge_atTop K₀).and
    apply eventually_all.mpr
    intro i
    exact eventually_tail_dualUnit_small D _ hη
  obtain ⟨K,hK,htailK⟩ := htail.exists
  have hfront : ∀ᶠ j : ℕ in atTop, ∀ i : Fin l,
      ‖completedPairing D (a₀ i) (T (u.inSubspace j))‖ < η/(2*logarithmicWeight N) := by
    apply eventually_all.mpr
    intro i
    have h := u.tendsto_subspace_functional_zero ((completedPairing D (a₀ i)).comp T)
    exact h.norm.eventually_lt_const (by simpa using div_pos hη (mul_pos (by norm_num) hf))
  obtain ⟨L,hL⟩ := eventually_atTop.mp hfront
  let B := max K L
  have hBK : K ≤ B := le_max_left _ _
  have hBB₀ : B₀ ≤ B := (le_max_left _ _).trans (hK.trans hBK)
  have hbound (i : Fin l) :
      max ((x₀ i).support.sup id) (max ((a₀ i).support.sup id + R)
        ((spreadParameterSquare R).sup (fun z => (spread z.1 z.2 (x₀ i)).support.sup id))) ≤ K :=
    (Finset.le_sup (f := fun i : Fin l =>
      max ((x₀ i).support.sup id) (max ((a₀ i).support.sup id + R)
        ((spreadParameterSquare R).sup (fun z => (spread z.1 z.2 (x₀ i)).support.sup id))))
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hK)
  have hxi (i : Fin l) : (x₀ i).support.sup id ≤ K :=
    (max_le_iff.mp (hbound i)).1
  have hai (i : Fin l) : (a₀ i).support.sup id + R ≤ K :=
    (max_le_iff.mp (max_le_iff.mp (hbound i)).2).1
  have hzi (i : Fin l) (z) (hz : z ∈ spreadParameterSquare R) :
      (spread z.1 z.2 (x₀ i)).support.sup id ≤ K :=
    (Finset.le_sup (f := fun z : ℕ × ℕ =>
      (spread z.1 z.2 (x₀ i)).support.sup id) hz).trans
        (max_le_iff.mp (max_le_iff.mp (hbound i)).2).2
  have hprefix : ∀ a ∈ List.ofFn a₀, ∀ j ∈ a.support, j ≤ B := by
    intro a ha j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    have hj' : j ≤ (a₀ i).support.sup id := Finset.le_sup (f := id) hj
    have hi := hai i
    omega
  obtain ⟨x,hx,a,hxB,haB,hxn,hRIS,hsource,hinterval,havg,ha0,hr,hcoding,
      hM,hcut,hW,hdetect,horbit⟩ :=
    exists_coded_detecting_NPair_with_RIS u hne T q hq hε hsep m B M W
      (List.ofFn a₀) hcode hprefix
  have haK : a ∈ afterCutoff K := fun j hj => haB j (hj.trans hBK)
  refine ⟨x,hx,a,(fun j hj => hxB j (hj.trans hBB₀)),
    (fun j hj => haB j (hj.trans hBB₀)),hxn,hRIS,hinterval,havg,ha0,hr,hcoding,
    hM,hcut,hW,hdetect,horbit,?_⟩
  intro i
  have hxBefore : Before (x₀ i) x := before_of_mem_afterCutoff
    (fun j hj => (Finset.le_sup (f := id) hj).trans ((hxi i).trans hBK)) hxB
  have haBefore : Before (a₀ i) a := before_of_mem_afterCutoff
    (hprefix _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) haB
  refine ⟨hxBefore,haBefore,?_,htailK i a haK havg.dualUnit,?_⟩
  · obtain ⟨b,hb,hbB,hxb⟩ := hsource
    have hvalue : (⟨denseEmbedding D x,hx⟩ : Y) =
        normalizedPairSum (𝕜 := 𝕜) (fun j => u.inSubspace (b j)) := by
      apply Subtype.ext
      rw [normalizedPairSum_subspace_value D Y _ (fun j => u.vector (b j)) (fun _ => rfl)]
      exact congrArg (denseEmbedding D) hxb
    rw [hvalue]
    have hh := normalizedPairSum_functional_bound hN (fun j => u.inSubspace (b j))
      ((completedPairing D (a₀ i)).comp T)
      (fun j => (hL (b j) ((le_max_right K L).trans (hbB j).le) i).le)
    apply hh.trans_lt
    calc
      logarithmicWeight N * (η/(2*logarithmicWeight N)) = η/2 := by field_simp
      _ < η := by linarith
  · intro z hz
    refine ⟨pairing_eq_zero_of_before (before_of_mem_afterCutoff
      (fun j hj => Finset.le_sup (f := id) hj) (spread_mem_afterCutoff _ z.1 z.2 ?_)),
      pairing_eq_zero_of_before_rev (before_of_mem_afterCutoff
        (fun j hj => (Finset.le_sup (f := id) hj).trans (hzi i z hz)) haK)⟩
    intro j hj
    apply hxB j
    have hzR : z.1 ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hz).1)
    have hi := hai i
    omega

end ThesisCommon.GowersMaurey
