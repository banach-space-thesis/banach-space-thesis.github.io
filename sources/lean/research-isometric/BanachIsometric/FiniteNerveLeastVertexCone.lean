import BanachIsometric.FiniteNerveRationalCoordinates
import Mathlib.Data.Fin.Tuple.Basic

/-! An actual simplicial cone at a least vertex. The face condition is actual
closure under adjoining that vertex; the operator is defined on the literal
finite ordered-face basis. The cone identities are proved from face deletion.
This file does not assume chain acyclicity. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [OrderBot ι] [Fintype ι]
variable (K : Complex ι) (hcone : ∀ s ∈ K.faces, insert (⊥ : ι) s ∈ K.faces)

theorem strictMono_cons_bottom {n : ℕ} (v : StrictOrderedSimplex K n)
    (hv : (⊥ : ι) < v.val.val 0) : StrictMono (Fin.cons (⊥ : ι) v.val.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · change (⊥ : ι) < v.val.val 0
    exact hv
  · change v.val.val j.castSucc < v.val.val j.succ
    exact v.property (Fin.castSucc_lt_succ j)

def prependBottomSimplex {n : ℕ} (v : StrictOrderedSimplex K n)
    (hv : (⊥ : ι) < v.val.val 0) : StrictOrderedSimplex K (n + 1) := by
  let w : Fin (n + 2) →o ι :=
    ⟨Fin.cons (⊥ : ι) v.val.val, (strictMono_cons_bottom K v hv).monotone⟩
  refine ⟨⟨w, K.downward _ (hcone _ v.val.property) _ ?_ ?_⟩,
    strictMono_cons_bottom K v hv⟩
  · intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

@[simp] theorem prependBottomSimplex_zero {n : ℕ} (v : StrictOrderedSimplex K n)
    (hv : (⊥ : ι) < v.val.val 0) :
    (prependBottomSimplex K hcone v hv).val.val 0 = ⊥ := rfl

@[simp] theorem prependBottomSimplex_succ {n : ℕ} (v : StrictOrderedSimplex K n)
    (hv : (⊥ : ι) < v.val.val 0) (j : Fin (n + 1)) :
    (prependBottomSimplex K hcone v hv).val.val j.succ = v.val.val j := rfl

theorem strictOrderedFace_prependBottom_zero {n : ℕ} (v : StrictOrderedSimplex K n)
    (hv : (⊥ : ι) < v.val.val 0) :
    strictOrderedFace K 0 (prependBottomSimplex K hcone v hv) = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply OrderHom.ext
  funext j
  change (prependBottomSimplex K hcone v hv).val.val ((0 : Fin (n + 2)).succAbove j) = _
  rw [Fin.succAbove_zero, prependBottomSimplex_succ]

theorem bottom_lt_face_first {n : ℕ} (v : StrictOrderedSimplex K (n + 1))
    (hv : (⊥ : ι) < v.val.val 0) (i : Fin (n + 2)) :
    (⊥ : ι) < (strictOrderedFace K i v).val.val 0 :=
  hv.trans_le (v.val.val.monotone (Fin.zero_le _))

theorem strictOrderedFace_prependBottom_succ {n : ℕ} (v : StrictOrderedSimplex K (n + 1))
    (hv : (⊥ : ι) < v.val.val 0) (i : Fin (n + 2)) :
    strictOrderedFace K i.succ (prependBottomSimplex K hcone v hv) =
      prependBottomSimplex K hcone (strictOrderedFace K i v) (bottom_lt_face_first K v hv i) := by
  apply Subtype.ext
  apply Subtype.ext
  apply OrderHom.ext
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change (prependBottomSimplex K hcone v hv).val.val (i.succ.succAbove 0) = ⊥
    rw [Fin.succ_succAbove_zero, prependBottomSimplex_zero]
  · change (prependBottomSimplex K hcone v hv).val.val (i.succ.succAbove j.succ) =
      (strictOrderedFace K i v).val.val j
    rw [Fin.succ_succAbove_succ, prependBottomSimplex_succ]
    rfl

def leastVertexCone (n : ℕ) : FiniteRationalChains K n →ₗ[ℚ] FiniteRationalChains K (n + 1) :=
  Finsupp.linearCombination ℚ (fun v : StrictOrderedSimplex K n =>
    if hv : (⊥ : ι) < v.val.val 0 then Finsupp.single (prependBottomSimplex K hcone v hv) 1 else 0)

theorem leastVertexCone_single {n : ℕ} (v : StrictOrderedSimplex K n) :
    leastVertexCone K hcone n (Finsupp.single v 1) =
      if hv : (⊥ : ι) < v.val.val 0 then Finsupp.single (prependBottomSimplex K hcone v hv) 1 else 0 := by
  simp [leastVertexCone]

end BanachIsometric.FiniteNerve
