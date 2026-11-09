import BanachIsometric.SphereRepetition

/-! The actual pinned Mathlib homotopy group of a product is the product of
the actual homotopy groups. Maps are postcomposition of literal cubical loops;
injectivity combines literal relative homotopies, not a product axiom. -/

noncomputable section
namespace BanachIsometric
open SphereGenerator
open scoped Topology Topology.Homotopy unitInterval

variable {N X Y : Type*} [DecidableEq N] [Nonempty N]
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def basedHomotopyGroupMap (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := Quotient.map' (mapGenLoop f hf) (fun _ _ h => h.comp_continuousMap f)
  map_one' := by
    change genLoopClass (mapGenLoop f hf GenLoop.const) = _
    rw [mapGenLoop_const]
    rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h α =>
      induction b using Quotient.inductionOn with
      | h β =>
        let Φ : HomotopyGroup N X x → HomotopyGroup N Y y :=
          Quotient.map' (mapGenLoop f hf) (fun _ _ h => h.comp_continuousMap f)
        change Φ (genLoopClass α * genLoopClass β) = Φ (genLoopClass α) * Φ (genLoopClass β)
        have hmul : genLoopClass α * genLoopClass β =
            genLoopClass (GenLoop.transAt (Classical.arbitrary N) β α) := HomotopyGroup.mul_spec
        rw [hmul]
        change genLoopClass (mapGenLoop f hf (GenLoop.transAt (Classical.arbitrary N) β α)) =
          genLoopClass (mapGenLoop f hf α) * genLoopClass (mapGenLoop f hf β)
        rw [mapGenLoop_transAt]
        exact (HomotopyGroup.mul_spec (i := Classical.arbitrary N)).symm

def productGenLoop (α : GenLoop N X x) (β : GenLoop N Y y) : GenLoop N (X × Y) (x, y) :=
  ⟨α.1.prodMk β.1, fun u hu => Prod.ext (α.property u hu) (β.property u hu)⟩

omit [DecidableEq N] [Nonempty N] in
@[simp] theorem mapGenLoop_fst_product (α : GenLoop N X x) (β : GenLoop N Y y) :
    mapGenLoop (ContinuousMap.fst : C(X × Y, X)) rfl (productGenLoop α β) = α := by
  ext u
  rfl

omit [DecidableEq N] [Nonempty N] in
@[simp] theorem mapGenLoop_snd_product (α : GenLoop N X x) (β : GenLoop N Y y) :
    mapGenLoop (ContinuousMap.snd : C(X × Y, Y)) rfl (productGenLoop α β) = β := by
  ext u
  rfl

def productHomotopyGroupMap :
    HomotopyGroup N (X × Y) (x, y) →* (HomotopyGroup N X x × HomotopyGroup N Y y) :=
  (basedHomotopyGroupMap (ContinuousMap.fst : C(X × Y, X)) rfl).prod
    (basedHomotopyGroupMap (ContinuousMap.snd : C(X × Y, Y)) rfl)

theorem productHomotopyGroupMap_injective :
    Function.Injective (productHomotopyGroupMap (N := N) (x := x) (y := y)) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      intro hab
      have hfst := congrArg Prod.fst hab
      have hsnd := congrArg Prod.snd hab
      obtain ⟨H₁⟩ := Quotient.exact hfst
      obtain ⟨H₂⟩ := Quotient.exact hsnd
      let H := H₁.toHomotopy.prodMk H₂.toHomotopy
      have hzero : (ContinuousMap.fst.comp α.1).prodMk (ContinuousMap.snd.comp α.1) = α.1 := by
        apply ContinuousMap.ext
        intro u
        rfl
      have hone : (ContinuousMap.fst.comp β.1).prodMk (ContinuousMap.snd.comp β.1) = β.1 := by
        apply ContinuousMap.ext
        intro u
        rfl
      apply Quotient.sound
      refine ⟨{ toHomotopy := H.cast hzero hone, prop' := ?_ }⟩
      intro t u hu
      apply Prod.ext
      · exact H₁.eq_fst t hu
      · exact H₂.eq_fst t hu

theorem productHomotopyGroupMap_surjective :
    Function.Surjective (productHomotopyGroupMap (N := N) (x := x) (y := y)) := by
  rintro ⟨a, b⟩
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      refine ⟨genLoopClass (productGenLoop α β), ?_⟩
      apply Prod.ext
      · change genLoopClass (mapGenLoop ContinuousMap.fst rfl (productGenLoop α β)) = genLoopClass α
        rw [mapGenLoop_fst_product]
      · change genLoopClass (mapGenLoop ContinuousMap.snd rfl (productGenLoop α β)) = genLoopClass β
        rw [mapGenLoop_snd_product]

def productHigherHomotopyEquiv :
    HomotopyGroup N (X × Y) (x, y) ≃* (HomotopyGroup N X x × HomotopyGroup N Y y) :=
  MulEquiv.ofBijective productHomotopyGroupMap
    ⟨productHomotopyGroupMap_injective, productHomotopyGroupMap_surjective⟩

end BanachIsometric
