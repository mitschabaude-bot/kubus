import Model.Whnf.Per2

/-!
# The binary relation of inductive types is a partial equivalence
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

theorem Comp2_empty (m k : ℕ) (f : Hom k m) : Comp2 S ∅ m k f = Pack2.bot := by
  rw [Comp2_eq]; unfold compF2; rw [dif_neg (by simp)]

theorem perP_bot : PERP Pack2.bot :=
  ⟨fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim⟩

/-- The point argument relations of an inductive type's code are partial equivalences. -/
theorem perP_tyLook {Θ : SData m} (ih : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → PER2 S n (Θ.ty c j n g pre))
    {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V) :
    PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)) := by
  rcases tyLook_cases (Θ.restr h) c j pre with h0 | h0
  · rw [h0, Comp2_empty]; exact perP_bot
  · rw [tyLook_eq h0]
    exact ih c j n (h.comp (Hom.id n)) pre (ptValid_of_validPre h0) n (Hom.id n)

section
variable {k0 : ℕ} (Θ : SData m) (f : Hom k0 m)

/-- The argument clause of an inductive type, at the restrictions of `g`, from the parameters `ps`
(at which the arguments are related) to the parameters `ps'`. -/
def argRelH (S : Sig) (k : ℕ) (g : Hom k k0) (ps ps' : Tm) : Prop :=
  ∀ k'' (σ' : ISub k'' k) (c : ℕ) (C : Ctor) (args args' : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → args'.length = args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k'' (g.comp σ'.hom)
        (.data Θ.idx (ps.isub σ')) args[j] args'[j]) →
    (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
      dataP2 S Θ f k'' (g.comp σ'.hom) c j ((args.take j).map (semK S k''))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList
          ((args.take j).reverse ++ (ps.isub σ').toList.reverse))
        args[j] args'[j]) →
    (Comp2 S (tyLook (shapeV (Θ.restr (f.comp (g.comp σ'.hom)))) c args.length (args.map (semK S k'')))
      k'' k'' (Hom.id k'')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args.reverse ++ (ps.isub σ').toList.reverse))
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList
        (args'.reverse ++ (ps'.isub σ').toList.reverse))

theorem argRel2_iff {k : ℕ} {f : Hom k m} {k' : ℕ} (σ : ISub k' k) {ps ps' : Tm} :
    argRel2 S Θ f k' σ ps ps' ↔ argRelH Θ f S k' σ.hom ps ps' := by
  unfold argRel2 argRelH; simp only [ISub.hom_comp]

theorem argRelH_isub {k : ℕ} {g : Hom k k0} {ps ps' : Tm} (h : argRelH Θ f S k g ps ps') (σ : ISub k' k) :
    argRelH Θ f S k' (g.comp σ.hom) (ps.isub σ) (ps'.isub σ) := by
  intro k3 σ3 c C args args' hC hl hl' hr hrec hpt
  have := h k3 (σ.comp σ3) c C args args' hC hl hl' hr
    (fun j hj hj' hrj => by have := hrec j hj hj' hrj; rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub] at this)
    (fun j hj hj' hrj => by have := hpt j hj hj' hrj; rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub] at this)
  rwa [Hom.comp_assoc, ← ISub.hom_comp, Tm.isub_isub, Tm.isub_isub]

end

end

end Model.Whnf
