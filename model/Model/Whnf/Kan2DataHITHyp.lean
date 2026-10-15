import Model.Whnf.Kan2DataHCSound

/-!
# Boundary relations at a signature prefix

`HITHyp2 S n` contains constructor boundary expansion and boundary argument typing for declarations before `n`. The outer induction `hyps_take` derives argument typing from validity at the preceding prefix and then derives boundary expansion from the checked overlap agreement (`Boundary2.hitHyp_of_bndTyping`). These relations support constructor validity and transport at higher inductive types.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

mutual
/-- The closed instance of `Ctor.bndTyped`: at the arguments `Y`, `Y'` and parameters `P1`, `Q1` of
constructor `C` (with `n` arguments) and interval arguments `rs`, the type of each point argument of a
nested constructor of the boundary element, instantiated on the right, is related to the type of the
argument of `C` it is, instantiated on the left. -/
def bndRel (S : Sig) (k d np n : ℕ) (C : Ctor) (ctors : List Ctor) (P1 Q1 : Tm) (Y Y' : List Tm)
    (rs : List I) : Tm → Prop
  | .con _ c' _ as _ =>
    match ctors[c']? with
    | some C' => bndRelArgs S k d np n C ctors P1 Q1 Y Y' rs C' 0 [] as
    | none => True
  | _ => True
/-- The same for the arguments of a nested constructor `C'`, from position `j` on, with the earlier
arguments `prev` (instantiated on the right, most recent first). -/
def bndRelArgs (S : Sig) (k d np n : ℕ) (C : Ctor) (ctors : List Ctor) (P1 Q1 : Tm) (Y Y' : List Tm)
    (rs : List I) (C' : Ctor) (j : ℕ) (prev : List Tm) : Tm → Prop
  | .tcons a as =>
    (∀ x, a = .var x → C'.isRec j = false → x < n →
      RT2 S k ((C.argTy d np (n - 1 - x)).substList ((Y.take (n - 1 - x)).reverse ++ P1.toList.reverse))
        ((C'.argTy d np j).substList (prev ++ Q1.toList.reverse))) ∧
    (C'.isRec j = true → bndRel S k d np n C ctors P1 Q1 Y Y' rs a) ∧
    bndRelArgs S k d np n C ctors P1 Q1 Y Y' rs C' (j + 1) (Ctor.bndAt a Q1.toList Y' rs :: prev) as
  | _ => True

end

/-- Boundary type validity for the declarations before a signature prefix. -/
structure HITHyp2 (S : Sig) (n : ℕ) : Prop where
  conBnd : ∀ {k d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {P1 : Tm} {Y : List Tm} {rs : List I} {kb : ℕ}
    {ψ : I} {b : Tm},
    d < n → S[d]? = some (.data D) → D.isHIT = true → D.ctors[c]? = some C → C.bnd[kb]? = some (ψ, b) →
    I.Entails .one (Ctor.cofAt ψ rs) →
    HasTy S k .one [] (.data d P1) (.univ D.level) → RT2 S k (.data d P1) (.data d P1) →
    Y.length = C.args.length →
    HasTy S k .one [] (.con d c P1 (Tm.ofList Y) rs) (.data d P1) →
    (∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) →
    RE2 S k (.data d P1) (.con d c P1 (Tm.ofList Y) rs) (Ctor.bndAt b P1.toList Y rs)
  /-- The argument types of the nested constructors of a boundary that holds are related to those of
  the constructor (validity of the equations of `Ctor.bndTyped`). -/
  bndTy : ∀ {k d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {P1 : Tm} {Y : List Tm} {rs : List I}
    {kb : ℕ} {ψ : I} {b : Tm},
    d < n → S[d]? = some (.data D) → D.isHIT = true → D.ctors[c]? = some C → C.bnd[kb]? = some (ψ, b) →
    I.Entails .one (Ctor.cofAt ψ rs) →
    HasTy S k .one [] (.data d P1) (.univ D.level) → RT2 S k (.data d P1) (.data d P1) →
    Y.length = C.args.length →
    HasTy S k .one [] (.con d c P1 (Tm.ofList Y) rs) (.data d P1) →
    (∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) →
    bndRel S k d D.params.length C.args.length C D.ctors P1 P1 Y Y rs b

/-- Boundary type validity restricts to a smaller signature prefix. -/
theorem HITHyp2.mono {n m : ℕ} (h : HITHyp2 S n) (hm : m ≤ n) : HITHyp2 S m :=
  ⟨fun hd => h.conBnd (by omega), fun hd => h.bndTy (by omega)⟩


end

end Model.Whnf
