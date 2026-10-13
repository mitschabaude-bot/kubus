import Model.Canon.Proj

/-!
# Weak-head reduction of closed terms

One step of deterministic weak-head reduction `step S t` of closed terms (no term variables, any
number of interval variables, the trivial restriction `.one`): the spec's computation rules
oriented left to right, under head positions. A Kan operation first reduces its type line to a
weak-head normal form and then computes by its head; at an inductive type it first reduces its
base. Faces are decided by `I.entails .one`. Determinism holds by construction.

The composition in an inductive type without path constructors (`hcompCon`) takes the tube's
arguments to be its projections (`Model.Canon.proj`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore Model.Canon

/-- The first boundary of constructor `C` that holds at the interval arguments `rs`, with the
boundary term. -/
def firstBnd (bnd : List (I × Tm)) (rs : List I) : Option Tm :=
  match bnd.find? fun p => I.entails .one (Ctor.cofAt p.1 rs) with
  | some p => some p.2
  | none => none

/-- One step of weak-head reduction. -/
def step (S : Sig) : Tm → Option Tm
  | .const c => match S[c]? with
    | some (.defn t _) => some t
    | _ => none
  | .app f a => match f with
    | .lam _ t => some (t.inst a)
    | _ => (step S f).map (.app · a)
  | .fst p => match p with
    | .pair a _ => some a
    | _ => (step S p).map .fst
  | .snd p => match p with
    | .pair _ b => some b
    | _ => (step S p).map .snd
  | .papp p r => match p with
    | .plam t => some (t.dinst r)
    | _ => (step S p).map (.papp · r)
  | .split φ t ψ u =>
    if I.entails .one φ then some t else if I.entails .one ψ then some u else none
  | .transp A φ a =>
    if I.entails .one φ then some a else
    match step S A with
    | some A' => some (.transp A' φ a)
    | none => match A with
      | .univ _ => some a
      | .pi A B => some (Tm.transpPi A B φ a)
      | .sigma A B => some (Tm.transpSigma A B φ a)
      | .path A x y => some (Tm.transpPath A x y φ a)
      | .ipi A => some (Tm.transpIPi A φ a)
      | .glue A ψ T e => some (Tm.transpGlueWith ψ.forall0 A ψ T e φ a)
      | .data d ps => match S[d]? with
        | some (.data D) =>
          if D.params = [] then some a else
          match step S a with
          | some a' => some (.transp A φ a')
          | none => match a with
            | .con d' c _ args rs => if d' ≠ d then none else match D.ctors[c]? with
              | some C => some (.con d c (ps.dinst .one)
                  (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs)
              | none => none
            | .hcomp (.data d' _) ψ u a' =>
              if d' = d ∧ D.isHIT then some (.hcomp (.data d (ps.dinst .one)) ψ
                (.transp ((Tm.data d ps).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) φ.shift u)
                (.transp (.data d ps) φ a'))
              else none
            | _ => none
        | _ => none
      | _ => none
  | .hcomp A φ u a =>
    if I.entails .one φ then some (u.dinst .one) else
    match step S A with
    | some A' => some (.hcomp A' φ u a)
    | none => match A with
      | .univ _ => some (Tm.hcompU φ u a)
      | .pi A B => some (Tm.hcompPi A B φ u a)
      | .sigma A B => some (Tm.hcompSigma A B φ u a)
      | .path A x y => some (Tm.hcompPath A x y φ u a)
      | .ipi A => some (Tm.hcompIPi A φ u a)
      | .glue A ψ T e => some (Tm.hcompGlue A ψ T e φ u a)
      | .data d ps => match S[d]? with
        | some (.data D) =>
          if D.isHIT then none else
          match step S a with
          | some a' => some (.hcomp A φ u a')
          | none => match a with
            | .con d' c _ args [] => if d' ≠ d then none else match D.ctors[c]? with
              | some C => some (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps)
                  ps.dshift.toList φ 0 []
                  ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u) args.toList)) [])
              | none => none
            | _ => none
        | _ => none
      | _ => none
  | .glue _ φ T _ => if I.entails .one φ then some T else none
  | .glueEl φ _ t _ => if I.entails .one φ then some t else none
  | .unglue φ e g =>
    if I.entails .one φ then some (.app (.fst e) g) else
    match step S g with
    | some g' => some (.unglue φ e g')
    | none => match g with
      | .glueEl _ _ _ a => some a
      | _ => none
  | .con d c ps args rs => match S[d]? with
    | some (.data D) => match D.ctors[c]? with
      | some C => (firstBnd C.bnd rs).map fun b => Ctor.bndAt b ps.toList args.toList rs
      | none => none
    | _ => none
  | .elim d ps P bs t =>
    match step S t with
    | some t' => some (.elim d ps P bs t')
    | none => match t with
      | .con d' c _ args rs => if d' ≠ d then none else match S[d]?, bs.toList[c]? with
        | some (.data D), some b => match D.ctors[c]? with
          | some C => some (Tm.papps (Tm.apps b (args.toList ++
              C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs)
          | none => none
        | _, _ => none
      | .hcomp (.data d' _) φ u a => match S[d]? with
        | some (.data D) =>
          if d' = d ∧ D.isHIT then some (Tm.comp (P.subst (fun | 0 => Tm.hfill (.data d ps) φ u a | j + 1 => .var j)
              (fun i => .var (i + 1))) φ (.elim d ps.dshift P.dshift bs.dshift u) (.elim d ps P bs a))
          else none
        | _ => none
      | _ => none
  | _ => none

/-- Weak-head normal forms: terms without a step. -/
def IsWhnf (S : Sig) (t : Tm) : Prop := step S t = none

/-- Reduction: the reflexive-transitive closure of `step`. -/
inductive Red (S : Sig) : Tm → Tm → Prop
  | refl (t : Tm) : Red S t t
  | step {t t' t'' : Tm} : step S t = some t' → Red S t' t'' → Red S t t''

/-- Reduction to weak-head normal form. -/
def RedW (S : Sig) (t w : Tm) : Prop := Red S t w ∧ IsWhnf S w

theorem Red.trans {S : Sig} {t t' t'' : Tm} (h : Red S t t') (h' : Red S t' t'') : Red S t t'' := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

/-- Weak-head normal forms are unique. -/
theorem RedW.unique {S : Sig} {t w w' : Tm} (h : RedW S t w) (h' : RedW S t w') : w = w' := by
  obtain ⟨h1, hw⟩ := h
  obtain ⟨h2, hw'⟩ := h'
  induction h1 with
  | refl t =>
    cases h2 with
    | refl => rfl
    | step hs _ => unfold IsWhnf at hw; rw [hw] at hs; cases hs
  | step hs _ ih =>
    cases h2 with
    | refl => unfold IsWhnf at hw'; rw [hw'] at hs; cases hs
    | step hs' r' => rw [hs] at hs'; cases hs'; exact ih hw r'

end Model.Whnf
