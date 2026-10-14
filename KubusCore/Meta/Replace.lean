import KubusCore.Meta.Final

/-!
# Metatheory: replacement of β-redexes

Contracting the β-redexes `(λ x. b) a` inside a typed term (in function, argument, λ-body,
pair, projection, path-application and path-abstraction positions) gives a judgmentally
equal term at the same type: `beta_replace`. The proof is by induction on the typing
derivation, with the congruence rules, `piBeta`, and presupposition for the typings of the
contracted sides.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `f a`, contracted if `f` is a λ. -/
def _root_.KubusCore.Tm.betaApp (f a : Tm) : Tm :=
  match f with
  | .lam _ b => b.inst a
  | f => .app f a

/-- Contract the β-redexes `(λ x. b) a` in function, argument, λ-body, pair, projection,
path-application and path-abstraction positions (one pass, innermost first). -/
def _root_.KubusCore.Tm.betaIn : Tm → Tm
  | .app f a => Tm.betaApp f.betaIn a.betaIn
  | .lam A t => .lam A t.betaIn
  | .pair a b => .pair a.betaIn b.betaIn
  | .fst p => .fst p.betaIn
  | .snd p => .snd p.betaIn
  | .papp p r => .papp p.betaIn r
  | .plam t => .plam t.betaIn
  | t => t

section
variable (hS : SigClosed S) (hP : Presup0 S)
include hS hP

theorem betaApp_eq {Ψ Φ Γ f a T} (h : EqTm0 S Ψ Φ Γ (app f a) (app f a) T) :
    EqTm0 S Ψ Φ Γ (app f a) (Tm.betaApp f a) T := by
  cases f with
  | lam A b => exact EqTm0.piBeta (hP h).1
  | _ => exact h

theorem beta_replace {Ψ Φ Γ t T} (h : HasTy0 S Ψ Φ Γ t T) : EqTm0 S Ψ Φ Γ t t.betaIn T :=
  match h with
  | .var h0 h1 => EqTm0.refl (.var h0 h1)
  | .conv h0 h1 => EqTm0.conv (beta_replace h0) h1
  | .restrict h0 h1 h2 => EqTm0.restrict h0 h1 (beta_replace h2)
  | .const h0 h1 => EqTm0.refl (.const h0 h1)
  | .univ h0 h1 => EqTm0.refl (.univ h0 h1)
  | .cumul h0 h1 => EqTm0.cumul h0 (beta_replace h1)
  | .pi h0 h1 => EqTm0.refl (.pi h0 h1)
  | .lam h0 h1 => EqTm0.lam h0 (beta_replace h1)
  | .app h0 h1 => by
    have e := EqTm0.app (beta_replace h0) (beta_replace h1)
    exact EqTm0.trans e (betaApp_eq hS hP (EqTm0.refl (hP e).2))
  | .sigma h0 h1 => EqTm0.refl (.sigma h0 h1)
  | .pair h0 h1 h2 => EqTm0.pair h0 (beta_replace h1) (beta_replace h2)
  | .fst h0 => EqTm0.fst (beta_replace h0)
  | .snd h0 => EqTm0.snd (beta_replace h0)
  | .path h0 h1 h2 => EqTm0.refl (.path h0 h1 h2)
  | .plam h0 h1 h2 h3 => by
    have e := beta_replace h1
    have e0 := EqTm0.dsubst hS e (r := .zero) trivial
    have e1 := EqTm0.dsubst hS e (r := .one) trivial
    have h' := HasTy0.plam h0 (hP e).2 (EqTm0.trans (EqTm0.symm e0) h2) (EqTm0.trans (EqTm0.symm e1) h3)
    exact EqTm0.plam h0 (.plam h0 h1 h2 h3) h' e
  | .papp h0 h1 => EqTm0.papp (beta_replace h0) h1 h1 (fun _ => rfl)
  | .ipi h0 h1 => EqTm0.refl (.ipi h0 h1)
  | .ilam h0 h1 => EqTm0.ilam h0 (beta_replace h1)
  | .iapp h0 h1 => EqTm0.iapp (beta_replace h0) h1 h1 (fun _ => rfl)
  | .split h0 h1 h2 h3 h4 h5 h6 => EqTm0.refl (.split h0 h1 h2 h3 h4 h5 h6)
  | .abort h0 h1 => EqTm0.refl (.abort h0 h1)
  | .transp h0 h1 h2 h3 => EqTm0.refl (.transp h0 h1 h2 h3)
  | .hcomp h0 h1 h2 h3 h4 => EqTm0.refl (.hcomp h0 h1 h2 h3 h4)
  | .glue h0 h1 h2 h3 => EqTm0.refl (.glue h0 h1 h2 h3)
  | .glueEl h0 h1 h2 h3 h4 => EqTm0.refl (.glueEl h0 h1 h2 h3 h4)
  | .unglue h0 h1 h2 h3 => EqTm0.refl (.unglue h0 h1 h2 h3)
  | .data h0 h1 h2 => EqTm0.refl (.data h0 h1 h2)
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => EqTm0.refl (.con h0 h1 h2 h3 h4 h5 h6 h7)
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => EqTm0.refl (.elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)

end

/-- Replacement in the spec's judgments, for a well-formed signature. -/
theorem HasTy.beta_replace (hS : WfSig S) {Ψ Φ Γ t T} (h : HasTy S Ψ Φ Γ t T) :
    EqTm S Ψ Φ Γ t t.betaIn T :=
  minimal_to_spec_eq (Meta.beta_replace (sigClosed_of_wfSig hS)
    (presup0 (sigClosed_of_wfSig hS) (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2)
    (spec_to_minimal hS h))

theorem gen_unglue {Ψ Φ Γ s T0} (h : HasTy0 S Ψ Φ Γ s T0) {φ e g} (hs : s = .unglue φ e g) :
    ∃ A T l, (HasTy0 S Ψ Φ Γ (glue A φ T e) (univ l) ∧ HasTy0 S Ψ Φ Γ A (univ l) ∧
      HasTy0 S Ψ (cof Φ φ) Γ e (equiv T A) ∧ HasTy0 S Ψ Φ Γ g (glue A φ T e)) ∧ TyChainC S Ψ Φ Γ A T0 :=
  match h with
  | .var _ _ => by cases hs
  | .conv h0 h1 => by
    obtain ⟨A, T, l, x, ch⟩ := gen_unglue h0 hs
    exact ⟨A, T, l, x, ch.snoc h1⟩
  | .restrict hsc he h2 => by
    obtain ⟨A, T, l, ⟨h0, h1, h2', h3⟩, ch⟩ := gen_unglue h2 hs
    have hφ := scoped_cof_right (scoped_of_ty h2')
    have hs' : (cof _ φ).Scoped Ψ := ⟨hsc, hφ⟩
    exact ⟨A, T, l, ⟨HasTy0.restrict hsc he h0, HasTy0.restrict hsc he h1,
      HasTy0.restrict hs' (ent_and_mono he (ent_refl _)) h2', HasTy0.restrict hsc he h3⟩, ch.restrict hsc he⟩
  | .const _ _ => by cases hs
  | .univ _ _ => by cases hs
  | .cumul h0 h1 => by
    obtain ⟨A, T, l, x, ch⟩ := gen_unglue h1 hs
    exact ⟨A, T, l, x, ch.cumul h0⟩
  | .pi _ _ => by cases hs
  | .lam _ _ => by cases hs
  | .app _ _ => by cases hs
  | .sigma _ _ => by cases hs
  | .pair _ _ _ => by cases hs
  | .fst _ => by cases hs
  | .snd _ => by cases hs
  | .path _ _ _ => by cases hs
  | .plam _ _ _ _ => by cases hs
  | .papp _ _ => by cases hs
  | .ipi _ _ => by cases hs
  | .ilam _ _ => by cases hs
  | .iapp _ _ => by cases hs
  | .split _ _ _ _ _ _ _ => by cases hs
  | .abort _ _ => by cases hs
  | .transp _ _ _ _ => by cases hs
  | .hcomp _ _ _ _ _ => by cases hs
  | .glue _ _ _ _ => by cases hs
  | .glueEl _ _ _ _ _ => by cases hs
  | .unglue h0 h1 h2 h3 => by cases hs; exact ⟨_, _, _, ⟨h0, h1, h2, h3⟩, .refl _⟩
  | .data _ _ _ => by cases hs
  | .con _ _ _ _ _ _ _ _ => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases hs

section
variable (hP : Presup0 S)
include hP

/-- Replacement under `unglue`: a system argument one of whose faces holds is its branch. -/
theorem unglue_split {Ψ Φ Γ T0 φ e φ1 t ψ1 u g'}
    (h : HasTy0 S Ψ Φ Γ (unglue φ e (split φ1 t ψ1 u)) T0)
    (hb : (I.Entails Φ φ1 ∧ g' = t) ∨ (I.Entails Φ ψ1 ∧ g' = u)) :
    EqTm0 S Ψ Φ Γ (unglue φ e (split φ1 t ψ1 u)) (unglue φ e g') T0 := by
  obtain ⟨A, T, l, ⟨hG, hA, he, hg⟩, ch⟩ := gen_unglue h rfl
  have e1 : EqTm0 S Ψ Φ Γ (split φ1 t ψ1 u) g' (glue A φ T e) := by
    rcases hb with ⟨hent, rfl⟩ | ⟨hent, rfl⟩
    · exact EqTm0.splitL hent hg
    · exact EqTm0.splitR hent hg
  have hu := HasTy0.unglue hG hA he hg
  have hu' := HasTy0.unglue hG hA he (hP e1).2
  exact ch.transportEq (EqTm0.unglue hu hu' (ent_refl _) (ent_refl _) (EqTm0.refl he) e1)

end

theorem HasTy.unglue_split (hS : WfSig S) {Ψ Φ Γ T0 φ e φ1 t ψ1 u g'}
    (h : HasTy S Ψ Φ Γ (unglue φ e (split φ1 t ψ1 u)) T0)
    (hb : (I.Entails Φ φ1 ∧ g' = t) ∨ (I.Entails Φ ψ1 ∧ g' = u)) :
    EqTm S Ψ Φ Γ (unglue φ e (split φ1 t ψ1 u)) (unglue φ e g') T0 :=
  minimal_to_spec_eq (Meta.unglue_split
    (presup0 (sigClosed_of_wfSig hS) (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2)
    (spec_to_minimal hS h) hb)

end KubusCore.Meta
