import Model.Whnf.Valid2CompSigma
import Model.Whnf.Valid2CompPi
import Model.Whnf.Valid2CompPath
import Model.Whnf.Valid2CompGlue
import Model.Whnf.Valid2LineEquiv
import Model.Whnf.Valid2TranspGlue
import Model.Whnf.Valid2Data
import Model.Whnf.Valid2Elim
import Model.Whnf.Valid2TranspCon
import Model.Whnf.Valid2HcompCon
import Model.Whnf.NearAll
import Model.Whnf.Valid2GlueBeta

/-!
# The binary fundamental lemma

Every derivation of the minimal judgments in a prefix `S'` of the signature `S` is valid in `S`
(`Valid2`, `VTele2`): related closing substitutions give related instances. By mutual structural
induction on the derivations, given the hypotheses of `Fund2Hyp.lean`. The premises of the rules that
the validity lemmas need beyond the rule's own premises (the agreement of a system's branches, a
composition's tube with its base, a transport's line with its constancy, the components of
Glue terms and types) come from inverting the typing derivations of the rule's subjects, within the
same induction (`fund2_split`, `fund2_hcompInv`, `fund2_transpInv`, `fund2_glueElInv`, `fund2_unglueInv`,
`fund2_glueTyInv`, `fund2_hcompGlueInv`, `fund2_transpGlueInv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S S' : Sig} {k : ℕ}

section
variable (hW : WfSig S) (hpre : ∀ (j : ℕ) (e : Entry), S'[j]? = some e → S[j]? = some e)
include hW hpre

/-- The two sides of an equation of `S'`, typed in `S`. -/
theorem pre2 {Ψ Φ Γ t u A} (h : EqTm0 S' Ψ Φ Γ t u A) : HasTy0 S Ψ Φ Γ t A ∧ HasTy0 S Ψ Φ Γ u A :=
  presup hW (sigwk_eq hpre h)

end

section
variable (hW : WfSig S) (hpre : ∀ (j : ℕ) (e : Entry), S'[j]? = some e → S[j]? = some e)
  (hD : DefHyp2 S S') (hK : KanOracle2 S) (hDa : DataHyp2 S S') (hN : NearEl2 S)
  (hDe : DeclHyp2 S S'.length)
include hW hpre hD hK hDa hN hDe

mutual

theorem fund2_ty {Ψ Φ Γ t A} (hd : HasTy0 S' Ψ Φ Γ t A) :
    Valid2 S Ψ Φ Γ t t A :=
  match hd with
  | .var _ h1 => valid_var hW h1
  | .conv h0 h1 => valid_conv hW (fund2_ty h0) (fund2_eq h1)
  | .restrict _ h1 h2 => valid_restrict hW h1 (fund2_ty h2)
  | .const h0 h1 => valid_const hW (hpre _ _ h1) (hD _ _ _ h1) (sigwk_ty hpre (.const h0 h1))
  | .univ h0 _ => valid_univ hW h0
  | .cumul h0 h1 => valid_cumul hW h0 (fund2_ty h1)
  | .pi h0 h1 => by
    have h := sigwk_ty hpre (.pi h0 h1)
    exact valid_pi hW (fund2_ty h0) (fund2_ty h1) h h (.refl h)
  | .lam h0 h1 => by
    have h := sigwk_ty hpre (.lam h0 h1)
    exact valid_lam hW (fund2_ty h0) (fund2_ty h1) h h (.refl h)
  | .app h0 h1 => valid_app hW (fund2_ty h0) (fund2_ty h1)
  | .sigma h0 h1 => by
    have h := sigwk_ty hpre (.sigma h0 h1)
    exact valid_sigma hW (fund2_ty h0) (fund2_ty h1) h h (.refl h)
  | .pair h0 h1 h2 => by
    have h := sigwk_ty hpre (.pair h0 h1 h2)
    exact valid_pair hW (fund2_ty h0) (fund2_ty h1) (fund2_ty h2) h h (.refl h)
  | .fst h0 => valid_fst hW (fund2_ty h0)
  | .snd h0 => valid_snd hW (fund2_ty h0)
  | .path h0 h1 h2 => by
    have h := sigwk_ty hpre (.path h0 h1 h2)
    exact valid_path hW (fund2_ty h0) (fund2_ty h1) (fund2_ty h2) h h (.refl h)
  | .plam h0 h1 h2 h3 =>
    valid_plam hW (fund2_ty h0) (fund2_ty h1) (fund2_eq h2) (fund2_eq h3) (sigwk_ty hpre (.plam h0 h1 h2 h3))
  | .papp h0 h1 => valid_papp hW (fund2_ty h0) h1 h1 (I_eq_refl _)
  | .ipi h0 h1 => by
    have h := sigwk_ty hpre (.ipi h0 h1)
    exact valid_ipi hW (fund2_ty h1) h h (.refl h)
  | .ilam h0 h1 => by
    have h := sigwk_ty hpre (.ilam h0 h1)
    exact valid_ilam hW (fund2_ty h0) (fund2_ty h1) h h (.refl h)
  | .iapp h0 h1 => valid_iapp hW (fund2_ty h0) h1 h1 (I_eq_refl _)
  | .split h0 h1 h2 h3 h4 h5 h6 => by
    have h := sigwk_ty hpre (.split h0 h1 h2 h3 h4 h5 h6)
    exact valid_split hW h0 h1 h2 (fund2_ty h4) (fund2_ty h5) (fund2_eq h6) h h
  | .abort h0 _ => valid_absurd h0
  | .transp h0 h1 h2 h3 => by
    have h := sigwk_ty hpre (.transp h0 h1 h2 h3)
    have hA := fund2_ty h0
    exact valid_transp hW h1 (ent_refl _) (ent_refl _) hA (fund2_eq h2) (fund2_ty h3) h h (.refl h)
      fun k c => hK.transp k _ _ (hA.ty hW (c.up hW))
  | .hcomp h0 h1 h2 h3 h4 => by
    have h := sigwk_ty hpre (.hcomp h0 h1 h2 h3 h4)
    have hA := fund2_ty h0
    exact valid_hcomp hW h1 (ent_refl _) (ent_refl _) hA (fund2_ty h2) (fund2_ty h3) (fund2_eq h4) (fund2_eq h4)
      h h (.refl h) (.refl (sigwk_ty hpre h2)) fun k c => hK.hcomp k _ _ (hA.ty hW c)
  | .glue h0 h1 h2 h3 => valid_glue hW h1 (fund2_ty h0) (fund2_ty h2) (fund2_ty h3) (sigwk_ty hpre (.glue h0 h1 h2 h3))
  | .glueEl h0 h1 h2 h3 h4 => by
    obtain ⟨_, ⟨-, hφ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h0) rfl
    exact valid_glueEl hW hφ (fund2_ty h0) (sigwk_ty hpre h1) (fund2_ty h2) (fund2_ty h3) (fund2_eq h4)
      (sigwk_ty hpre (.glueEl h0 h1 h2 h3 h4))
  | .unglue h0 h1 h2 h3 => by
    obtain ⟨_, ⟨-, hφ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h0) rfl
    exact valid_unglue hW hφ (fund2_ty h1) (sigwk_ty hpre h2) (fund2_ty h2) (fund2_ty h3)
      (sigwk_ty hpre (.unglue h0 h1 h2 h3))
  | .data h0 h1 h2 => by
    have a2 := fund2_tele h2
    have hd := (List.getElem?_eq_some_iff.1 h0).1
    exact valid_data hW (hpre _ _ h0) (hDe.mono (by omega)) h1 (sigwk_tele hpre h2) a2
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => by
    have a3 := fund2_ty h3; have a4 := fund2_tele h4; have a5 := fund2_tele h5
    rename_i D _ _ _ _ _
    cases hH : D.isHIT
    · have hd := (List.getElem?_eq_some_iff.1 h0).1
      exact valid_con_nonHIT hW (hpre _ _ h0) (hDe.mono (by omega)) hH h1 h2 (sigwk_ty hpre (.con h0 h1 h2 h3 h4 h5 h6 h7))
        (.refl (sigwk_ty hpre (.con h0 h1 h2 h3 h4 h5 h6 h7))) (by simpa using Meta.tele_length h4) (tele_isList h5)
        (tele_isList h5) (by simpa [Ctor.argTys] using Meta.tele_length h5)
        (by simpa [Ctor.argTys] using Meta.tele_length h5) h6 h6 a3 a5
    · exact hDa.con h0 hH h1 h2 (sigwk_ty hpre h3) (sigwk_tele hpre h4) (sigwk_tele hpre h5) h6 h7 a3 a4 a5
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    rename_i D _ _ _ _ _
    cases hH : D.isHIT
    · have hty := sigwk_ty hpre (.elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
      exact valid_elim hW (hpre _ _ h0) hH hty hty (fund2_ty h2) (fund2_ty h4)
        (fun c C b b' hC hb hb' => by rw [hb] at hb'; cases hb'; exact fund2_ty (h7 c C b hC hb)) (fund2_ty h9)
    exact hDa.elim h0 hH h1 (sigwk_ty hpre h2) (sigwk_tele hpre h3) (sigwk_ty hpre h4) h5 h6
      (fun c C b hC hb => sigwk_ty hpre (h7 c C b hC hb))
      (fun c C b k ψ e hC hb hk => sigwk_eq hpre (h8 c C b k ψ e hC hb hk)) (sigwk_ty hpre h9)
      (fund2_ty h2) (fund2_tele h3) (fund2_ty h4) (fun c C b hC hb => fund2_ty (h7 c C b hC hb))
      (fun c C b k ψ e hC hb hk => fund2_eq (h8 c C b k ψ e hC hb hk)) (fund2_ty h9)
termination_by structural hd


theorem fund2_tele {Ψ Φ Γ ts Δ prev} (hd : HasTele0 S' Ψ Φ Γ ts Δ prev) :
    VTele2 S Ψ Φ Γ ts ts Δ prev :=
  match hd with
  | .nil _ => trivial
  | .cons h0 h1 => ⟨fund2_ty h0, fund2_tele h1⟩
termination_by structural hd


theorem fund2_eqtele {Ψ Φ Γ ts ts' Δ prev} (hd : EqTele0 S' Ψ Φ Γ ts ts' Δ prev) :
    VTele2 S Ψ Φ Γ ts ts' Δ prev :=
  match hd with
  | .nil _ => trivial
  | .cons h0 h1 => ⟨fund2_eq h0, fund2_eqtele h1⟩
  | .dataInj h0 h1 h2 h3 =>
    valid_dataInj hW (hpre _ _ h0) (sigwk_tele hpre h1) (sigwk_tele hpre h2) (sigwk_eq hpre h3) (fund2_tele h1)
      (fund2_eq h3)
termination_by structural hd


theorem fund2_split {Ψ Φ Γ s T} (hd : HasTy0 S' Ψ Φ Γ s T) :
    ∀ {φ t ψ u}, s = .split φ t ψ u →
    SplitInv S Ψ Φ Γ φ t ψ u T :=
  match hd with
  | .split h0 h1 h2 _ h4 h5 h6 => fun hs => by
    have a := fund2_ty h4; have b := fund2_ty h5; have c := fund2_eq h6
    cases hs; exact ⟨h0, h1, h2, a, b, c⟩
  | .conv h0 h1 => fun hs => (fund2_split h0 hs).conv hW (fund2_eq h1)
  | .restrict _ h1 h2 => fun hs => (fund2_split h2 hs).restrict hW h1
  | .cumul h0 h1 => fun hs => (fund2_split h1 hs).cumul hW h0
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_hcompInv {Ψ Φ Γ s T} (hd : HasTy0 S' Ψ Φ Γ s T) :
    ∀ {A φ u a}, s = .hcomp A φ u a → HcompInv S Ψ Φ Γ A φ u a T :=
  match hd with
  | .hcomp h0 h1 h2 h3 h4 => fun hs => by
    have a0 := fund2_ty h0; have a2 := fund2_ty h2; have a3 := fund2_ty h3; have a4 := fund2_eq h4
    cases hs; exact ⟨_, h1, a0, a2, a3, a4, ElTr2.refl _, sigwk_ty hpre h0, sigwk_ty hpre h2, sigwk_ty hpre h3,
      sigwk_eq hpre h4⟩
  | .conv h0 h1 => fun hs => (fund2_hcompInv h0 hs).conv hW (fund2_eq h1)
  | .restrict h0 h1 h2 => fun hs => (fund2_hcompInv h2 hs).restrict hW h0 h1
  | .cumul h0 h1 => fun hs => (fund2_hcompInv h1 hs).cumul hW h0
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_transpInv {Ψ Φ Γ s T} (hd : HasTy0 S' Ψ Φ Γ s T) :
    ∀ {A φ a}, s = .transp A φ a → TranspInv S Ψ Φ Γ A φ a T :=
  match hd with
  | .transp h0 h1 h2 h3 => fun hs => by
    have a0 := fund2_ty h0; have a2 := fund2_eq h2; have a3 := fund2_ty h3
    cases hs; exact ⟨_, h1, a0, a2, a3, ElTr2.refl _, sigwk_ty hpre h0, sigwk_eq hpre h2, sigwk_ty hpre h3⟩
  | .conv h0 h1 => fun hs => (fund2_transpInv h0 hs).conv hW (fund2_eq h1)
  | .restrict h0 h1 h2 => fun hs => (fund2_transpInv h2 hs).restrict hW h0 h1
  | .cumul h0 h1 => fun hs => (fund2_transpInv h1 hs).cumul hW h0
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_glueElInv {Ψ Φ Γ s G} (hd : HasTy0 S' Ψ Φ Γ s G) :
    ∀ {φ e t a}, s = .glueEl φ e t a →
    GlueElInv S Ψ Φ Γ φ e t a G :=
  match hd with
  | .glueEl h0 h1 h2 h3 h4 => fun hs => by
    have a1 := fund2_ty h1; have a2 := fund2_ty h2; have a3 := fund2_ty h3; have a4 := fund2_eq h4
    cases hs
    obtain ⟨_, ⟨-, hφ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h0) rfl
    exact ⟨_, _, _, hφ, sigwk_ty hpre (.glueEl h0 h1 h2 h3 h4), sigwk_ty hpre h0, sigwk_ty hpre h1, a1,
      a2, a3, a4, ElTr2.refl _⟩
  | .conv h0 h1 => fun hs => (fund2_glueElInv h0 hs).conv hW (fund2_eq h1)
  | .restrict h0 h1 h2 => fun hs => (fund2_glueElInv h2 hs).restrict hW h0 h1
  | .cumul h0 h1 => fun hs => (fund2_glueElInv h1 hs).cumul hW h0
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_unglueInv {Ψ Φ Γ s G} (hd : HasTy0 S' Ψ Φ Γ s G) :
    ∀ {φ e g}, s = .unglue φ e g →
    UnglueInv S Ψ Φ Γ φ e g G :=
  match hd with
  | .unglue h0 h1 h2 h3 => fun hs => by
    have a2 := fund2_ty h2; have a1 := fund2_ty h1
    have a3 : ∀ {φ' e' t a}, _ = Tm.glueEl φ' e' t a → _ := fun hg => fund2_glueElInv h3 hg
    cases hs
    obtain ⟨_, ⟨-, hφ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h0) rfl
    exact ⟨_, _, _, hφ, sigwk_ty hpre h0, sigwk_ty hpre h1, sigwk_ty hpre h2, a2, a1,
      ElTr2.refl _, sigwk_ty hpre h3, .refl _, fun t a hg => a3 hg⟩
  | .conv h0 h1 => fun hs => (fund2_unglueInv h0 hs).conv hW (fund2_eq h1) (sigwk_eq hpre h1)
  | .restrict h0 h1 h2 => fun hs => (fund2_unglueInv h2 hs).restrict hW h0 h1
  | .cumul h0 h1 => fun hs => (fund2_unglueInv h1 hs).cumul hW h0
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_glueTyInv {Ψ Φ Γ s G} (hd : HasTy0 S' Ψ Φ Γ s G) :
    ∀ {A φ T e}, s = .glue A φ T e → GlueTyInv S Ψ Φ Γ A φ T e :=
  match hd with
  | .glue h0 h1 h2 h3 => fun hs => by
    have a0 := fund2_ty h0; have a2 := fund2_ty h2; have a3 := fund2_ty h3
    cases hs
    exact ⟨_, h1, a0, a2, a3, sigwk_ty hpre h0, sigwk_ty hpre h2, sigwk_ty hpre h3⟩
  | .conv h0 _ => fun hs => fund2_glueTyInv h0 hs
  | .restrict h0 h1 h2 => fun hs => (fund2_glueTyInv h2 hs).restrict hW h0 h1
  | .cumul _ h1 => fun hs => fund2_glueTyInv h1 hs
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_hcompGlueInv {Ψ Φ Γ s G} (hd : HasTy0 S' Ψ Φ Γ s G) :
    ∀ {A φ T e ψ u a}, s = .hcomp (.glue A φ T e) ψ u a → GlueTyInv S Ψ Φ Γ A φ T e :=
  match hd with
  | .hcomp h0 _ _ _ _ => fun hs => by
    have a0 : ∀ {A φ T e}, _ = Tm.glue A φ T e → _ := fun hg => fund2_glueTyInv h0 hg
    cases hs; exact a0 rfl
  | .conv h0 _ => fun hs => fund2_hcompGlueInv h0 hs
  | .restrict h0 h1 h2 => fun hs => (fund2_hcompGlueInv h2 hs).restrict hW h0 h1
  | .cumul _ h1 => fun hs => fund2_hcompGlueInv h1 hs
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .transp _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_transpGlueInv {Ψ Φ Γ s G} (hd : HasTy0 S' Ψ Φ Γ s G) :
    ∀ {A φ T e ψ a}, s = .transp (.glue A φ T e) ψ a → GlueTyInv S (Ψ + 1) Φ.shift Γ.dshift A φ T e :=
  match hd with
  | .transp h0 _ _ _ => fun hs => by
    have a0 : ∀ {A φ T e}, _ = Tm.glue A φ T e → _ := fun hg => fund2_glueTyInv h0 hg
    cases hs; exact a0 rfl
  | .conv h0 _ => fun hs => fund2_transpGlueInv h0 hs
  | .restrict h0 h1 h2 => fun hs =>
    (fund2_transpGlueInv h2 hs).restrict hW (KubusCore.I.scoped_shift h0) (ent_shift h1)
  | .cumul _ h1 => fun hs => fund2_transpGlueInv h1 hs
  | .var _ _ => fun hs => by cases hs
  | .const _ _ => fun hs => by cases hs
  | .univ _ _ => fun hs => by cases hs
  | .pi _ _ => fun hs => by cases hs
  | .lam _ _ => fun hs => by cases hs
  | .app _ _ => fun hs => by cases hs
  | .sigma _ _ => fun hs => by cases hs
  | .pair _ _ _ => fun hs => by cases hs
  | .fst _ => fun hs => by cases hs
  | .snd _ => fun hs => by cases hs
  | .path _ _ _ => fun hs => by cases hs
  | .plam _ _ _ _ => fun hs => by cases hs
  | .papp _ _ => fun hs => by cases hs
  | .ipi _ _ => fun hs => by cases hs
  | .ilam _ _ => fun hs => by cases hs
  | .iapp _ _ => fun hs => by cases hs
  | .split _ _ _ _ _ _ _ => fun hs => by cases hs
  | .abort _ _ => fun hs => by cases hs
  | .hcomp _ _ _ _ _ => fun hs => by cases hs
  | .glue _ _ _ _ => fun hs => by cases hs
  | .glueEl _ _ _ _ _ => fun hs => by cases hs
  | .data _ _ _ => fun hs => by cases hs
  | .con _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => fun hs => by cases hs
  | .unglue _ _ _ _ => fun hs => by cases hs
termination_by structural hd


theorem fund2_eq {Ψ Φ Γ t u A} (hd : EqTm0 S' Ψ Φ Γ t u A) :
    Valid2 S Ψ Φ Γ t u A :=
  match hd with
  | .refl h0 => fund2_ty h0
  | .symm h0 => valid_symm hW (fund2_eq h0)
  | .trans h0 h1 => valid_trans hW (fund2_eq h0) (fund2_eq h1)
  | .conv h0 h1 => valid_conv hW (fund2_eq h0) (fund2_eq h1)
  | .restrict _ h1 h2 => valid_restrict hW h1 (fund2_eq h2)
  | .cumul h0 h1 => valid_cumul hW h0 (fund2_eq h1)
  | .delta h0 h1 => valid_delta hW (hpre _ _ h1) (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.delta h0 h1)).2
  | .absurd h0 _ _ => valid_absurd h0
  | .local h0 h1 h2 _ _ h5 h6 => valid_local h0 h1 h2 (fund2_eq h5) (fund2_eq h6)
  | .face h0 h1 _ h3 => valid_face hW h0 h1 (fund2_ty h3)
  | .faceU h0 h1 h2 => valid_face hW h0 h1 (fund2_ty h2)
  | .pi h0 h1 => by
    have p := pre2 hW hpre (.pi h0 h1)
    exact valid_pi hW (fund2_eq h0) (fund2_eq h1) p.1 p.2 (sigwk_eq hpre (.pi h0 h1))
  | .lam h0 h1 => by
    have p := pre2 hW hpre (.lam h0 h1)
    exact valid_lam hW (fund2_ty h0) (fund2_eq h1) p.1 p.2 (sigwk_eq hpre (.lam h0 h1))
  | .app h0 h1 => valid_app hW (fund2_eq h0) (fund2_eq h1)
  | .sigma h0 h1 => by
    have p := pre2 hW hpre (.sigma h0 h1)
    exact valid_sigma hW (fund2_eq h0) (fund2_eq h1) p.1 p.2 (sigwk_eq hpre (.sigma h0 h1))
  | .pair h0 h1 h2 => by
    have p := pre2 hW hpre (.pair h0 h1 h2)
    exact valid_pair hW (fund2_ty h0) (fund2_eq h1) (fund2_eq h2) p.1 p.2 (sigwk_eq hpre (.pair h0 h1 h2))
  | .fst h0 => valid_fst hW (fund2_eq h0)
  | .snd h0 => valid_snd hW (fund2_eq h0)
  | .path h0 h1 h2 => by
    have p := pre2 hW hpre (.path h0 h1 h2)
    exact valid_path hW (fund2_eq h0) (fund2_eq h1) (fund2_eq h2) p.1 p.2 (sigwk_eq hpre (.path h0 h1 h2))
  | .plam h0 h1 h2 h3 =>
    valid_plam_eq hW (fund2_ty h0) (fund2_ty h1) (fund2_eq h3) (sigwk_ty hpre h1) (sigwk_ty hpre h2)
      (sigwk_eq hpre (.plam h0 h1 h2 h3))
  | .papp h0 h1 h2 h3 => valid_papp hW (fund2_eq h0) h1 h2 h3
  | .split h0 h1 h2 h3 => by
    have i0 := fund2_split h0 rfl
    have i1 := fund2_split h1 rfl
    exact valid_split hW i0.1 i0.2.1 i0.2.2.1 (fund2_eq h2) (fund2_eq h3) i1.2.2.2.2.2 (sigwk_ty hpre h0)
      (sigwk_ty hpre h1)
  | .transp h0 h1 h2 h3 h4 h5 => by
    obtain ⟨_, hφ, -, hC, -⟩ := fund2_transpInv h0 rfl
    have hA := fund2_eq h2
    exact valid_transp hW hφ h3 h4 hA hC (fund2_eq h5) (sigwk_ty hpre h0) (sigwk_ty hpre h1)
      (sigwk_eq hpre (.transp h0 h1 h2 h3 h4 h5)) fun k c => hK.transp k _ _ (hA.ty hW (c.up hW))
  | .hcomp h0 h1 h2 h3 h4 h5 h6 => by
    obtain ⟨_, hφ, -, -, -, hu0, -⟩ := fund2_hcompInv h0 rfl
    obtain ⟨_, -, -, -, -, hu0', -⟩ := fund2_hcompInv h1 rfl
    have hA := fund2_eq h2
    have hu0'' := valid_conv hW (valid_restrict hW (ent_and_mono (ent_refl _) h3) hu0')
      (valid_restrict hW (ent_and_left _ _) (valid_symm hW hA))
    exact valid_hcomp hW hφ h3 h4 hA (fund2_eq h5) (fund2_eq h6) hu0 hu0'' (sigwk_ty hpre h0) (sigwk_ty hpre h1)
      (sigwk_eq hpre (.hcomp h0 h1 h2 h3 h4 h5 h6)) (sigwk_eq hpre h5) fun k c => hK.hcomp k _ _ (hA.ty hW c)
  | .glue h0 h1 h2 h3 h4 h5 h6 => by
    obtain ⟨_, ⟨-, hφ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h0) rfl
    obtain ⟨_, ⟨-, hφ', -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (sigwk_ty hpre h1) rfl
    exact valid_glue_eq hW hφ hφ' h3 h4 (fund2_eq h2) (fund2_eq h5) (fund2_eq h6) (fund2_ty h1) (sigwk_ty hpre h0)
      (sigwk_ty hpre h1) (sigwk_eq hpre (.glue h0 h1 h2 h3 h4 h5 h6))
  | .glueEl h0 h1 h2 h3 h4 h5 h6 => by
    have g0 := fund2_ty h0
    obtain ⟨l, hGt, hφ, -⟩ := glue_ty_of_el hW (sigwk_ty hpre h0)
    exact valid_glueEl_eq hW hφ h2 h3 (valid_ty_of hW g0 hGt) (sigwk_eq hpre h4) (fund2_eq h5) (fund2_eq h6) g0
      (fund2_ty h1) (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre (.glueEl h0 h1 h2 h3 h4 h5 h6))
  | .unglue h0 h1 h2 h3 h4 h5 => by
    obtain ⟨_, -, hφ, -⟩ := glue_ty_of_el hW (pre2 hW hpre h5).1
    have hc := closed_ty (sigwk_ty hpre h1)
    simp only [Tm.closedB, Bool.and_eq_true] at hc
    exact valid_unglue_eq hW hφ ((I.scopedB_iff _ _).1 hc.1.1) h2 h3 (fund2_ty h0) (sigwk_eq hpre h4) (fund2_eq h4)
      (fund2_eq h5) (sigwk_ty hpre h0) (sigwk_ty hpre h1) (sigwk_eq hpre (.unglue h0 h1 h2 h3 h4 h5))
  | .ipi h0 h1 => by
    have p := pre2 hW hpre (.ipi h0 h1)
    exact valid_ipi hW (fund2_eq h1) p.1 p.2 (sigwk_eq hpre (.ipi h0 h1))
  | .ilam h0 h1 => by
    have p := pre2 hW hpre (.ilam h0 h1)
    exact valid_ilam hW (fund2_ty h0) (fund2_eq h1) p.1 p.2 (sigwk_eq hpre (.ilam h0 h1))
  | .iapp h0 h1 h2 h3 => valid_iapp hW (fund2_eq h0) h1 h2 h3
  | .piInjDom h0 => by
    have p := pre2 hW hpre (.piInjDom h0)
    exact valid_piInjDom hW (fund2_eq h0) p.1 p.2 (sigwk_eq hpre (.piInjDom h0))
  | .piInjCod h0 h1 => by
    have p := pre2 hW hpre (.piInjCod h0 h1)
    exact valid_piInjCod hW (fund2_eq h0) (fund2_ty h1) p.1 p.2 (sigwk_eq hpre (.piInjCod h0 h1))
  | .sigmaInjDom h0 => by
    have p := pre2 hW hpre (.sigmaInjDom h0)
    exact valid_sigmaInjDom hW (fund2_eq h0) p.1 p.2 (sigwk_eq hpre (.sigmaInjDom h0))
  | .sigmaInjCod h0 h1 => by
    have p := pre2 hW hpre (.sigmaInjCod h0 h1)
    exact valid_sigmaInjCod hW (fund2_eq h0) (fund2_ty h1) p.1 p.2 (sigwk_eq hpre (.sigmaInjCod h0 h1))
  | .pathInjLine h0 h1 => by
    have p := pre2 hW hpre (.pathInjLine h0 h1)
    exact valid_pathInjLine hW (fund2_eq h0) h1 p.1 p.2 (sigwk_eq hpre (.pathInjLine h0 h1))
  | .pathInjLeft h0 => valid_pathInjLeft hW (fund2_eq h0)
  | .pathInjRight h0 => valid_pathInjRight hW (fund2_eq h0)
  | .ipiInj h0 h1 => by
    have p := pre2 hW hpre (.ipiInj h0 h1)
    exact valid_ipiInj hW (fund2_eq h0) h1 p.1 p.2 (sigwk_eq hpre (.ipiInj h0 h1))
  | .dataInjAt h0 h1 h2 h3 h4 h5 h6 h7 h8 =>
    valid_dataInjAt hW (hpre _ _ h0) h1 h2 (sigwk_eq hpre h3) h4 h5 h6
      (fun kk hk => by subst hk; exact sigwk_eq hpre (.dataInjAt h0 h1 h2 h3 h4 h5 h6 h7 h8)) (fund2_eq h3) (fund2_ty h7)
  | .noConf h0 h1 _ _ => valid_noConf hW h0 (fund2_eq h1)
  | .piBeta h0 => valid_piBeta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.piBeta h0)).2
  | .piEta h0 => valid_piEta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.piEta h0)).2
      (sigwk_eq hpre (.piEta h0))
  | .fstBeta h0 => valid_fstBeta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.fstBeta h0)).2
  | .sndBeta h0 => valid_sndBeta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.sndBeta h0)).2
  | .sigmaEta h0 => valid_sigmaEta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.sigmaEta h0)).2
      (sigwk_eq hpre (.sigmaEta h0))
  | .pathBeta h0 => valid_pathBeta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.pathBeta h0)).2
  | .pathEta h0 => valid_pathEta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.pathEta h0)).2
      (sigwk_eq hpre (.pathEta h0))
  | .ipiEta h0 => valid_ipiEta hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.ipiEta h0)).2
      (sigwk_eq hpre (.ipiEta h0))
  | .pathZero h0 => valid_pathZero hW (fund2_ty h0)
  | .pathOne h0 => valid_pathOne hW (fund2_ty h0)
  | .splitL h0 h1 => valid_splitL hW h0 (fund2_ty h1) (sigwk_ty hpre h1) (pre2 hW hpre (.splitL h0 h1)).2
  | .splitR h0 h1 => by
    have i := fund2_split h1 rfl
    exact valid_splitR hW i.1 i.2.1 h0 i.2.2.2.2.1 i.2.2.2.2.2 (sigwk_ty hpre h1) (pre2 hW hpre (.splitR h0 h1)).2
  | .transpFace h0 h1 => valid_transpFace hW h0 (fund2_ty h1) (sigwk_ty hpre h1) (pre2 hW hpre (.transpFace h0 h1)).2
  | .hcompFace h0 h1 => valid_hcompFace hW h0 (fund2_ty h1) (sigwk_ty hpre h1) (pre2 hW hpre (.hcompFace h0 h1)).2
  | .transpU h0 => valid_transpU hW (fund2_ty h0) (sigwk_ty hpre h0) (pre2 hW hpre (.transpU h0)).2
  | .transpPi h0 => valid_transpPi_rule hW hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_transpInv h0 rfl)
  | .transpSigma h0 => valid_transpSigma_rule hW hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_transpInv h0 rfl)
  | .transpPath h0 =>
    valid_transpPath_rule hW hK.hcomp hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_transpInv h0 rfl)
  | .transpGlue h0 _ _ h3 h4 h5 =>
    valid_transpGlue_rule hW hK.hcomp hK.transp hN (sigwk_ty hpre h0) (fund2_ty h0) (fund2_transpInv h0 rfl)
      (fund2_transpGlueInv h0 rfl) h3 h4 h5
  | .transpIPi h0 => valid_transpIPi_rule hW hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_transpInv h0 rfl)
  | .hcompIPi h0 => valid_hcompIPi_rule hW hK.hcomp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl)
  | .hcompPi h0 => valid_hcompPi_rule hW hK.hcomp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl)
  | .hcompSigma h0 =>
    valid_hcompSigma_rule hW hK.hcomp hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl)
  | .hcompPath h0 =>
    valid_hcompPath_rule hW hK.hcomp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl)
  | .hcompGlue h0 _ _ =>
    valid_hcompGlue_rule hW hK.hcomp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl) (fund2_hcompGlueInv h0 rfl)
  | .hcompU h0 =>
    valid_hcompU_rule hW hK.transp (sigwk_ty hpre h0) (fund2_ty h0) (fund2_hcompInv h0 rfl)
  | .glueFace h0 h1 => valid_glueFace hW h0 (fund2_ty h1) (sigwk_ty hpre h1) (pre2 hW hpre (.glueFace h0 h1)).2
  | .glueElFace h0 h1 =>
    valid_glueElFace hW h0 (fund2_ty h1) (sigwk_ty hpre h1) (pre2 hW hpre (.glueElFace h0 h1)).2
  | .unglueFace h0 h1 h2 h3 => by
    have g1 := sigwk_ty hpre h1
    obtain ⟨_, -, hφ, -⟩ := glue_ty_of_el hW g1
    have p := pre2 hW hpre (.unglueFace h0 h1 h2 h3)
    have he0 := HasTy0.restrict (show I.Scoped Ψ (cof Φ _) from ⟨scoped_of_ty g1, hφ⟩) (ent_and_left _ _) (sigwk_ty hpre h3)
    exact valid_unglueFace hW h0 (valid_unglue hW hφ (fund2_ty h2) he0
      (valid_restrict hW (ent_and_left _ _) (fund2_ty h3)) (fund2_ty h1) p.1) p.1 g1 (sigwk_ty hpre h2)
      (sigwk_ty hpre h3) p.2
  | .glueBeta h0 h1 h2 => by
    obtain ⟨A, T, l, hφ, hG, hA, he0, he, hAv, htr, hgA, hch, hgl⟩ := fund2_unglueInv h0 rfl
    obtain ⟨A2, T2, l2, -, hg2, hG2, he2, hev2, htv, hav, hatv, htr2⟩ := hgl _ _ rfl
    exact valid_glueBeta2 hW hφ (sigwk_ty hpre h0) (fund2_ty h1) (sigwk_eq hpre h2) (fund2_eq h2) hA he0 he htr
      hgA hch hG2 htv htr2
  | .glueEta h0 => by
    have g0 := fund2_ty h0
    obtain ⟨l, hGt, hφ, he0⟩ := glue_ty_of_el hW (sigwk_ty hpre h0)
    exact valid_glueEta_ty hW hφ (valid_ty_of hW g0 hGt) he0 g0 (sigwk_ty hpre h0) (pre2 hW hpre (.glueEta h0)).2
  | .data h0 h1 h2 h3 => by
    have a3 := fund2_eqtele h3
    have hd := (List.getElem?_eq_some_iff.1 h0).1
    exact valid_dataEq hW (hpre _ _ h0) (hDe.mono (by omega)) (sigwk_ty hpre h1) (sigwk_ty hpre h2)
      (sigwk_eq hpre (.data h0 h1 h2 h3)) a3
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => by
    rename_i d D _ _ ps _ _ _ _ _
    cases hH : D.isHIT
    · have hD := hpre _ _ h0
      have hd := (List.getElem?_eq_some_iff.1 h0).1
      have hcon := sigwk_ty hpre h2
      have hcon' := sigwk_ty hpre h3
      obtain ⟨D1, C1, hD1, hC1, hpl, hpsl, -, hrs⟩ := gen_con hcon rfl
      obtain ⟨D2, C2, hD2, hC2, -, -, -, hrs'⟩ := gen_con hcon' rfl
      rw [hD] at hD1 hD2; cases hD1; cases hD2
      rw [h1] at hC1 hC2; cases hC1; cases hC2
      have va := fund2_eqtele h5
      obtain ⟨hal, hal', hall, hall'⟩ := VTele2.shape va
      simp only [Ctor.argTys, List.length_map, List.length_range] at hall hall'
      have hvd : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) := by
        rcases pre_ty (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 hcon with
          ⟨l, hl⟩ | ⟨l, he, -⟩
        · obtain ⟨D3, hD3, htele⟩ := gen_data_tele hl rfl
          rw [hD] at hD3; cases hD3
          exact valid_data hW hD (hDe.mono (by omega)) (hW.2 _ D hD).1 htele (VTele2.left hW (fund2_eqtele h4))
        · cases he
      exact valid_con_nonHIT hW hD (hDe.mono (by omega)) hH h1 hpl hcon (sigwk_eq hpre (.con h0 h1 h2 h3 h4 h5 h6 h7))
        hpsl hal hal' hall hall' hrs hrs' hvd va
    exact hDa.conEq h0 hH h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3) (sigwk_eqtele hpre h4) (sigwk_eqtele hpre h5) h6 h7
      (fund2_ty h2) (fund2_ty h3) (fund2_eqtele h4) (fund2_eqtele h5)
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    rename_i D _ _ _ _ _ _ _ _ _
    cases hH : D.isHIT
    · obtain ⟨D0, m0, hE0, -⟩ := gen_elimP h1 rfl
      obtain ⟨D1, m1, hE1, -⟩ := gen_elimP h2 rfl
      have e0 : D0 = D := by have := hE0.hD; rw [h0] at this; cases this; rfl
      have e1 : D1 = D := by have := hE1.hD; rw [h0] at this; cases this; rfl
      rw [e0] at hE0; rw [e1] at hE1
      have hd := (List.getElem?_eq_some_iff.1 h0).1
      have hps := valid_dataEq hW (hpre _ _ h0) (hDe.mono (by omega)) (sigwk_ty hpre hE0.hdata)
        (sigwk_ty hpre hE1.hdata) (sigwk_eq hpre (.data h0 hE0.hdata hE1.hdata h3)) (fund2_eqtele h3)
      exact valid_elim hW (hpre _ _ h0) hH (sigwk_ty hpre h1) (sigwk_ty hpre h2) hps (fund2_eq h4)
        (fun c C b b' hC hb hb' => fund2_eq (h8 c C b b' hC hb hb')) (fund2_eq h9)
    exact hDa.elimEq h0 hH (sigwk_ty hpre h1) (sigwk_ty hpre h2) (sigwk_eqtele hpre h3) (sigwk_eq hpre h4) h5 h6 h7
      (fun c C b b' hC hb hb' => sigwk_eq hpre (h8 c C b b' hC hb hb')) (sigwk_eq hpre h9)
      (fund2_ty h1) (fund2_ty h2) (fund2_eqtele h3) (fund2_eq h4)
      (fun c C b b' hC hb hb' => fund2_eq (h8 c C b b' hC hb hb')) (fund2_eq h9)
  | .conBnd h0 h1 h2 h3 h4 h5 h6 => by
    rename_i D _ C _ _ _ _ _ _
    cases hH : D.isHIT
    · simp only [DataDecl.isHIT, List.any_eq_false] at hH
      have := hH _ (List.mem_of_getElem? h1)
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at this
      have hb : C.bnd = [] := Classical.byContradiction fun hne => this (.inr hne)
      rw [hb] at h2; cases h2
    exact hDa.conBnd h0 hH h1 h2 h3 h4 h5 (sigwk_ty hpre h6) (pre2 hW hpre (.conBnd h0 h1 h2 h3 h4 h5 h6)).2 (fund2_ty h6)
  | .elimCon h0 h1 h2 h3 h4 h5 h6 h7 => by
    rename_i D _ _ _ _ _ _ _ _ _
    cases hH : D.isHIT
    · exact valid_elimCon hW (hpre _ _ h0) hH h1 h2 h4 h5 (sigwk_ty hpre h7)
        (pre2 hW hpre (.elimCon h0 h1 h2 h3 h4 h5 h6 h7)).2 (sigwk_eq hpre (.elimCon h0 h1 h2 h3 h4 h5 h6 h7))
        (fund2_ty h7)
    exact hDa.elimCon h0 hH h1 h2 h3 h4 h5 (sigwk_tele hpre h6) (sigwk_ty hpre h7)
      (pre2 hW hpre (.elimCon h0 h1 h2 h3 h4 h5 h6 h7)).2 (fund2_tele h6) (fund2_ty h7)
  | .elimHcomp h0 h1 h2 h3 =>
    hDa.elimHcomp h0 h1 (sigwk_ty hpre h2) (sigwk_ty hpre h3) (pre2 hW hpre (.elimHcomp h0 h1 h2 h3)).2
      (fund2_ty h2) (fund2_ty h3)
  | .hcompCon h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    valid_hcompCon hW (hpre _ _ h0) h1 hK h2 h3 h4 h5 (sigwk_tele hpre h6) (sigwk_tele hpre h7) (sigwk_eq hpre h8)
      (sigwk_eqtele hpre h9) (fund2_eq h8) (fund2_ty h10) (fund2_hcompInv h10 rfl)
  | .transpData0 h0 h1 h2 =>
    valid_transpData0 hW (hpre _ _ h0) h1 (pre2 hW hpre (.transpData0 h0 h1 h2)).2
      (sigwk_eq hpre (.transpData0 h0 h1 h2)) (fund2_ty h2)
  | .transpCon h0 h1 h2 h3 h4 h5 h6 => by
    rename_i D _ _ _ _ _ _ _
    cases hH : D.isHIT
    · exact valid_transpCon hW (hpre _ _ h0) hH h1 hK h2 h3 (sigwk_ty hpre h6)
        (pre2 hW hpre (.transpCon h0 h1 h2 h3 h4 h5 h6)).2 (sigwk_eq hpre (.transpCon h0 h1 h2 h3 h4 h5 h6))
        (fund2_tele h5) (fund2_ty h6) (fund2_transpInv h6 rfl)
    exact hDa.transpCon h0 hH h1 h2 h3 h4 (sigwk_tele hpre h5) (sigwk_ty hpre h6)
      (pre2 hW hpre (.transpCon h0 h1 h2 h3 h4 h5 h6)).2 (fund2_tele h5) (fund2_ty h6)
  | .transpHcomp h0 h1 h2 h3 h4 =>
    hDa.transpHcomp h0 h1 h2 (sigwk_ty hpre h3) (sigwk_ty hpre h4) (pre2 hW hpre (.transpHcomp h0 h1 h2 h3 h4)).2
      (fund2_ty h3) (fund2_ty h4)
termination_by structural hd

end

end

/-! ### Closed terms and the signature -/

/-- The identity related substitution at stage `k` (closed terms). -/
def CSub2.idS (S : Sig) (k : ℕ) : CSub2 S k .one [] k where
  σ := ISub.id k
  σ' := ISub.id k
  hσ := INear.refl _
  γ := Tm.var
  γ' := Tm.var
  hγ _ := rfl
  hγ' _ := rfl
  face := ent_refl _
  look x A h := by simp [Ctx.lookup] at h
  lookT x A h := by simp [Ctx.lookup] at h

/-- The related substitution from stage `0` into stage `k`. -/
def CSub2.nil (S : Sig) (k : ℕ) : CSub2 S 0 .one [] k where
  σ := ⟨fun _ => .zero, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  σ' := ⟨fun _ => .zero, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  hσ := INear.refl _
  γ := Tm.var
  γ' := Tm.var
  hγ _ := rfl
  hγ' _ := rfl
  face := ent_refl _
  look x A h := by simp [Ctx.lookup] at h
  lookT x A h := by simp [Ctx.lookup] at h

theorem valid_closed {t u A : Tm} (h : Valid2 S k .one [] t u A) (ht : t.closedB 0 k = true)
    (hu : u.closedB 0 k = true) (hA : A.closedB 0 k = true) : RT2 S k A A ∧ RE2 S k A t u := by
  have := h k (CSub2.idS S k)
  simp only [CSub2.L, CSub2.R, CSub2.idS] at this
  have e : ∀ {x : Tm}, x.closedB 0 k = true → x.subst Tm.var (ISub.id k).τ = x := fun hx => isub_id_of_closed hx
  rwa [e ht, e hu, e hA] at this

theorem valid_closed0 {t u A : Tm} (h : Valid2 S 0 .one [] t u A) (ht : t.closedB 0 0 = true)
    (hu : u.closedB 0 0 = true) (hA : A.closedB 0 0 = true) (k : ℕ) : RT2 S k A A ∧ RE2 S k A t u := by
  have := h k (CSub2.nil S k)
  simp only [CSub2.L, CSub2.R] at this
  simp only [closed0_subst ht, closed0_subst hu, closed0_subst hA] at this; exact this

/-- Element relations are invariant under near terms on the left (`RE2_near`). -/
theorem nearEl2_of (hW : WfSig S) : NearEl2 S := by
  intro k X t t' u hXX h hn ht'
  exact RE2.symm hW hXX (RE2_near hW hXX (RE2.symm hW hXX h) hn ht')

/-- The definitions of every prefix of the signature are related, and the declared types of its inductive
types are valid, by induction on the prefix. -/
theorem hyps_take (hW : WfSig S) (hK : KanOracle2 S) (hDa : ∀ n, DataHyp2 S (S.take n))
    : ∀ n, DefHyp2 S (S.take n) ∧ DeclHyp2 S n := by
  intro n
  induction n with
  | zero => exact ⟨fun i t A h => by simp at h, ⟨fun d hd => absurd hd (Nat.not_lt_zero _),
      fun d hd => absurd hd (Nat.not_lt_zero _)⟩⟩
  | succ n ih =>
    have hpre : ∀ (j : ℕ) (e : Entry), (S.take n)[j]? = some e → S[j]? = some e :=
      fun j e h => (getElem?_take_some h).2
    have hDe : DeclHyp2 S (S.take n).length := ih.2.mono (by simp)
    have hfund := fun {Ψ Φ Γ t A} (h : HasTy0 (S.take n) Ψ Φ Γ t A) =>
      fund2_ty hW hpre ih.1 hK (hDa n) (nearEl2_of hW) hDe h
    refine ⟨fun i t A h => ?_, ⟨fun d hd D hD j A hA k c => ?_, fun d hd D hD c' C hC i A hA k cs => ?_⟩⟩
    · obtain ⟨hi, hS⟩ := getElem?_take_some h
      by_cases hin : i < n
      · exact ih.1 i t A (by rw [List.getElem?_take_of_lt hin]; exact hS)
      · have hi' : i = n := by omega
        subst hi'
        obtain ⟨htc, hAc, -, hty⟩ := hW.1 i t A hS
        have h0 := spec_to_minimal (wfSig_take hW i) hty
        have hv := hfund h0
        intro k
        exact valid_closed0 hv htc htc hAc k
    · by_cases hdn : d < n
      · exact ih.2.params d hdn D hD j A hA k c
      obtain rfl : d = n := by omega
      rcases ((hW.2 d D hD).2.1 j A hA).2.2 with hty | ⟨kk, hkk, rfl⟩
      · have hv := hfund (spec_to_minimal (wfSig_take hW d) hty)
        exact ((RE2_univ_iff hW).1 (hv k c).2).2.2
      · exact RT2_univ hW
    · by_cases hdn : d < n
      · exact ih.2.points d hdn D hD c' C hC i A hA k cs
      obtain rfl : d = n := by omega
      have hty := (((hW.2 d D hD).2.2 c' C hC).1 i A hA).2.2.2.2
      have hv := hfund (spec_to_minimal (wfSig_take hW d) hty)
      exact ((RE2_univ_iff hW).1 (hv k cs).2).2.2

/-- **The binary fundamental lemma**, for derivations in the whole signature. -/
theorem fund2 (hW : WfSig S) (hK : KanOracle2 S) (hDa : ∀ n, DataHyp2 S (S.take n))
    {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) : Valid2 S Ψ Φ Γ t u A := by
  have hH := hyps_take hW hK hDa S.length
  have hD := hH.1
  rw [List.take_length] at hD
  have := hDa S.length
  rw [List.take_length] at this
  exact fund2_eq hW (fun _ _ h => h) hD hK this (nearEl2_of hW) hH.2 h

/-- The binary fundamental lemma for closed terms at stage `k`. -/
theorem fund2_closed (hW : WfSig S) (hK : KanOracle2 S) (hDa : ∀ n, DataHyp2 S (S.take n))
    {t u A : Tm} (h : EqTm0 S k .one [] t u A) : RT2 S k A A ∧ RE2 S k A t u := by
  obtain ⟨ht, hu⟩ := presup hW h
  have hA := RE2.typed ((fund2 hW hK hDa (EqTm0.refl ht)) k (CSub2.idS S k)).2
  refine valid_closed (fund2 hW hK hDa h) (closed_ty ht) (closed_ty hu) ?_
  rcases pre_ty (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 ht with ⟨l, hl⟩ | ⟨l, rfl, -⟩
  · exact closed_ty hl
  · rfl

end

end Model.Whnf
