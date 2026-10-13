import KubusCore.Meta.DataTele

/-!
# Metatheory: typing the contracta of the computation rules of inductive types

The redex's typing is given by its generation data (computed in `Presup.lean`): the premises of
the eliminator (`ElimPrem`) or of `transp`, and the scrutinee's introduction typing at its
natural type `X` (`IntroTy`), related to the type the elimination expects by `Rel`. Injectivity
of inductive types in their parameters (`EqTele0.dataInj`) relates the scrutinee's parameters
to the eliminator's.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem elimCon_of (hS : SigClosed S) {Ψ Φ Γ d D D' c C ps P bs b qs args rs m X l T}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) (hb : bs.toList[c]? = some b)
    (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
    (hbs : bs = Tm.ofList bs.toList)
    (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hE : ElimPrem S Ψ Φ Γ d D' ps P bs m) (hI : IntroTy S Ψ Φ Γ (con d c qs args rs) X)
    (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel) (r : Rel S Ψ Φ Γ X (data d ps))
    (tb : TB S Ψ Φ Γ (data d ps)) (ch : TyChainC S Ψ Φ Γ (P.inst (con d c qs args rs)) T) :
    HasTy0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T := by
  have hDD : D' = D := by have := hE.hD; rw [hD] at this; cases this; rfl
  subst hDD
  obtain ⟨hXq, D0, C0, hD0, hC0, hqs, hdq, hqt, haq, hrs, hrsc⟩ := hI
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  subst hXq
  have hlen := tele_length hE.hpt
  have ha : HasTele0 S Ψ Φ Γ (Tm.ofList args.toList) (C.argTys d D'.params.length) ps.toList.reverse := by
    rw [← hargs]; exact htele
  have happ := branch_app_typed hS hD hC hlen (hE.hbr c C b hC hb) ha (ihs_tele hE ha) hrs hrsc
  rw [← hargs] at happ
  -- relate the constructor at `ps` with the one at `qs`
  obtain ⟨m', _, e⟩ := r.collapse hX hl rfl tb (fun k h => by cases h)
  have hcp := HasTy0.con hD hC hE.hps hE.hdata hE.hpt htele hrs hrsc
  have hcq := HasTy0.conv (HasTy0.con hD hC hqs hdq hqt haq hrs hrsc) e
  have eps := EqTele0.dataInj hD hE.hpt hqt (EqTm0.symm e)
  have ec := EqTm0.con hD hC hcp hcq eps (EqTele0.refl htele) rfl
    (fun k r r' h1 h2 => by rw [h1] at h2; cases h2; exact I_eq_refl _)
  exact ch.transport (HasTy0.conv happ (HasTy0.inst_congr hS hE.hP hcp hcq ec))

theorem elimHcomp_C_eq (P H : Tm) : P.subst (consSub H) (fun i => .var (i + 1)) = (P.dshift).inst H := by
  scalc

theorem dshift_inst_dinst (P H : Tm) (r : I) : ((P.dshift).inst H).dinst r = P.inst (H.dinst r) := by
  scalc

theorem elim_dshift_dinst0 (d : Nat) (ps P bs u : Tm) :
    (elim d ps.dshift P.dshift bs.dshift u).dinst .zero = elim d ps P bs (u.dinst .zero) := by
  show elim d (ps.dshift.dinst .zero) (P.dshift.subst (up Tm.var) (I.inst0 .zero)) (bs.dshift.dinst .zero)
    (u.dinst .zero) = _
  rw [up_var, dinst_eq, dshift_dinst, dshift_dinst, dshift_dinst]

theorem ElimPrem.elim_ty {Ψ Φ Γ d D ps P bs m} (hE : ElimPrem S Ψ Φ Γ d D ps P bs m) {t : Tm}
    (ht : HasTy0 S Ψ Φ Γ t (data d ps)) : HasTy0 S Ψ Φ Γ (elim d ps P bs t) (P.inst t) :=
  HasTy0.elim hE.hD hE.hps hE.hdata hE.hpt hE.hP hE.hbs hE.hlen hE.hbr hE.hcoh ht

/-- Congruence of the eliminator in the scrutinee. -/
theorem ElimPrem.elim_congr (hS : SigClosed S) {Ψ Φ Γ d D ps P bs m} (hE : ElimPrem S Ψ Φ Γ d D ps P bs m)
    {t t' : Tm} (ht : HasTy0 S Ψ Φ Γ t (data d ps)) (ht' : HasTy0 S Ψ Φ Γ t' (data d ps))
    (e : EqTm0 S Ψ Φ Γ t t' (data d ps)) :
    EqTm0 S Ψ Φ Γ (elim d ps P bs t) (elim d ps P bs t') (P.inst t) :=
  EqTm0.elim hE.hD (hE.elim_ty ht)
    (HasTy0.conv (hE.elim_ty ht') (EqTm0.symm (HasTy0.inst_congr hS hE.hP ht ht' e)))
    (EqTele0.refl hE.hpt) (EqTm0.refl hE.hP) hE.hbs hE.hbs rfl
    (fun c C b b' hc hb hb' => by
      rw [hb] at hb'; cases hb'; exact EqTm0.refl (hE.hbr c C b hc hb)) e

theorem elimHcomp_of (hS : SigClosed S) {Ψ Φ Γ d D D' ps P bs qs φ u a m X l T}
    (hD : S[d]? = some (.data D)) (hh : HasTy0 S Ψ Φ Γ (hcomp (data d ps) φ u a) (data d ps))
    (hE : ElimPrem S Ψ Φ Γ d D' ps P bs m)
    (hI : IntroTy S Ψ Φ Γ (hcomp (data d qs) φ u a) X)
    (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel) (r : Rel S Ψ Φ Γ X (data d ps))
    (tb : TB S Ψ Φ Γ (data d ps)) (ch : TyChainC S Ψ Φ Γ (P.inst (hcomp (data d qs) φ u a)) T) :
    HasTy0 S Ψ Φ Γ (comp (P.subst (consSub (hfill (data d ps) φ u a)) (fun i => .var (i + 1))) φ
      (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T := by
  obtain ⟨_, ⟨_, hφ, hu, ha, hside⟩, _⟩ := gen_hcomp hh rfl
  obtain ⟨hH, hH0, hH1, hHu⟩ := hfill_typed hS hE.hdata hφ hu ha hside
  have hw := wf_of_ty ha
  have hs := scoped_of_wf hw
  have hXs : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXs1 : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift hXs
  have hent1 : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left Φ φ)
  have hPd : HasTy0 S (Ψ + 1) Φ.shift ((data d ps).dshift :: Γ.dshift) P.dshift (univ m) :=
    HasTy0.dwk hS hE.hP
  have hC := HasTy0.subst hS hPd hH
  rw [← elimHcomp_C_eq] at hC
  -- the tube
  obtain ⟨D'', m', hE'⟩ := hE.dwk hS ha
  have hE'c := hE'.restrict hXs1 hent1
  have hel := hE'c.elim_ty hu
  have hHc := HasTy0.restrict hXs1 hent1 hH
  have eT := HasTy0.inst_congr hS (HasTy0.restrict hXs1 hent1 hPd) hHc hu hHu
  have hu' := HasTy0.conv hel (EqTm0.symm eT)
  rw [← elimHcomp_C_eq] at hu'
  -- the base
  have hH0t : HasTy0 S Ψ Φ Γ ((hfill (data d ps) φ u a).dinst .zero) (data d ps) := by
    have := HasTy0.dsubst hS hH (r := .zero) trivial
    rwa [dshift_dinst] at this
  have hu0 := HasTy0.conv (hE.elim_ty ha)
    (EqTm0.symm (HasTy0.inst_congr hS hE.hP hH0t ha hH0))
  rw [← dshift_inst_dinst, ← elimHcomp_C_eq] at hu0
  -- the side condition
  have hud : HasTy0 S Ψ (cof Φ φ) Γ (u.dinst .zero) (data d ps) := by
    have := HasTy0.dsubst hS hu (r := .zero) trivial
    rwa [dshift_dinst] at this
  have hentc : I.Entails (cof Φ φ) Φ := ent_and_left Φ φ
  have hEc := hE.restrict hXs hentc
  have hac := HasTy0.restrict hXs hentc ha
  have hH0c := HasTy0.restrict hXs hentc hH0t
  have es := hEc.elim_congr hS hud hac hside
  have e2 := HasTy0.inst_congr hS hEc.hP hud hH0c
    (EqTm0.trans hside (EqTm0.symm (EqTm0.restrict hXs hentc hH0)))
  have hside' := EqTm0.conv es e2
  rw [← elim_dshift_dinst0, ← dshift_inst_dinst, ← elimHcomp_C_eq] at hside'
  have hcomp := comp_typed hS hC hφ hu' hu0 hside'
  rw [show (P.subst (consSub (hfill (data d ps) φ u a)) (fun i => .var (i + 1))).dinst .one =
    P.inst ((hfill (data d ps) φ u a).dinst .one) by rw [elimHcomp_C_eq, dshift_inst_dinst]] at hcomp
  -- the result type
  have hH1t : HasTy0 S Ψ Φ Γ ((hfill (data d ps) φ u a).dinst .one) (data d ps) := by
    have := HasTy0.dsubst hS hH (r := .one) trivial
    rwa [dshift_dinst] at this
  have e3 := HasTy0.inst_congr hS hE.hP hH1t hh hH1
  obtain ⟨hXq, l', hAq, _, huq, haq, hsideq⟩ := hI
  subst hXq
  obtain ⟨m'', _, eq⟩ := r.collapse hX hl rfl tb (fun k h => by cases h)
  have hhq := HasTy0.conv (HasTy0.hcomp hAq hφ huq haq hsideq) eq
  have e4 := EqTm0.hcomp hh hhq (EqTm0.symm eq) (ent_refl _) (ent_refl _)
    (EqTm0.refl hu) (EqTm0.refl ha)
  have e5 := HasTy0.inst_congr hS hE.hP hh hhq e4
  exact ch.transport (HasTy0.conv (HasTy0.conv hcomp e3) e5)

theorem transpCon_of (hS : SigClosed S) {Ψ Φ Γ d D c C ps φ qs args rs l0 X l T}
    (hD : S[d]? = some (.data D)) (hne : D.params ≠ []) (hC : D.ctors[c]? = some C)
    (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
    (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0)) (hφ : φ.Scoped Ψ)
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0))
    (hI : IntroTy S Ψ Φ Γ (con d c qs args rs) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X ((data d ps).dinst .zero)) (tb : TB S Ψ Φ Γ ((data d ps).dinst .zero))
    (ch : TyChainC S Ψ Φ Γ ((data d ps).dinst .one) T) :
    HasTy0 S Ψ Φ Γ (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  sorry

theorem skip1I_dinst0_dshift (A : Tm) : ((A.dsubst skip1I).dinst .zero).dshift = (A.dinst .zero).dshift.dshift := by
  ssub

theorem dshift_skip1I (A : Tm) : A.dshift.subst Tm.var skip1I = A.dshift.dshift := by ssub

theorem skip1I_dinst0 (A : Tm) : (A.dsubst skip1I).dinst .zero = (A.dinst .zero).dshift := by ssub

theorem skip1I_dinst1 (A : Tm) : (A.dsubst skip1I).dinst .one = (A.dinst .one).dshift := by ssub

theorem I_shift_skip1I (Φ : I) : Φ.shift.subst skip1I = Φ.shift.shift := by
  simp only [I.shift, I.ren, I_subst_subst]; rfl

theorem ctxI_skip1I (Γ : Ctx) : ctxI skip1I Γ.dshift = Γ.dshift.dshift := by
  rw [ctxI_dshift_gen]; exact ctxI_add2 Γ

theorem skip1I_scoped (Ψ : Nat) : ∀ i < Ψ + 1, (skip1I i).Scoped (Ψ + 1 + 1) := by
  intro i hi; cases i with
  | zero => show 0 < Ψ + 1 + 1; omega
  | succ i => show i + 2 < Ψ + 1 + 1; omega

theorem transp_skip_dinst0 (A : Tm) (φ : I) (u : Tm) :
    (transp (A.dsubst skip1I) φ.shift u).dinst .zero = transp A φ (u.dinst .zero) := by
  show transp ((A.subst Tm.var skip1I).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero)))
    (φ.shift.subst (I.inst0 .zero)) (u.dinst .zero) = _
  congr 1
  · rw [subst_subst]
    apply subst_id_of
    · intro n; rfl
    · intro i; cases i with
      | zero => rfl
      | succ i => rfl
  · simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var φ

/-- A transport, renamed past a new interval variable 1 (the tube variable of an `hcomp`). -/
theorem transp_skip (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {A : Tm} {φ ψ : I} {u : Tm} {l : Nat}
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l)) (hφ : φ.Scoped Ψ)
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l))
    (hu : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u (A.dinst .zero).dshift) :
    HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (transp (A.dsubst skip1I) φ.shift u) (A.dinst .one).dshift := by
  have hw2 := Wf0.dwk hS (wf_of_ty hu)
  have hs2 := scoped_of_wf hw2
  have hL' := HasTy0.isub hS (Φ' := (cof Φ ψ).shift.shift) hL (skip1I_scoped Ψ)
    (by rw [I_shift_skip1I]; exact ent_shift (ent_shift (ent_and_left _ _))) (by rw [ctxI_skip1I]; exact hw2)
  rw [ctxI_skip1I] at hL'
  have hφ1 : φ.shift.Scoped (Ψ + 1) := scoped_shift hφ
  have hs0 : (cof Φ ψ).Scoped Ψ := scoped_of_wf (wf_unshift hS (wf_of_ty hu))
  have hX : (cof (cof Φ ψ).shift φ.shift).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨scoped_shift hs0, hφ1⟩
  have hc' := EqTm0.isub hS (Φ' := (cof (cof Φ ψ).shift φ.shift).shift) hc (skip1I_scoped Ψ)
    (by rw [I_shift_skip1I]; exact ent_shift (ent_shift (ent_and_mono (ent_and_left _ _) (ent_refl _))))
    (by rw [ctxI_skip1I]; exact hw2.restrict hX (ent_shift (ent_and_left _ _)))
  rw [ctxI_skip1I, dshift_skip1I, ← skip1I_dinst0_dshift] at hc'
  rw [← dsubst_eq_subst] at hL' hc'
  have := HasTy0.transp hL' hφ1 hc' (by rw [skip1I_dinst0]; exact hu)
  rwa [skip1I_dinst1] at this

theorem transpHcomp_of (hS : SigClosed S) {Ψ Φ Γ d D ps φ qs ψ u a l0 X l T}
    (hD : S[d]? = some (.data D)) (hne : D.params ≠ [])
    (hh : HasTy0 S Ψ Φ Γ (hcomp (data d (ps.dinst .zero)) ψ u a) (data d (ps.dinst .zero)))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0)) (hφ : φ.Scoped Ψ)
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0))
    (hI : IntroTy S Ψ Φ Γ (hcomp (data d qs) ψ u a) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X ((data d ps).dinst .zero)) (tb : TB S Ψ Φ Γ ((data d ps).dinst .zero))
    (ch : TyChainC S Ψ Φ Γ ((data d ps).dinst .one) T) :
    HasTy0 S Ψ Φ Γ (hcomp (data d (ps.dinst .one)) ψ
      (transp ((data d ps).dsubst skip1I) φ.shift u) (transp (data d ps) φ a)) T := by
  obtain ⟨_, ⟨_, hψ, hu, ha, hside⟩, _⟩ := gen_hcomp hh rfl
  have hs := scoped_of_wf (wf_of_ty ha)
  have hXs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hent : I.Entails (cof Φ ψ) Φ := ent_and_left Φ ψ
  have htu := transp_skip hS hL hφ hc hu
  have hA1 := HasTy0.dsubst hS hL (r := .one) trivial
  have hta := HasTy0.transp hL hφ hc ha
  have hu0 : HasTy0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) ((data d ps).dinst .zero) := by
    have := HasTy0.dsubst hS hu (r := .zero) trivial
    rwa [dshift_dinst] at this
  have hLc := HasTy0.restrict (scoped_shift hXs) (ent_shift hent) hL
  have hcc := EqTm0.restrict (scoped_shift (show (cof (cof Φ ψ) φ).Scoped Ψ from ⟨hXs, hφ⟩))
    (ent_shift (ent_and_mono hent (ent_refl _))) hc
  have h1 := HasTy0.transp hLc hφ hcc hu0
  have h2 := HasTy0.restrict hXs hent hta
  have side := EqTm0.transp h1 h2 (EqTm0.refl hLc) (ent_refl _) (ent_refl _) hside
  rw [← transp_skip_dinst0] at side
  exact ch.transport (HasTy0.hcomp hA1 hψ htu hta side)

end KubusCore.Meta
