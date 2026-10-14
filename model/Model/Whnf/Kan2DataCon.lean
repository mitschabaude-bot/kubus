import Model.Whnf.Kan2DataLine

/-!
# Composition of related constructors in an inductive type without path constructors

The `hcompCon` contracta of compositions of related constructors along related tubes are related at
one stage (`hcompCon2`): recursive arguments by the composition of the base's arguments (an
induction hypothesis), point arguments by heterogeneous composition along their related type
lines, whose earlier arguments are the related fillers.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hW hD hH

/-- A term judgmentally equal to a constructor of an inductive type without path constructors is that
constructor at the parameters of its type, in any context. -/
theorem con_retype0 {Ψ : ℕ} {Φ : I} {t qs p : Tm} {c : ℕ} {C : Ctor} {Z : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C) (he : EqTm0 S Ψ Φ [] t (.con d c qs (Tm.ofList Z) rs) (.data d p))
    (hpT : HasTy0 S Ψ Φ [] (.data d p) (.univ D.level)) :
    HasTele0 S Ψ Φ [] (Tm.ofList Z) (C.argTys d D.params.length) p.toList.reverse ∧
    EqTm0 S Ψ Φ [] t (.con d c p (Tm.ofList Z) []) (.data d p) ∧ rs = [] := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨-, hcon, -⟩ := pre_eq hS hT hCt he
  obtain ⟨D', C', hD', hC', hpL, -, htele, hrs, m, eq0⟩ := con_args hW hcon hpT
  rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (nonHIT_ctor hH hC).1])
  subst hrs0
  obtain ⟨hq, -, -⟩ := pre_eq hS hT hCt eq0
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hpT rfl
  rw [hD] at hD2; cases hD2
  have eps : EqTele0 S Ψ Φ [] p qs D.params [] := EqTele0.dataInj hD hpt hqt (EqTm0.symm eq0)
  have hc0 : HasTy0 S Ψ Φ [] (.con d c p (Tm.ofList Z) []) (.data d p) :=
    HasTy0.con hD hC (tele_isList hpt) hpT hpt htele (by simp [(nonHIT_ctor hH hC).1]) (by simp)
  have ec := EqTm0.con hD hC hc0 hcon eps (EqTele0.refl htele) rfl (fun _ _ _ h => by simp at h)
  exact ⟨htele, he.trans (EqTm0.symm ec), rfl⟩

end

theorem getD_take_lt {L : List Tm} {i j : ℕ} (h : i < j) : (L.take j).getD i .abort = L.getD i .abort := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

section core
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P Q Q' : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
  (hQ : RT2 S K (.data d P) (.data d Q)) (hQ' : RT2 S K (.data d P) (.data d Q'))
  (hArgK : ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → KanP2 S n ((ΘK S D d K P).ty c j n g pre))
include hW hD hH hP hPP hQ hQ' hArgK

/-- The `hcompCon` contracta of compositions of related constructors along related tubes are related
at one stage. -/
theorem hcompCon2 {k1 : ℕ} (ρ : ISub k1 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs qs' : Tm}
    {X X' : List Tm} (hXl : X.length = C.args.length) (hXl' : X'.length = C.args.length)
    (hrecR : ∀ i (hi : i < C.args.length), C.isRec i = true →
      RE2 S k1 (.data d (P.isub ρ)) (X.getD i .abort) (X'.getD i .abort))
    (hptR : ∀ i (hi : i < C.args.length), C.isRec i = false →
      RE2 S k1 ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ).toList.reverse))
        (X.getD i .abort) (X'.getD i .abort))
    (hrecH : ∀ i (hi : i < C.args.length), C.isRec i = true → ∀ (Q1 Q1' : Tm),
      RT2 S K (.data d P) (.data d Q1) → RT2 S K (.data d P) (.data d Q1') → ∀ K2 (σ : ISub K2 k1),
      HC2 S K2 (.data d (P.isub (ρ.comp σ))) (.data d (Q1.isub (ρ.comp σ))) (.data d (Q1'.isub (ρ.comp σ)))
        ((X.getD i .abort).isub σ) ((X'.getD i .abort).isub σ))
    {φ φ' : I} {u u' : Tm} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') []))
      (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) (.data d (P.isub ρ)))
    (hteq : EqTm S (k1 + 1) (cof .one φ).shift [] u u' (Tm.data d (P.isub ρ)).dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u')
    (hbd : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((Tm.data d (P.isub ρ)).isub σ) ((u.isub σ.up).dinst .zero) ((Tm.con d c qs' (Tm.ofList X') []).isub σ))
    (hbd' : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((Tm.data d (P.isub ρ)).isub σ) ((Tm.con d c qs (Tm.ofList X) []).isub σ) ((u'.isub σ.up).dinst .zero)) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
      (.data d (P.isub ρ)) (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) := by
  have hS := sigClosed_of_wfSig hW
  have hdD := dataD_eq hW hD
  set q := Q.isub ρ with hq
  set q' := Q'.isub ρ with hq'
  set p := P.isub ρ with hp
  set Ac := C.argTy d D.params.length with hAc
  set us := (List.range C.args.length).map fun j => proj d D q.dshift c C j u with hus
  set us' := (List.range C.args.length).map fun j => proj d D q'.dshift c C j u' with hus'
  set Y := (List.range C.args.length).map (Meta.hOut C Ac (.data d q) q.dshift.toList φ us X) with hY
  set Y' := (List.range C.args.length).map (Meta.hOut C Ac (.data d q') q'.dshift.toList φ' us' X') with hY'
  -- typing
  obtain ⟨l0, ⟨hdq, hφs, hut, hb, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨l0', ⟨hdq', hφs', hut', hb', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hdq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hqt'⟩ := gen_data_tele hdq' rfl
  rw [hD] at hD2; cases hD2
  have hqT : HasTy S k1 .one [] (.data d q) (.univ D.level) := minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hqt)
  have hq'T : HasTy S k1 .one [] (.data d q') (.univ D.level) :=
    minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hqt')
  have hpT : HasTy S k1 .one [] (.data d p) (.univ D.level) := HasTy.isubS hW hP ρ
  have hXP := tyCode_of_univ hW hP
  have hPQρ : RT2 S k1 (.data d p) (.data d q) := RT2.isub hW hXP hQ ρ
  have hPQ'ρ : RT2 S k1 (.data d p) (.data d q') := RT2.isub hW hXP hQ' ρ
  have hPPρ : RT2 S k1 (.data d p) (.data d p) := RT2.isub hW hXP hPP ρ
  have hTPQ : TyEq S k1 (.data d p) (.data d q) := (Comp2_ty_base hPQρ).2.2.2.2.2
  have hTPQ' : TyEq S k1 (.data d p) (.data d q') := (Comp2_ty_base hPQ'ρ).2.2.2.2.2
  have hXp : TyCode k1 (semK S k1 (.data d p)) := tyCode_of_univ hW hpT
  have hpσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 ((Tm.data d p).isub σ) ((Tm.data d p).isub σ) :=
    fun σ => RT2.isub hW hXp hPPρ σ
  -- the faces
  have hn' : ¬ I.Entails .one φ' := fun h => hn (ent_trans h h21)
  have hholds : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ'.subst σ.τ)).holds →
      (ival (idEnv k3) (φ.subst σ.τ)).holds := fun σ h => by
    rw [holds_iff_entails (I.scoped_subst hφs σ.sc)]
    exact ent_trans ((holds_iff_entails (I.scoped_subst hφs' σ.sc)).1 h) (ent_subst h21 σ.τ)
  -- the tubes related to themselves
  have htubeL : Tube2 S k1 (.data d p) φ u u := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hpσ σ) (htube k3 σ r r' hr hr' hE hh) (RE2.symm hW (hpσ σ) (htube k3 σ r' r' hr' hr' (I_eq_refl _) hh))
  have htubeR : Tube2 S k1 (.data d p) φ' u' u' := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hpσ σ) (RE2.symm hW (hpσ σ) (htube k3 σ r r hr hr (I_eq_refl _) (hholds σ hh)))
      (htube k3 σ r r' hr hr' hE (hholds σ hh))
  have hcan := tubeCanon_of hW hD hH hP ρ hTPQ hqT htubeL
  have hcan' := tubeCanon_of hW hD hH hP ρ hTPQ' hq'T htubeR
  -- the contracta
  have e_hc := hcompCon_sound hW hD hH hC hty hcan
  have e_hc' := hcompCon_sound hW hD hH hC hty' hcan'
  have hul : us.length = C.args.length := by simp [us]
  have hul' : us'.length = C.args.length := by simp [us']
  have heqT := Meta.hcompTele_eq C Ac (.data d q) q.dshift.toList φ us X us X 0 rfl rfl (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heqT
  rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d q) q.dshift.toList φ us X 0).reverse from rfl, heqT] at e_hc
  have heqT' := Meta.hcompTele_eq C Ac (.data d q') q'.dshift.toList φ' us' X' us' X' 0 rfl rfl (by rw [hul', hXl'])
  simp only [hXl', ← List.range_eq_range'] at heqT'
  rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d q') q'.dshift.toList φ' us' X' 0).reverse from rfl, heqT']
    at e_hc'
  have rL : Red S (.hcomp (.data d q) φ u (.con d c qs (Tm.ofList X) [])) (.con d c q (Tm.ofList Y) []) := by
    refine .step (step_hcompCon hD hH hC hn X) ?_
    rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d q) q.dshift.toList φ us X 0).reverse from rfl, heqT]
    exact .refl _
  have rR : Red S (.hcomp (.data d q') φ' u' (.con d c qs' (Tm.ofList X') [])) (.con d c q' (Tm.ofList Y') []) := by
    refine .step (step_hcompCon hD hH hC hn' X') ?_
    rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d q') q'.dshift.toList φ' us' X' 0).reverse from rfl, heqT']
    exact .refl _
  have eLR : EqTm S k1 .one [] (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') []) (.data d p) :=
    e_hc.symm.trans (heq.trans e_hc')
  refine DR2At.expandR hW (DR2At.expand hW ?_ rL e_hc) rR e_hc'
  -- the premises of `hcompCon` on both sides
  obtain ⟨hXq, ebase, -, -⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hqT
  obtain ⟨hXq', ebase', -, -⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb')) (TyEq.refl _) hq'T
  have hside_q : EqTm S k1 (cof .one φ) [] (u.dinst .zero) (.con d c q (Tm.ofList X) []) (.data d q) :=
    (minimal_to_spec_eq hside).trans (EqTm.restrict (show (cof .one φ).Scoped k1 from ⟨trivial, hφs⟩)
      (ent_and_left _ _) ebase)
  have hside_q' : EqTm S k1 (cof .one φ') [] (u'.dinst .zero) (.con d c q' (Tm.ofList X') []) (.data d q') :=
    (minimal_to_spec_eq hside').trans (EqTm.restrict (show (cof .one φ').Scoped k1 from ⟨trivial, hφs'⟩)
      (ent_and_left _ _) ebase')
  obtain ⟨G1, G2, G3, G4⟩ := hcompCon_premises hW hD hH hC hqT hφs hut hside_q hXq hcan
  obtain ⟨G1', G2', G3', G4'⟩ := hcompCon_premises hW hD hH hC hq'T hφs' hut' hside_q' hXq' hcan'
  -- the projections of the tubes are judgmentally equal
  have hΦs : ((cof .one φ).shift).Scoped (k1 + 1) := KubusCore.I.scoped_shift ⟨trivial, hφs⟩
  have hΦe : I.Entails (cof .one φ).shift (cof .one φ').shift := ent_shift (ent_and_mono (ent_refl _) h12)
  have hdq1 : HasTy0 S (k1 + 1) (cof .one φ).shift [] (.data d q.dshift) (.univ D.level) :=
    HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hqT))
  have H1 := PD.of hW hD hH hdq1
  -- the types, under the face, weakened
  have dwkΦ : ∀ {A B : Tm} {l : ℕ}, EqTm S k1 .one [] A B (.univ l) →
      EqTm0 S (k1 + 1) (cof .one φ).shift [] A.dshift B.dshift (.univ l) := fun e =>
    EqTm0.restrict hΦs (ent_one _) (EqTm0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal_eq hW e))
  obtain ⟨lq'q, eq'q⟩ := tyEq_eq hW (hTPQ'.symm.trans hW hTPQ) ⟨_, hqT⟩
  obtain ⟨lpq, epq⟩ := tyEq_eq hW hTPQ ⟨_, hqT⟩
  have hteq0 : EqTm0 S (k1 + 1) (cof .one φ).shift [] u u' (.data d q.dshift) :=
    EqTm0.conv (spec_to_minimal_eq hW hteq) (dwkΦ epq)
  have G2'' : EqTm0 S (k1 + 1) (cof .one φ).shift [] u' (.con d c q'.dshift (Tm.ofList us') []) (.data d q.dshift) :=
    EqTm0.conv (EqTm0.restrict hΦs hΦe G2') (dwkΦ eq'q)
  obtain ⟨hus't, eus', -⟩ := con_retype0 hW hD hH hC G2'' hdq1
  have euu : ∀ i (hi : i < C.args.length), EqTm0 S (k1 + 1) (cof .one φ).shift [] (us.getD i .abort) (us'.getD i .abort)
      ((C.argTy d D.params.length i).substList ((us.take i).reverse ++ q.dshift.toList.reverse)) := fun i hi =>
    con_args_eq hW hD hH H1 hC G1 hus't ((EqTm0.symm G2).trans (hteq0.trans eus')) hi
  -- the arguments of the contracta are judgmentally equal
  obtain ⟨hYp, eYp, -, hYl⟩ := con_retype hW hD hH hC (EqTm.refl (HasTy.eqL eLR)) (TyEq.refl _) hpT
  obtain ⟨hY'p, eY'p, -, hY'l⟩ := con_retype hW hD hH hC (EqTm.refl (HasTy.eqR eLR)) (TyEq.refl _) hpT
  have Hp := PD.of hW hD hH (spec_to_minimal hW hpT)
  have eYY' : ∀ i (hi : i < C.args.length), EqTm0 S k1 .one [] (Y.getD i .abort) (Y'.getD i .abort)
      ((Ac i).substList ((Y.take i).reverse ++ p.toList.reverse)) := fun i hi =>
    con_args_eq hW hD hH Hp hC hYp hY'p (spec_to_minimal_eq hW (eYp.symm.trans (eLR.trans eY'p))) hi
  -- restrictions
  have ePσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), (Tm.data d p).isub σ = .data d (P.isub (ρ.comp σ)) := fun σ => by
    show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]
  have eQσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), q.isub σ = Q.isub (ρ.comp σ) := fun σ => Tm.isub_isub _ _ _
  have eQ'σ : ∀ {k3 : ℕ} (σ : ISub k3 k1), q'.isub σ = Q'.isub (ρ.comp σ) := fun σ => Tm.isub_isub _ _ _
  have H1' := PD.of hW hD hH (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hq'T))
  have husi : ∀ i, i < C.args.length → us.getD i .abort = proj d D q.dshift c C i u := by
    intro i hi; simp [us, List.getD_eq_getElem?_getD, hi]
  have husi' : ∀ i, i < C.args.length → us'.getD i .abort = proj d D q'.dshift c C i u' := by
    intro i hi; simp [us', List.getD_eq_getElem?_getD, hi]
  have usσ : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) {j : ℕ} (hj : j < C.args.length),
      (us.getD j .abort).isub (ISub.cons r hr σ) = proj d D (Q.isub (ρ.comp σ)) c C j ((u.isub σ.up).dinst r) := by
    intro k3 σ r hr j hj
    rw [husi j hj, proj_tube_isub hW hD hC hj H1.hpsL H1.hpl σ hr, eQσ]
  have usσ' : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) {j : ℕ} (hj : j < C.args.length),
      (us'.getD j .abort).isub (ISub.cons r hr σ) =
        proj d D (Q'.isub (ρ.comp σ)) c C j ((u'.isub σ.up).dinst r) := by
    intro k3 σ r hr j hj
    rw [husi' j hj, proj_tube_isub hW hD hC hj H1'.hpsL H1'.hpl σ hr, eQ'σ]
  have usmap : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3),
      us.map (·.isub (ISub.cons r hr σ)) =
        (List.range C.args.length).map fun j => proj d D (Q.isub (ρ.comp σ)) c C j ((u.isub σ.up).dinst r) := by
    intro k3 σ r hr
    apply List.ext_getElem (by simp [us])
    intro j h1 h2
    have hj : j < C.args.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← usσ σ r hr hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
    rfl
  have huc : u.closedB 0 (k1 + 1) = true := closed_ty hut
  have huc' : u'.closedB 0 (k1 + 1) = true := closed_ty hut'
  have hPσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) :=
    fun σ => RT2.isub hW hXP hPP (ρ.comp σ)
  -- the normal forms of the tubes at points of their faces are the constructor `c`
  have tagL : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3), (ival (idEnv k3) (φ.subst σ.τ)).holds →
      ∀ {c0 : ℕ} {C0 : Ctor} {qs0 : Tm} {Z : List Tm}, D.ctors[c0]? = some C0 →
      RedE S k3 (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst r) (.con d c0 qs0 (Tm.ofList Z) []) → c0 = c := by
    intro k3 σ r hr hh c0 C0 qs0 Z hC0 ht
    have hTσ : TyEq S k3 (.data d (P.isub (ρ.comp σ))) (.data d (q.isub σ)) := by
      have := hTPQ.isub hW σ; rwa [ePσ] at this
    obtain ⟨-, e, -, -⟩ := con_retype hW hD hH hC0 ht.2 hTσ (HasTy.isubS hW hqT σ)
    exact tube_tag hW hD hH hC hqT hφs huc hside_q hcan σ hr hh hC0 e
  have tagR : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3), (ival (idEnv k3) (φ'.subst σ.τ)).holds →
      ∀ {c0 : ℕ} {C0 : Ctor} {qs0 : Tm} {Z : List Tm}, D.ctors[c0]? = some C0 →
      RedE S k3 (.data d (P.isub (ρ.comp σ))) ((u'.isub σ.up).dinst r) (.con d c0 qs0 (Tm.ofList Z) []) → c0 = c := by
    intro k3 σ r hr hh c0 C0 qs0 Z hC0 ht
    have hTσ : TyEq S k3 (.data d (P.isub (ρ.comp σ))) (.data d (q'.isub σ)) := by
      have := hTPQ'.isub hW σ; rwa [ePσ] at this
    obtain ⟨-, e, -, -⟩ := con_retype hW hD hH hC0 ht.2 hTσ (HasTy.isubS hW hq'T σ)
    exact tube_tag hW hD hH hC hq'T hφs' huc' hside_q' hcan' σ hr hh hC0 e
  -- the projections of the tubes at points of their faces
  have PRJ : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ j (hj : j < C.args.length),
      RE2 S k3 ((Ac j).substList (((us.map (·.isub (ISub.cons r hr σ))).take j).reverse ++
        (Q.isub (ρ.comp σ)).toList.reverse)) ((us.getD j .abort).isub (ISub.cons r hr σ))
        ((us'.getD j .abort).isub (ISub.cons r' hr' σ)) := by
    intro k3 σ r r' hr hr' hE hh j hj
    have hx := htube k3 σ r r' hr hr' hE hh
    rw [ePσ] at hx
    obtain ⟨c0, C0, qs0, Z, -, -, hC0, -, -, ht, -, -, -⟩ := dataLit_args hW hD hH hP hPP (ρ.comp σ) hx
    have hcc := tagL σ r hr hh hC0 ht
    rw [hcc] at hC0 ht
    rw [hC] at hC0; cases hC0
    have := (projs_rel hW hD hH hP hPP hQ hQ' (ρ.comp σ) hx hC ht.1 hj).1
    rw [usmap σ r hr, usσ σ r hr hj, usσ' σ r' hr' hj]
    exact this
  -- the projections of the left tube against the right base
  have PRJb : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ j (hj : j < C.args.length),
      RE2 S k3 ((Ac j).substList (((us.map (·.isub (ISub.cons .zero trivial σ))).take j).reverse ++
        (Q.isub (ρ.comp σ)).toList.reverse)) ((us.getD j .abort).isub (ISub.cons .zero trivial σ))
        ((X'.getD j .abort).isub σ) := by
    intro k3 σ hh j hj
    have hx := hbd k3 σ hh
    rw [ePσ, show (Tm.con d c qs' (Tm.ofList X') []).isub σ =
        .con d c (qs'.isub σ) (Tm.ofList (X'.map (·.isub σ))) [] by
      show Tm.con d c (qs'.isub σ) ((Tm.ofList X').isub σ) [] = _; rw [ofList_isub]] at hx
    have hxx := RE2.trans hW (hPσ σ) hx (RE2.symm hW (hPσ σ) hx)
    obtain ⟨c0, C0, qs0, Z, qs1, Z1, hC0, hZl, hZ1l, ht, ht1, hZZ⟩ := dataLit_argsU hW hD hH hP hPP (ρ.comp σ) hx
    have e1 := RedW.unique ht1.1 (redW_self (step_con_nonHIT hD hH hC _ _ _))
    simp only [Tm.con.injEq] at e1
    obtain ⟨-, hc0, -, ea, -⟩ := e1
    have ea' := congrArg Tm.toList ea
    simp only [toList_ofList] at ea'
    subst ea'
    rw [hc0] at hC0 ht
    rw [hC] at hC0; cases hC0
    obtain ⟨-, p2, p3⟩ := projs_rel hW hD hH hP hPP hQ hQ (ρ.comp σ) hxx hC ht.1 hj
    have hX := RE2.tyCode hW p2
    have z := RE2.conv hW p3 (hZZ j hj)
    rw [usmap σ .zero trivial, usσ σ .zero trivial hj]
    have hgx : (X'.map (·.isub σ)).getD j .abort = (X'.getD j .abort).isub σ := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases X'[j]? with _ | a <;> rfl
    rw [hgx] at z
    exact RE2.trans hW (RT2.refl' hW (RE2.tyCode hW (hZZ j hj)) p3) p2 z
  -- the left base against the projections of the right tube
  have PRJb' : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ j (hj : j < C.args.length),
      RE2 S k3 ((Ac j).substList (((X.map (·.isub σ)).take j).reverse ++ (P.isub (ρ.comp σ)).toList.reverse))
        ((X.getD j .abort).isub σ) ((us'.getD j .abort).isub (ISub.cons .zero trivial σ)) := by
    intro k3 σ hh j hj
    have hx := hbd' k3 σ hh
    rw [ePσ, show (Tm.con d c qs (Tm.ofList X) []).isub σ =
        .con d c (qs.isub σ) (Tm.ofList (X.map (·.isub σ))) [] by
      show Tm.con d c (qs.isub σ) ((Tm.ofList X).isub σ) [] = _; rw [ofList_isub]] at hx
    have hxx := RE2.trans hW (hPσ σ) (RE2.symm hW (hPσ σ) hx) hx
    obtain ⟨c0, C0, qs0, Z, qs1, Z1, hC0, hZl, hZ1l, ht, ht1, hZZ⟩ := dataLit_argsU hW hD hH hP hPP (ρ.comp σ) hx
    have e1 := RedW.unique ht.1 (redW_self (step_con_nonHIT hD hH hC _ _ _))
    simp only [Tm.con.injEq] at e1
    obtain ⟨-, hc0, -, ea, -⟩ := e1
    have ea' := congrArg Tm.toList ea
    simp only [toList_ofList] at ea'
    subst ea'
    rw [hc0] at hC0 ht1
    rw [hC] at hC0; cases hC0
    obtain ⟨-, p2, p3⟩ := projs_rel hW hD hH hP hPP hQ' hQ' (ρ.comp σ) hxx hC ht1.1 hj
    have hPl := (dataLit_rel hW hD hP hPP (ρ.comp σ)).2.2.2.2.2.1
    have hplen : (P.isub (ρ.comp σ)).toList.length = D.params.length := by
      have := data_len_of hW (⟨_, .inl (HasTy.isubS hW hP (ρ.comp σ))⟩ : IsTyK S k3 (.data d (P.isub (ρ.comp σ))))
      rwa [dataD_eq hW hD] at this
    have TX := argTy_rt2 hW hD hH hP hPP hPP hPP (ρ.comp σ) hC hj (A := (X.map (·.isub σ)).take j)
      (B := Z1.take j) (by simp [hXl]; omega) (by simp [hZ1l]; omega) (fun i hi => by
        have h := hZZ i (by omega)
        rw [getD_take_lt hi, getD_take_lt hi, List.take_take, Nat.min_eq_left hi.le]
        cases hri : C.isRec i
        · exact ⟨fun h' => (by cases h'), fun _ => h⟩
        · refine ⟨fun _ => ?_, fun h' => (by cases h')⟩
          rwa [argTy_rec_inst hri hPl hplen (by simp; omega)] at h)
    have hXT := RE2.tyCode hW (hZZ j hj)
    have hXZ := RT2.tyCode_r hW TX hXT
    have q1 := RE2.conv hW (RT2.symm hW hXT TX) (RE2.conv hW (RT2.symm hW hXZ p3)
      (RE2.symm hW (RT2.refl' hW hXZ p3) p2))
    rw [usσ' σ .zero trivial hj]
    have hgx : (X.map (·.isub σ)).getD j .abort = (X.getD j .abort).isub σ := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases X[j]? with _ | a <;> rfl
    have a1 := hZZ j hj
    rw [hgx] at a1
    exact RE2.trans hW (RT2.refl hW hXT TX) a1 q1
  sorry

end core

end

end Model.Whnf
