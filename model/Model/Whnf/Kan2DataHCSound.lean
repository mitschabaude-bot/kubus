import Model.Whnf.Kan2DataCode

/-!
# Soundness of the `hcompCon` step

`HCSound` (`Sound.lean`) holds given canonical forms of the tubes of compositions at the restrictions
where their context and face hold (`TubeCanonΦ`, e.g. from the fundamental lemma through `tubeCanon_of`):
the premises of `hcompCon` hold for the tube's projections in any context (`hcompCon_premisesΦ`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

/-- Canonical forms of a tube at the restrictions where its context and its face hold. -/
def TubeCanonΦ (S : Sig) (k d : ℕ) (D : DataDecl) (ps : Tm) (Φ φ : I) (u : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (Φ.subst σ.τ)).holds →
    (ival (idEnv k') (φ.subst σ.τ)).holds →
    ∃ c' C' X', D.ctors[c']? = some C' ∧
      HasTele0 S k' .one [] (Tm.ofList X') (C'.argTys d D.params.length) (ps.isub σ).toList.reverse ∧
      EqTm S k' .one [] ((u.isub σ.up).dinst r) (.con d c' (ps.isub σ) (Tm.ofList X') []) (.data d (ps.isub σ))

/-- All canonical forms of a tube have the base's constructor. -/
theorem tube_tagΦ (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
    {k : ℕ} {Φ : I} (hΦs : Φ.Scoped k) {ps u : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} (hC : D.ctors[c]? = some C)
    (hd : HasTy S k Φ [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k) (hut : u.closedB 0 (k + 1) = true)
    (hside : EqTm S k (cof Φ φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hcan : TubeCanonΦ S k d D ps Φ φ u) {k' : ℕ} (σ : ISub k' k) {r : I} (hr : r.Scoped k')
    (hhΦ : (ival (idEnv k') (Φ.subst σ.τ)).holds)
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) {c' : ℕ} {C' : Ctor} {X' : List Tm} (hC' : D.ctors[c']? = some C')
    (he : EqTm S k' .one [] ((u.isub σ.up).dinst r) (.con d c' (ps.isub σ) (Tm.ofList X') []) (.data d (ps.isub σ))) :
    c' = c := by
  have hS := sigClosed_of_wfSig hW
  have hpsc : ps.closedB 0 k = true := by simpa [Tm.closedB] using closed_ty (spec_to_minimal hW hd)
  have hΦσ := entails_of_holds (I.scoped_subst hΦs σ.sc) hhΦ
  have hdσ : HasTy S k' .one [] (.data d (ps.isub σ)) (.univ D.level) :=
    HasTy.restrict (Φ' := .one) trivial hΦσ (HasTy.isubF hW hΦs hd σ)
  -- the canonical form of the whole restricted line
  have hsh : ∀ {x : I}, x.Scoped k → (ival (idEnv k') (x.subst σ.τ)).holds →
      (ival (idEnv (k' + 1)) (x.subst σ.sh.τ)).holds := by
    intro x hxs hxh
    rw [holds_iff_entails (I.scoped_subst hxs σ.sh.sc)]
    rw [I_subst_congr_scoped (τ := fun i => (σ.τ i).shift) (fun i hi => by simp [ISub.sh, ISub.ofFun, hi]) hxs]
    rw [show (fun i => (σ.τ i).shift) = (fun i => (σ.τ i).subst fun j => .var (j + 1)) from rfl, ← I_subst_subst]
    exact ent_subst (entails_of_holds (I.scoped_subst hxs σ.sc) hxh) _
  obtain ⟨c1, C1, X1, hC1, -, e1⟩ := hcan (k' + 1) σ.sh (.var 0) (show 0 < k' + 1 by omega) (hsh hΦs hhΦ) (hsh hφs hh)
  rw [isub_sh_up_var hut, isub_sh hpsc] at e1
  -- its instances
  have inst : ∀ s : I, s.Scoped k' → EqTm S k' .one [] ((u.isub σ.up).dinst s)
      (.con d c1 (ps.isub σ) ((Tm.ofList X1).dinst s) []) (.data d (ps.isub σ)) := by
    intro s hs
    have := minimal_to_spec_eq (EqTm0.dsubst hS (Ψ := k') (Φ := .one) (Γ := []) (spec_to_minimal_eq hW e1) (r := s) hs)
    rw [show (Tm.con d c1 (ps.isub σ).dshift (Tm.ofList X1) []).dinst s =
        Tm.con d c1 ((ps.isub σ).dshift.dinst s) ((Tm.ofList X1).dinst s) [] from rfl,
      show (Tm.data d (ps.isub σ).dshift).dinst s = Tm.data d ((ps.isub σ).dshift.dinst s) from rfl,
      Meta.dshift_dinst] at this
    exact this
  have hd1 := HasTy.eqR he
  have tagr := con_tag hW hD hC1 hC' (nonHIT_ctor hH hC1).2 (nonHIT_ctor hH hC').2 hdσ hdσ
    (HasTy.eqR (inst r hr)) hd1 ((inst r hr).symm.trans he)
  -- at the start of the tube
  have hent : I.Entails .one ((cof Φ φ).subst σ.τ) :=
    ent_and_intro hΦσ (entails_of_holds (I.scoped_subst hφs σ.sc) hh)
  have hs0 := EqTm.restrict (Φ' := .one) trivial hent (EqTm.isubF hW (show (cof Φ φ).Scoped k from ⟨hΦs, hφs⟩) hside σ)
  rw [dinst_isub_end' _ (.inl rfl)] at hs0
  have e0 := (inst .zero trivial).symm.trans hs0
  have tag0 := con_tag hW hD hC1 hC (nonHIT_ctor hH hC1).2 (nonHIT_ctor hH hC).2 hdσ hdσ
    (HasTy.eqR (inst .zero trivial)) (HasTy.eqR hs0) e0
  rw [← tagr, tag0]

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
include hW hD hH hC

/-- On a face of the cofibration of a composition, the tube is the base's constructor, at
arguments which are the projections of the tube there. -/
theorem face_dataΦ {k : ℕ} {Φ : I} (hΦs : Φ.Scoped k) {ps u : Tm} {φ : I} {X : List Tm}
    (hd : HasTy S k Φ [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k)
    (hut : HasTy0 S (k + 1) (cof Φ φ).shift [] u (Tm.data d ps).dshift)
    (hside : EqTm S k (cof Φ φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hcan : TubeCanonΦ S k d D ps Φ φ u) {α : I.Face} (hα : α ∈ ((cof Φ φ).shift).faces) :
    ∃ X' : List Tm,
      HasTele0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (Tm.ofList X') (C.argTys d D.params.length)
        (ps.dshift.subst Tm.var (faceSub α)).toList.reverse ∧
      EqTm0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] u
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') []) (.data d ps.dshift) ∧
      EqTm0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (.data d ps.dshift)
        (.data d (ps.dshift.subst Tm.var (faceSub α))) (.univ D.level) ∧
      HasTy0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (.data d (ps.dshift.subst Tm.var (faceSub α)))
        (.univ D.level) := by
  have hS := sigClosed_of_wfSig hW
  have hΦs' : ((cof Φ φ).shift).Scoped (k + 1) := KubusCore.I.scoped_shift ⟨hΦs, hφs⟩
  have hcα := faces_consistent hα
  have hsc := faces_scoped hΦs' α hα
  have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
  have hΞs : (cof (cof Φ φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs', hsα⟩
  have hτ : ∀ i < k + 1, (faceSub α i).Scoped (k + 1) := fun i hi => by
    rcases faceSub_cases α i with ⟨e, _, h⟩ | ⟨_, h⟩
    · rw [h]; cases e <;> trivial
    · rw [h]; exact hi
  set ρ := ISub.ofFun (k + 1) (faceSub α) hτ with hρ
  have hpsc : ps.closedB 0 k = true := by simpa [Tm.closedB] using closed_ty (spec_to_minimal hW hd)
  have hpsd : ps.dshift.closedB 0 (k + 1) = true := by
    have := closed_ty (HasTy0.dwk hS (spec_to_minimal hW hd))
    simpa [Tm.closedB] using this
  have hPα : ps.dshift.subst Tm.var (faceSub α) = ps.isub ρ.tail := by
    rw [← dshift_isub_tail, hρ, isub_ofFun hpsd]
  have huc : u.closedB 0 (k + 1) = true := closed_ty hut
  have huα : u.subst Tm.var (faceSub α) = (u.isub ρ.tail.up).dinst (ρ.τ 0) := by
    rw [isub_up_dinst _ _ _ (ρ.sc 0 (by omega)), ISub.cons_tail, hρ, isub_ofFun huc]
  -- the faces hold at its endpoints
  have hfaceOf : ∀ {x : I}, x.Scoped k → I.Entails (I.ofFace α) x.shift → (ival (idEnv (k + 1)) (x.subst ρ.tail.τ)).holds := by
    intro x hxs h1
    rw [holds_iff_entails (I.scoped_subst hxs ρ.tail.sc)]
    have h2 := ent_trans (ent_ofFace_faceSub hcα) (ent_subst h1 (faceSub α))
    have e3 : x.shift.subst (faceSub α) = x.subst ρ.tail.τ := by
      rw [← I_shift_tail]
      exact I_subst_congr_scoped (fun i hi => by
        show faceSub α i = (if i < k + 1 then faceSub α i else .zero); rw [if_pos hi]) (KubusCore.I.scoped_shift hxs)
    rwa [e3] at h2
  have hface := hfaceOf hφs (ent_trans (ofFace_ent hα) (ent_and_right _ _))
  have hfaceΦ := hfaceOf hΦs (ent_trans (ofFace_ent hα) (ent_and_left _ _))
  obtain ⟨c', C', X', hC', hX', e'⟩ := hcan (k + 1) ρ.tail (ρ.τ 0) (ρ.sc 0 (by omega)) hfaceΦ hface
  have htag := tube_tagΦ hW hD hH hΦs hC hd hφs huc hside hcan ρ.tail (ρ.sc 0 (by omega)) hfaceΦ hface hC' e'
  subst htag; rw [hC] at hC'; cases hC'
  rw [← huα, ← hPα] at e'
  rw [← hPα] at hX'
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  have hent : I.Entails (cof (cof Φ φ).shift (I.ofFace α)) .one := ent_one _
  have hX'Ξ := HasTele0.restrict hΞs hent hX'
  have e'Ξ := EqTm0.restrict hΞs hent (spec_to_minimal_eq hW e')
  have hd1 : HasTy0 S (k + 1) (Φ.shift) (Ctx.dshift []) (Tm.data d ps).dshift (Tm.univ D.level).dshift :=
    HasTy0.dwk hS (spec_to_minimal hW hd)
  have hdΞ : HasTy0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (Tm.data d ps.dshift) (.univ D.level) :=
    HasTy0.restrict hΞs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hd1
  have e_u := face_all hW (.inl hdΞ) (HasTy0.restrict hΞs (ent_and_left _ _) hut) α hsc (ent_and_right _ _)
  have e_T := face_all hW (l := D.level) (.inr rfl) hdΞ α hsc (ent_and_right _ _)
  have hdα := (pre_eq hS hT hCt e_T).2.1
  exact ⟨X', hX'Ξ, e_u.trans (EqTm0.conv e'Ξ (EqTm0.symm e_T)), e_T, hdα⟩


/-- The premises of `hcompCon` for the tube's projections. -/
theorem hcompCon_premisesΦ {k : ℕ} {Φ : I} (hΦs : Φ.Scoped k) {ps u : Tm} {φ : I} {X : List Tm}
    (hd : HasTy S k Φ [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k)
    (hut : HasTy0 S (k + 1) (cof Φ φ).shift [] u (Tm.data d ps).dshift)
    (hside : EqTm S k (cof Φ φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hX : HasTele0 S k Φ [] (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse)
    (hcan : TubeCanonΦ S k d D ps Φ φ u) :
    HasTele0 S (k + 1) (cof Φ φ).shift [] (Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u))
      (C.argTys d D.params.length) ps.dshift.toList.reverse ∧
    EqTm0 S (k + 1) (cof Φ φ).shift [] u
      (.con d c ps.dshift (Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u)) [])
      (.data d ps.dshift) ∧
    EqTele0 S k (cof Φ φ) [] ((Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u)).dinst .zero)
      (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse ∧
    ∀ i (hi : i < X.length), EqTm0 S k (cof Φ φ) [] ((proj d D ps.dshift c C i u).dinst .zero) X[i]
      ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ ps.toList.reverse)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  have hΦs' : ((cof Φ φ).shift).Scoped (k + 1) := KubusCore.I.scoped_shift ⟨hΦs, hφs⟩
  have hd1 : HasTy0 S (k + 1) (cof Φ φ).shift [] (.data d ps.dshift) (.univ D.level) :=
    HasTy0.restrict hΦs' (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS (Φ := Φ) (Γ := []) (spec_to_minimal hW hd))
  have H' := PD.of hW hD hH hd1
  set uargs := (List.range C.args.length).map fun j => proj d D ps.dshift c C j u with huargs
  have hul : uargs.length = C.args.length := by simp [uargs]
  have huget : ∀ i (hi : i < uargs.length), uargs[i] = proj d D ps.dshift c C i u := by intro i hi; simp [uargs]
  -- facewise data
  have FD : ∀ α ∈ ((cof Φ φ).shift).faces, ∃ X' : List Tm,
      HasTele0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (Tm.ofList X') (C.argTys d D.params.length)
        (ps.dshift.subst Tm.var (faceSub α)).toList.reverse ∧
      EqTm0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] u
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') []) (.data d ps.dshift) ∧
      EqTm0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (.data d ps.dshift)
        (.data d (ps.dshift.subst Tm.var (faceSub α))) (.univ D.level) ∧
      HasTy0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) [] (.data d (ps.dshift.subst Tm.var (faceSub α)))
        (.univ D.level) := fun α hα => face_dataΦ hW hD hH hC hΦs hd hφs hut hside hcan hα
  -- the projections of the tube are a telescope
  have claim : ∀ j, j ≤ C.args.length → ∀ i (hi : i < j) (hi' : i < uargs.length),
      HasTy0 S (k + 1) (cof Φ φ).shift [] uargs[i]
        ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi hi'
      by_cases hij : i < j
      · exact ih (by omega) i hij hi'
      obtain rfl : i = j := by omega
      have hjC : i < C.args.length := by omega
      have hat : ∀ k' (hk : k' < (uargs.take i).length), k' < C.args.length →
          HasTy0 S (k + 1) (cof Φ φ).shift [] (uargs.take i)[k']
            ((C.argTy d D.params.length k').substList (((uargs.take i).take k').reverse ++ ps.dshift.toList.reverse)) := by
        intro k' hk _
        have hk' : k' < i := by simp at hk; omega
        rw [List.getElem_take, List.take_take, Nat.min_eq_left hk'.le]
        exact ih (by omega) k' hk' (by omega)
      have hR := argTy_inst_typed hS hW hD hC H'.hpsL H'.hpl H'.hpt H'.hdata H'.hw hat (j := i) (by simp; omega) hjC
      rw [List.take_take, Nat.min_self] at hR
      have hL : HasTy0 S (k + 1) (cof Φ φ).shift [] ((projQ d D ps.dshift c C i).inst u) (.univ D.level) :=
        HasTy0.subst hS (projQ_typedΓ hS hW H' hC hjC H'.hw) hut
      have e : EqTm0 S (k + 1) (cof Φ φ).shift [] ((projQ d D ps.dshift c C i).inst u)
          ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)) (.univ D.level) := by
        refine eq_local_faces hL hR fun α hα => ?_
        obtain ⟨X', hX', e_u, e_T, hdα⟩ := FD α hα
        have hsc := faces_scoped hΦs' α hα
        have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
        have hΞs : (cof (cof Φ φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs', hsα⟩
        have hent : I.Entails (cof (cof Φ φ).shift (I.ofFace α)) (I.ofFace α) := ent_and_right _ _
        have hΞe : I.Entails (cof (cof Φ φ).shift (I.ofFace α)) (cof Φ φ).shift := ent_and_left _ _
        have Hα := PD.of hW hD hH hdα
        have huΞ := HasTy0.restrict hΞs hΞe hut
        have hd1Ξ := HasTy0.restrict hΞs hΞe hd1
        have e_uu := face_all hW (.inl hd1Ξ) huΞ α hsc hent
        have e_uαc := EqTm0.conv (e_uu.symm.trans e_u) e_T
        have hX'l : X'.length = C.args.length := by
          have := Meta.tele_length hX'; rwa [toList_ofList, argTys_length] at this
        set Y := (List.range C.args.length).map fun i' =>
          proj d D (ps.dshift.subst Tm.var (faceSub α)) c C i' (u.subst Tm.var (faceSub α)) with hY
        have hYl : Y.length = X'.length := by simp [Y, hX'l]
        have hYX : ∀ i' (h1 : i' < X'.length) (h2 : i' < Y.length), EqTm0 S (k + 1)
            (cof (cof Φ φ).shift (I.ofFace α)) [] Y[i'] X'[i']
            ((C.argTy d D.params.length i').substList ((X'.take i').reverse ++
              (ps.dshift.subst Tm.var (faceSub α)).toList.reverse)) := by
          intro i' h1 h2
          have := proj_canon hS hW Hα hC hX' e_uαc (i := i') (by omega)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
          simpa [Y] using this
        have tc := tele_conv hW hD hC Hα.hpsL Hα.hpt Hα.hdata hX' hYl hYX
        have a1 := face_all hW (l := D.level) (.inr rfl) (HasTy0.restrict hΞs hΞe hL) α hsc hent
        rw [inst_dsubst, projQ_dsubst hS hD hC hjC H'.hpsL H'.hpl] at a1
        obtain ⟨hua, hca, -⟩ := pre_eq hS hT hCt e_uαc
        have a2 := HasTy0.inst_congr hS (projQ_typed hS hW Hα hC hjC) hua hca e_uαc
        have a3 := projQ_con hS hW Hα hC hjC Hα.hw hC hX'
        rw [if_pos rfl] at a3
        have a4 := (tc.2.2 i (by omega)).symm
        have a5 : (C.argTy d D.params.length i).substList ((Y.take i).reverse ++
            (ps.dshift.subst Tm.var (faceSub α)).toList.reverse) =
            ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)).subst
              Tm.var (faceSub α) := by
          have hcl := argTy_closed hS hD hC i
          rw [substList_subst (by simpa [H'.hpl, hul, Nat.min_eq_left hjC.le, Nat.add_comm] using hcl),
            List.map_append, toList_subst H'.hpsL, List.map_reverse, List.map_reverse]
          congr 3
          apply List.ext_getElem (by simp [Y, uargs])
          intro i' h1 h2
          simp only [Y, uargs, List.getElem_take, List.getElem_map, List.getElem_range]
          rw [proj_dsubst hS hD hC (by simp at h1; omega) H'.hpsL H'.hpl]
        have a6 := (face_all hW (l := D.level) (.inr rfl) (HasTy0.restrict hΞs hΞe hR) α hsc hent).symm
        rw [← a5] at a6
        exact a1.trans (a2.trans (a3.trans (a4.trans a6)))
      rw [huget i hi']
      exact HasTy0.conv (proj_typed hS hW H' hC hjC H'.hw hut) e
  have hdims := (nonHIT_ctor hH hC).1
  have G1 : HasTele0 S (k + 1) (cof Φ φ).shift [] (Tm.ofList uargs) (C.argTys d D.params.length)
      ps.dshift.toList.reverse := by
    refine HasTele0.ofList_of H'.hw uargs _ _ (by simp [hul, argTys_length]) (fun i a A ha hA => ?_)
    have hi := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    rw [argTys_get (by omega), Option.some.injEq] at hA; subst hA
    exact claim C.args.length (Nat.le_refl _) i (by omega) hi
  have hcon : HasTy0 S (k + 1) (cof Φ φ).shift [] (.con d c ps.dshift (Tm.ofList uargs) []) (.data d ps.dshift) :=
    HasTy0.con hD hC H'.hpsL H'.hdata H'.hpt G1 (by simp [hdims]) (by simp)
  refine ⟨G1, eq_local_faces hut hcon fun α hα => ?_, ?_, ?_⟩
  · obtain ⟨X', hX', e_u, e_T, hdα⟩ := FD α hα
    have hsc := faces_scoped hΦs' α hα
    have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
    have hΞs : (cof (cof Φ φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs', hsα⟩
    have hent : I.Entails (cof (cof Φ φ).shift (I.ofFace α)) (I.ofFace α) := ent_and_right _ _
    have hΞe : I.Entails (cof (cof Φ φ).shift (I.ofFace α)) (cof Φ φ).shift := ent_and_left _ _
    have Hα := PD.of hW hD hH hdα
    have huΞ := HasTy0.restrict hΞs hΞe hut
    have hd1Ξ := HasTy0.restrict hΞs hΞe hd1
    have e_uu := face_all hW (.inl hd1Ξ) huΞ α hsc hent
    have e_uαc := EqTm0.conv (e_uu.symm.trans e_u) e_T
    have hX'l : X'.length = C.args.length := by
      have := Meta.tele_length hX'; rwa [toList_ofList, argTys_length] at this
    set Y := (List.range C.args.length).map fun i' =>
      proj d D (ps.dshift.subst Tm.var (faceSub α)) c C i' (u.subst Tm.var (faceSub α)) with hY
    have hYl : Y.length = X'.length := by simp [Y, hX'l]
    have hYX : ∀ i' (h1 : i' < X'.length) (h2 : i' < Y.length), EqTm0 S (k + 1)
        (cof (cof Φ φ).shift (I.ofFace α)) [] Y[i'] X'[i']
        ((C.argTy d D.params.length i').substList ((X'.take i').reverse ++
          (ps.dshift.subst Tm.var (faceSub α)).toList.reverse)) := by
      intro i' h1 h2
      have := proj_canon hS hW Hα hC hX' e_uαc (i := i') (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
      simpa [Y] using this
    have tc := tele_conv hW hD hC Hα.hpsL Hα.hpt Hα.hdata hX' hYl hYX
    have b1 : EqTm0 S (k + 1) (cof (cof Φ φ).shift (I.ofFace α)) []
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') [])
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList Y) [])
        (.data d (ps.dshift.subst Tm.var (faceSub α))) :=
      EqTm0.con hD hC (HasTy0.con hD hC Hα.hpsL Hα.hdata Hα.hpt hX' (by simp [hdims]) (by simp))
        (HasTy0.con hD hC Hα.hpsL Hα.hdata Hα.hpt tc.1 (by simp [hdims]) (by simp)) (EqTele0.refl Hα.hpt)
        (EqTele0.ofList_of' Hα.hw X' Y _ _ (by simp [argTys_length, hX'l]) (by simp [argTys_length, Y])
          (fun i a a' A ha ha' hA => by
            have hi := (List.getElem?_eq_some_iff.1 ha).1
            obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
            obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha'
            rw [argTys_get (by omega), Option.some.injEq] at hA; subst hA
            exact EqTm0.symm (hYX i hi (by omega))))
        rfl (fun _ _ _ h => by simp at h)
    have b2 : (Tm.con d c ps.dshift (Tm.ofList uargs) []).subst Tm.var (faceSub α) =
        .con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList Y) [] := by
      show Tm.con d c _ ((Tm.ofList uargs).subst Tm.var (faceSub α)) [] = _
      rw [ofList_subst]
      congr 2
      apply List.ext_getElem (by simp [Y, uargs])
      intro i' h1 h2
      simp only [Y, uargs, List.getElem_map, List.getElem_range]
      rw [proj_dsubst hS hD hC (by simp [Y] at h2; omega) H'.hpsL H'.hpl]
    have b3 := face_all hW (.inl hd1Ξ) (HasTy0.restrict hΞs hΞe hcon) α hsc hent
    rw [b2] at b3
    exact e_u.trans ((EqTm0.conv b1 (EqTm0.symm e_T)).trans b3.symm)
  · have hd0 : HasTy0 S k (cof Φ φ) [] (.data d ps) (.univ D.level) :=
      HasTy0.restrict (show (cof Φ φ).Scoped k from ⟨hΦs, hφs⟩) (ent_and_left _ _) (spec_to_minimal hW hd)
    have H0 := PD.of hW hD hH hd0
    have hX0 := HasTele0.restrict (show (cof Φ φ).Scoped k from ⟨hΦs, hφs⟩) (ent_and_left _ _) hX
    have hside0 := spec_to_minimal_eq hW hside
    have hXl : X.length = C.args.length := by
      have := Meta.tele_length hX; rwa [toList_ofList, argTys_length] at this
    set Y0 := (List.range C.args.length).map fun i => proj d D ps c C i (u.dinst .zero) with hY0
    have e0 : (Tm.ofList uargs).dinst .zero = Tm.ofList Y0 := by
      rw [Tm.dinst, Tm.dsubst, ofList_subst]
      congr 1
      apply List.ext_getElem (by simp [Y0, uargs])
      intro i' h1 h2
      simp only [Y0, uargs, List.getElem_map, List.getElem_range]
      rw [proj_dsubst hS hD hC (by simp [Y0] at h2; omega) H'.hpsL H'.hpl]
      congr 1
      exact Meta.dshift_dinst ps .zero
    have hY0X : ∀ i (h1 : i < X.length) (h2 : i < Y0.length), EqTm0 S k (cof Φ φ) [] Y0[i] X[i]
        ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ ps.toList.reverse)) := by
      intro i h1 h2
      have := proj_canon hS hW H0 hC hX0 hside0 (i := i) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
      simpa [Y0] using this
    rw [e0]
    exact (tele_conv hW hD hC H0.hpsL H0.hpt H0.hdata hX0 (by simp [Y0, hXl]) hY0X).2.1
  · intro i hi
    have hX0 := HasTele0.restrict (show (cof Φ φ).Scoped k from ⟨hΦs, hφs⟩) (ent_and_left _ _) hX
    have hXl : X.length = C.args.length := by
      have := Meta.tele_length hX; rwa [toList_ofList, argTys_length] at this
    have := proj_canon hS hW (PD.of hW hD hH (HasTy0.restrict (show (cof Φ φ).Scoped k from ⟨hΦs, hφs⟩)
      (ent_and_left _ _) (spec_to_minimal hW hd))) hC hX0 (spec_to_minimal_eq hW hside) (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [Tm.dinst, Tm.dsubst, proj_dsubst hS hD hC (by omega) H'.hpsL H'.hpl, ← Tm.dsubst, ← Tm.dinst,
      Meta.dshift_dinst ps .zero]
    exact this

end

/-- A `hcomp` step at an inductive type whose base is normal: `hcompCon`. -/
theorem step_hcomp_data_some {d : ℕ} {ps u a t' : Tm} {φ : I} (hn : I.entails .one φ = false)
    (ha : step S a = none) (hs : step S (.hcomp (.data d ps) φ u a) = some t') :
    ∃ D c C qs args, S[d]? = some (.data D) ∧ D.isHIT = false ∧ D.ctors[c]? = some C ∧
      a = .con d c qs args [] ∧
      t' = .con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps) ps.dshift.toList φ 0 []
        ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u) args.toList)) [] := by
  simp only [step, hn, ha] at hs
  split at hs
  · rename_i h; cases h
  · split at hs
    · rename_i D hD
      split at hs
      · cases hs
      · rename_i hH
        split at hs
        all_goals try cases hs
        rename_i d' c q args
        split at hs
        · cases hs
        · rename_i hdd
          split at hs
          · rename_i C hC
            cases hs
            have : d' = d := by simpa using hdd
            subst this
            exact ⟨D, c, C, q, args, hD, by simpa using hH, hC, rfl, rfl⟩
          · cases hs
    · cases hs

/-- Soundness of the `hcompCon` step, given canonical forms of the tubes of compositions at the
restrictions where their context and face hold. -/
theorem hcSound_of (hW : WfSig S)
    (hTC : ∀ {Ψ : ℕ} {Φ φ : I} {d : ℕ} {D : DataDecl} {ps u : Tm}, S[d]? = some (.data D) → D.isHIT = false →
      Φ.Scoped Ψ → φ.Scoped Ψ → HasTy0 S Ψ Φ [] (.data d ps) (.univ D.level) →
      HasTy0 S (Ψ + 1) (cof Φ φ).shift [] u (Tm.data d ps).dshift → TubeCanonΦ S Ψ d D ps Φ φ u) :
    HCSound S := by
  intro Ψ Φ d ps φ u a T t' hty hn ha hs
  obtain ⟨D, c, C, qs, args, hD, hH, hC, rfl, rfl⟩ := step_hcomp_data_some hn ha hs
  obtain ⟨l0, ⟨hdT, hφs, hu, hb, hside⟩, -⟩ := gen_hcomp hty rfl
  have hΦs : Φ.Scoped Ψ := scoped_of_wf (wf_of_ty hty)
  obtain ⟨D', hD', hPt⟩ := gen_data_tele hdT rfl
  rw [hD] at hD'; cases hD'
  have hdD : HasTy0 S Ψ Φ [] (.data d ps) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hPt
  obtain ⟨D0, C0, hD0, hC0, -, hargsL, htele, -, m, eq0⟩ := con_args hW hb hdT
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  obtain ⟨hI, -⟩ := gen_conF hb rfl
  obtain ⟨-, D1, C1, hD1, hC1, -, -, hqt, -, -, -⟩ := hI
  rw [hD] at hD1; cases hD1
  have eps : EqTele0 S Ψ Φ [] ps qs D.params [] := EqTele0.dataInj hD hPt hqt (EqTm0.symm eq0)
  have hc0 : HasTy0 S Ψ Φ [] (.con d c ps args []) (.data d ps) :=
    HasTy0.con hD hC (tele_isList hPt) hdD hPt htele (by simp [(nonHIT_ctor hH hC).1]) (by simp)
  have ec := EqTm0.con hD hC hc0 hb eps (EqTele0.refl htele) rfl (fun _ _ _ h => by simp at h)
  have hside' : EqTm0 S Ψ (cof Φ φ) [] (u.dinst .zero) (.con d c ps args []) (.data d ps) :=
    hside.trans (EqTm0.restrict (show (cof Φ φ).Scoped Ψ from ⟨hΦs, hφs⟩) (ent_and_left _ _) (EqTm0.symm ec))
  have hcan := hTC hD hH hΦs hφs hdD hu
  rw [hargsL] at hside' htele
  obtain ⟨G1, G2, G3, -⟩ := hcompCon_premisesΦ hW hD hH hC hΦs (minimal_to_spec hdD) hφs hu
    (minimal_to_spec_eq hside') htele hcan
  have hty' := hty
  rw [hargsL] at hty'
  have e := EqTm0.hcompCon (qs := qs) hD hH hC (tele_isList hPt) (args := Tm.ofList args.toList)
    (by rw [toList_ofList])
    (uargs := Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u))
    (by rw [toList_ofList]) htele G1 G2 G3 hty'
  simp only [toList_ofList] at e
  rw [hargsL]
  simpa only [toList_ofList] using e

/-- Canonical forms of a tube, from its relation to itself (at the restrictions where its context and
face hold) at its type, a restricted inductive type without path constructors. -/
theorem tubeCanonΦ_of (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
    {Ψ : ℕ} {Φ φ : I} (hΦs : Φ.Scoped Ψ) {ps u : Tm} (hd : HasTy S Ψ Φ [] (.data d ps) (.univ D.level))
    (hpp : ∀ k' (σ : ISub k' Ψ), (ival (idEnv k') (Φ.subst σ.τ)).holds →
      RT2 S k' (.data d (ps.isub σ)) (.data d (ps.isub σ)))
    (hrel : ∀ k' (σ : ISub k' Ψ) (r : I), r.Scoped k' → (ival (idEnv k') (Φ.subst σ.τ)).holds →
      (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (.data d (ps.isub σ)) ((u.isub σ.up).dinst r) ((u.isub σ.up).dinst r)) :
    TubeCanonΦ S Ψ d D ps Φ φ u := by
  intro k' σ r hr hhΦ hh
  have hdσ : HasTy S k' .one [] (.data d (ps.isub σ)) (.univ D.level) :=
    HasTy.restrict (Φ' := .one) trivial (entails_of_holds (I.scoped_subst hΦs σ.sc) hhΦ) (HasTy.isubF hW hΦs hd σ)
  have hc : (ps.isub σ).closedB 0 k' = true := data_closed hW hD hH hdσ
  have h := hrel k' σ r hr hhΦ hh
  rw [← isub_id_of_closed hc] at h
  obtain ⟨c, C, qs, Z, -, -, hC, -, -, hr1, -, -, -⟩ := dataLit_args hW hD hH hdσ (hpp k' σ hhΦ) (ISub.id k') h
  rw [isub_id_of_closed hc] at hr1
  obtain ⟨hX, he, -, -⟩ := con_retype hW hD hH hC hr1.2 (TyEq.refl _) hdσ
  exact ⟨c, C, Z, hC, hX, he⟩

end

end Model.Whnf
