import Model.Whnf.Boundary2ConRel

/-! # Constructor boundary expansion from per-face overlap agreement -/
set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d c : ℕ} {D : DataDecl} {P : Tm} {C : Ctor}

/-- Advance boundary expansion at one constructor, after establishing its constructor relation. -/
theorem conBnd_step (hW : WfSig S) (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hBT : BndTyping S d)
    (hP : HasTy S k .one [] (.data d P) (.univ D.level)) (hPP : RT2 S k (.data d P) (.data d P))
    (ih : ∀ c' < c, CRSt S d D k P c') (hCB : ∀ c' < c, CBRSt S d D c')
    (hcon : CRSt S d D k P c) (hC : D.ctors[c]? = some C)
    {Y : List Tm} {rs : List I} {kb : ℕ} {ψ : I} {b : Tm}
    (hb : C.bnd[kb]? = some (ψ, b)) (hent : I.Entails .one (Ctor.cofAt ψ rs))
    (hY : Y.length = C.args.length)
    (ht : HasTy S k .one [] (.con d c P (Tm.ofList Y) rs) (.data d P))
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C Y i) (Y.getD i .abort) (Y.getD i .abort)) :
    RE2 S k (.data d P) (.con d c P (Tm.ofList Y) rs) (Ctor.bndAt b P.toList Y rs) := by
  have hid := p_id hW hP
  have hPl := p_lit hW hD hP hPP
  have CI := con_inv hW hD hC ht hP
  have hrsl := CI.2.2.2.1
  obtain ⟨hψ, hbc, _, _⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
  have eqb : EqTm S k .one [] (.con d c P (Tm.ofList Y) rs) (Ctor.bndAt b P.toList Y rs) (.data d P) := by
    have he := EqTm.conBnd hD hC hb hent hPl (by simp [toList_ofList]) ht
    simpa only [toList_ofList] using he
  have RC : RE2 S k (.data d P) (.con d c P (Tm.ofList Y) rs) (.con d c P (Tm.ofList Y) rs) := by
    have R := hcon (ISub.id k) hC (by simpa only [hid] using ht) (by simpa only [hid] using ht)
      (forall2_ieq_refl rs) (by simpa only [hid] using hargs)
    simpa only [hid] using R
  have Rb := (bnd_norm_rel hW hD hH hBT hP hPP ih hCB hC hb hent hY ht hargs).2.2
  have RB := RE2.trans hW hPP Rb (RE2.symm hW hPP Rb)
  have iffR := fun (x y : Tm) => RE2_dataLit_iff hW hD hP (ISub.id k) (x := x) (y := y)
  rw [hid] at iffR
  obtain ⟨_, RCd⟩ := (iffR _ _).1 RC
  obtain ⟨_, RBd⟩ := (iffR _ _).1 RB
  cases RCd with
  | intro _ _ hcC _ =>
  cases RBd with
  | intro _ _ hcB _ =>
  refine (iffR _ _).2 ⟨⟨ht, HasTy.eqR eqb, eqb⟩, .intro eqb (fun k' κ => ?_) hcC hcB⟩
  have hPκ := HasTy.isubS hW hP κ
  have hPPκ := RT2.isub hW (tyCode_of_univ hW hP) hPP κ
  have htκ := HasTy.isubS hW ht κ
  rw [isub_conT] at htκ
  have hYκ : (Y.map (·.isub κ)).length = C.args.length := by simp [hY]
  have hargsκ := args_restr hW hD hP hPP (ISub.id k) hC hY hY (by simpa only [hid] using hargs) κ
  simp only [ISub.id_comp] at hargsκ
  have hentκ : I.Entails .one (Ctor.cofAt ψ (rs.map (·.subst κ.τ))) := by
    rw [← cofAt_subst κ.τ (by rwa [hrsl])]
    exact ent_one_subst hent κ.τ
  have hPlκ := (dataLit_rel hW hD hP hPP κ).2.2.2.2.2.1
  have hbc0 : b.closedB (P.toList.length + Y.length) rs.length = true := by
    rw [p_len hW hD hP, hY, hrsl]; exact hbc
  rw [isub_conT, bndAt_isubL hPl hbc0 κ]
  cases hf : firstBnd C.bnd (rs.map (·.subst κ.τ)) with
  | none => exact False.elim (firstBnd_none hf hb hentκ)
  | some b0 =>
    obtain ⟨kb0, ψ0, hb0, hent0⟩ := firstBnd_spec hf
    have R := overlap_rel hW hD hH hBT hPκ hPPκ (fun c' hc' => crst_restr (ih c' hc') κ) hCB
      hC hb0 hb hent0 hentκ hYκ htκ hargsκ
    have at0 := DR2.at_id hW (Θ := ΘK S D d k P) ((RE2_dataLit_iff hW hD hP κ).1 R).2
    have e0 : EqTm S k' .one [] (.con d c (P.isub κ) (Tm.ofList (Y.map (·.isub κ))) (rs.map (·.subst κ.τ)))
        (Ctor.bndAt b0 (P.isub κ).toList (Y.map (·.isub κ)) (rs.map (·.subst κ.τ))) (.data d (P.isub κ)) := by
      have he := EqTm.conBnd hD hC hb0 hent0 hPlκ (by simp [toList_ofList]) htκ
      simpa only [toList_ofList] using he
    have s0 : step S (.con d c (P.isub κ) (Tm.ofList (Y.map (·.isub κ))) (rs.map (·.subst κ.τ))) =
        some (Ctor.bndAt b0 (P.isub κ).toList (Y.map (·.isub κ)) (rs.map (·.subst κ.τ))) := by
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    simpa only [ISub.hom_id, Hom.id_comp] using DR2At.expandL hW at0 (.step s0 (.refl _)) e0

/-- The joint induction proves constructor relatedness and boundary expansion for each constructor. -/
theorem constructors_and_boundaries (hW : WfSig S) (hD : S[d]? = some (.data D))
    (hH : D.isHIT = true) (hBT : BndTyping S d) :
    ∀ c, (∀ {K : ℕ} {P : Tm}, HasTy S K .one [] (.data d P) (.univ D.level) →
      RT2 S K (.data d P) (.data d P) → CRSt S d D K P c) ∧ CBRSt S d D c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    have hcb : ∀ c' < c, CBRSt S d D c' := fun c' hc' => (ih c' hc').2
    have hcr : ∀ {K : ℕ} {P : Tm}, HasTy S K .one [] (.data d P) (.univ D.level) →
        RT2 S K (.data d P) (.data d P) → CRSt S d D K P c := by
      intro K P hP hPP
      exact con_rel_step hW hD hP hPP hH hBT (fun c' hc' => (ih c' hc').1 hP hPP) hcb
    refine ⟨hcr, ?_⟩
    intro k C P Y rs kb ψ b hC hb hent hP hPP hY ht hargs
    exact conBnd_step hW hD hH hBT hP hPP (fun c' hc' => (ih c' hc').1 hP hPP) hcb
      (hcr hP hPP) hC hb hent hY ht hargs

/-- The overlap check and prefix boundary typing supply both indexed HIT hypotheses. -/
theorem hitHyp_of_bndTyping (hW : WfSig S) {n : ℕ}
    (hBT : ∀ d, d < n → BndTyping S d) : HITHyp2 S n where
  conBnd hd hD hH hC hb hent hP hPP hY ht hargs :=
    (constructors_and_boundaries hW hD hH (hBT _ hd) _).2 hC hb hent hP hPP hY ht hargs
  bndTy hd := hBT _ hd

end
end Model.Whnf.Boundary2
