import Model.Canon.Formers

/-!
# Canonicity: the fundamental lemma

Every typed term, instantiated by a computable substitution (an interval substitution into a
stage satisfying the face, and computable closed terms for the variables), is computable at its
instantiated type. By induction on minimal typing derivations; the definitions and the
declarations of inductive types are computable by an outer induction on their index in the
signature (`Hyp`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The definitions and inductive types below `n` are computable. -/
structure Hyp (S : Sig) (n : ℕ) : Prop where
  defn : ∀ i < n, ∀ t A, S[i]? = some (.defn t A) → ∀ k, RE S k A t

/-- Computability of the elements of a telescope. -/
def TeleComp (S : Sig) (k : ℕ) : Tm → List Tm → List Tm → Prop
  | .tnil, [], _ => True
  | .tcons a as, A :: Δ, prev => RE S k (A.substList prev) a ∧ TeleComp S k as Δ (a :: prev)
  | _, _, _ => False


variable (hW : WfSig S) {n : ℕ} (hH : Hyp S n)
include hW hH

mutual

theorem fund_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → t.ConstsLt n → ∀ k (c : CSub S Ψ Φ Γ k),
    RE S k (A.subst c.γ c.σ.τ) (t.subst c.γ c.σ.τ)
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 => fun _ k c => c.look x A h1
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => fun hc k c => by
    have ih := fund_ty h0 hc k c
    exact ih.conv_ty hW (.inr ⟨l, c.eq hW h1⟩)
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 => fun hc k c => fund_ty h2 hc k (CSub.restrictTo h1 c)
  | @HasTy0.const _ Ψ Φ Γ i t A h0 h1 => fun hc k c => by
    obtain ⟨htc, hAc, -, -⟩ := hW.1 i t A h1
    have hA : A.subst c.γ c.σ.τ = A := closed_subst_id hAc (fun x hx => absurd hx (Nat.not_lt_zero _))
      (fun i hi => absurd hi (Nat.not_lt_zero _))
    have hty := c.ty hW (HasTy0.const h0 h1)
    rw [hA] at hty ⊢
    exact (hH.defn i hc t A h1 k).conv hW (TyEq.refl _) (EqTm.symm (EqTm.delta hty h1))
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 => fun _ k c => by
    have hty := c.ty hW (HasTy0.univ h0 h1)
    show (Comp S (semK S k (.univ (l + 1))) k k (Hom.id k)).el (.univ (l + 1)) (.univ l)
    have hsem : ∀ l', semK S k (.univ l') = univC k l' := fun l' => rfl
    rw [hsem, Comp_univC]
    dsimp only
    rw [hsem]
    have hmem : univC k l ∈ ZFSet.sep (WF (l + 1) k) (Vt (l + 1)) :=
      ZFSet.mem_sep.2 ⟨univC_mem_Vt (by unfold maxLevel at h0; omega), wf_univC⟩
    refine ⟨hty, ?_, TyEq.refl _, hmem, ?_⟩
    · rw [res_id (isKV_univC _), El_univC]; exact hmem
    · rw [Comp_univC]
      exact ⟨⟨⟨l, .inr rfl⟩, by rw [hsem, res_id (isKV_univC _)]⟩, TyEq.refl _⟩
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    have ih := fund_ty h1 hc k c
    have hty := c.ty hW (HasTy0.cumul h0 h1)
    have hsem : ∀ l', semK S k (.univ l') = univC k l' := fun l' => rfl
    show (Comp S (semK S k (.univ (l + 1))) k k (Hom.id k)).el (.univ (l + 1)) _
    change (Comp S (semK S k (.univ l)) k k (Hom.id k)).el (.univ l) _ at ih
    rw [hsem, Comp_univC] at ih ⊢
    dsimp only at ih ⊢
    obtain ⟨-, -, -, hm, hrt⟩ := ih
    have hm' := ZFSet.mem_sep.1 hm
    have hmem : semK S k (A.subst c.γ c.σ.τ) ∈ ZFSet.sep (WF (l + 1) k) (Vt (l + 1)) :=
      ZFSet.mem_sep.2 ⟨Vt_subset_succ l (by unfold maxLevel at h0; omega) hm'.1, hm'.2.cumul⟩
    refine ⟨hty, ?_, TyEq.refl _, hmem, hrt⟩
    rw [res_id (isKV_univC _), El_univC]; exact hmem
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 => fun hc k c => by
    have hpi : HasTy S k .one [] (.pi (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) (.univ l) :=
      c.ty hW (HasTy0.pi h0 h1)
    refine RE_univ_of hW hpi (RT_pi_intro hW hpi (fun k' σ => ?_) (fun k' σ a ha => ?_))
    · have := (RE_univ_iff hW).1 (fund_ty h0 hc.1 k' (c.restr hW σ))
      rw [CSub.restr_subst] at this; exact this.2.2
    · have ha' : RE S k' (A.subst (c.restr hW σ).γ (c.restr hW σ).σ.τ) a := by rw [CSub.restr_subst]; exact ha
      have := (RE_univ_iff hW).1 (fund_ty h1 hc.2 k' ((c.restr hW σ).ext hW A a ha'))
      rw [subst_up_isub_inst]; exact this.2.2
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 => fun hc k c => by
    have hpi : HasTy S k .one [] (.pi (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) (.univ l) := c.ty hW h0
    have hf : HasTy S k .one [] (.lam (A.subst c.γ c.σ.τ) (t.subst (Tm.up c.γ) c.σ.τ))
        (.pi (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) := c.ty hW (HasTy0.lam h0 h1)
    show RE S k (.pi (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ))
      (.lam (A.subst c.γ c.σ.τ) (t.subst (Tm.up c.γ) c.σ.τ))
    refine RE_pi_intro hW hpi hf fun k' σ a ha => ?_
    have ha' : RE S k' (A.subst (c.restr hW σ).γ (c.restr hW σ).σ.τ) a := by rw [CSub.restr_subst]; exact ha
    have ih := fund_ty h1 hc.2 k' ((c.restr hW σ).ext hW A a ha')
    have e : ((B.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a =
        B.subst ((c.restr hW σ).ext hW A a ha').γ ((c.restr hW σ).ext hW A a ha').σ.τ :=
      subst_up_isub_inst _ _ _ _ _
    have et : ((t.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a =
        t.subst ((c.restr hW σ).ext hW A a ha').γ ((c.restr hW σ).ext hW A a ha').σ.τ :=
      subst_up_isub_inst _ _ _ _ _
    have hpiσ := HasTy.isubS hW hpi σ
    have hfσ := HasTy.isubS hW hf σ
    rw [isub_pi] at hpiσ hfσ
    have happ := HasTy.app hfσ (Comp_el_typed ha).1
    have hbeta : EqTm S k' .one [] (.app ((Tm.lam (A.subst c.γ c.σ.τ) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ) a)
        (((t.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a) (((B.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a) := by
      have : (Tm.lam (A.subst c.γ c.σ.τ) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ =
          .lam ((A.subst c.γ c.σ.τ).isub σ) ((t.subst (Tm.up c.γ) c.σ.τ).isub σ) := by
        simp only [Tm.isub, Tm.subst, up_var]
      rw [this] at happ ⊢
      exact EqTm.piBeta happ
    rw [← e, ← et] at ih
    exact ih.conv hW (TyEq.refl _) (EqTm.symm hbeta)
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 => fun hc k c => by
    have ihf := fund_ty h0 hc.1 k c
    have iha := fund_ty h1 hc.2 k c
    rw [inst_subst]
    exact RE_pi_elim hW ihf iha
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 => fun hc k c => by
    have hsig : HasTy S k .one [] (.sigma (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) (.univ l) :=
      c.ty hW (HasTy0.sigma h0 h1)
    refine RE_univ_of hW hsig (RT_sigma_intro hW hsig (fun k' σ => ?_) (fun k' σ a ha => ?_))
    · have := (RE_univ_iff hW).1 (fund_ty h0 hc.1 k' (c.restr hW σ))
      rw [CSub.restr_subst] at this; exact this.2.2
    · have ha' : RE S k' (A.subst (c.restr hW σ).γ (c.restr hW σ).σ.τ) a := by rw [CSub.restr_subst]; exact ha
      have := (RE_univ_iff hW).1 (fund_ty h1 hc.2 k' ((c.restr hW σ).ext hW A a ha'))
      rw [subst_up_isub_inst]; exact this.2.2
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 => fun hc k c => by
    have hsig : HasTy S k .one [] (.sigma (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) (.univ l) := c.ty hW h0
    have hp : HasTy S k .one [] (.pair (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))
        (.sigma (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ)) := c.ty hW (HasTy0.pair h0 h1 h2)
    show RE S k (.sigma (A.subst c.γ c.σ.τ) (B.subst (Tm.up c.γ) c.σ.τ))
      (.pair (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))
    have iha := fund_ty h1 hc.1 k c
    have ihb := fund_ty h2 hc.2 k c
    rw [inst_subst] at ihb
    have hf : EqTm S k .one [] (.fst (.pair (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))) (a.subst c.γ c.σ.τ)
        (A.subst c.γ c.σ.τ) := EqTm.fstBeta (HasTy.fst hp)
    have hB := HasTy.sigmaCod hsig
    have hBeq : EqTm S k .one [] ((B.subst (Tm.up c.γ) c.σ.τ).inst (a.subst c.γ c.σ.τ))
        ((B.subst (Tm.up c.γ) c.σ.τ).inst (.fst (.pair (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ)))) (.univ l) :=
      EqTm.subst (EqTm.refl hB) (EqTm.symm hf)
    refine RE_sigma_intro hW hsig hp (iha.conv hW (TyEq.refl _) (EqTm.symm hf)) ?_
    exact ihb.conv hW (.inr ⟨l, hBeq⟩) (EqTm.symm (EqTm.sndBeta (HasTy.snd hp)))
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 => fun hc k c => (RE_sigma_elim hW (fund_ty h0 hc k c)).1
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 => fun hc k c => by
    rw [inst_subst]; exact (RE_sigma_elim hW (fund_ty h0 hc k c)).2
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 => fun hc k c => by
    have hpath : HasTy S k .one [] (.path (A.subst (dupS c.γ) (I.up c.σ.τ)) (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))
        (.univ l) := c.ty hW (HasTy0.path h0 h1 h2)
    refine RE_univ_of hW hpath (RT_path_intro hW hpath (fun k' σ => ?_) ?_ ?_)
    · have := (RE_univ_iff hW).1 (fund_ty h0 hc.1 (k' + 1) ((c.restr hW σ).up hW))
      rw [CSub.up_restr_subst] at this; exact this.2.2
    · have := fund_ty h1 hc.2.1 k c; rwa [dinst_subst] at this
    · have := fund_ty h2 hc.2.2 k c; rwa [dinst_subst] at this
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 => fun hc k c => by
    have hpath : HasTy S k .one [] (.path (A.subst (dupS c.γ) (I.up c.σ.τ)) (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))
        (.univ l) := c.ty hW h0
    have hp : HasTy S k .one [] (.plam (t.subst (dupS c.γ) (I.up c.σ.τ)))
        (.path (A.subst (dupS c.γ) (I.up c.σ.τ)) (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ)) :=
      c.ty hW (HasTy0.plam h0 h1 h2 h3)
    show RE S k (.path (A.subst (dupS c.γ) (I.up c.σ.τ)) (a.subst c.γ c.σ.τ) (b.subst c.γ c.σ.τ))
      (.plam (t.subst (dupS c.γ) (I.up c.σ.τ)))
    refine RE_path_intro hW hpath hp fun k' σ r hr => ?_
    have ih := fund_ty h1 hc k' ((c.restr hW σ).cons r hr)
    rw [CSub.cons_restr_subst, CSub.cons_restr_subst] at ih
    have hpσ := HasTy.isubS hW hp σ
    rw [isub_path] at hpσ
    have happ := HasTy.papp hpσ hr
    exact ih.conv hW (TyEq.refl _) (EqTm.symm (EqTm.pathBeta happ))
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 => fun hc k c => by
    rw [dinst_subst]
    exact RE_path_elim hW (fund_ty h0 hc k c) _ (I.scoped_subst h1 c.σ.sc)
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    have hipi : HasTy S k .one [] (.ipi (A.subst (dupS c.γ) (I.up c.σ.τ))) (.univ l) := c.ty hW (HasTy0.ipi h0 h1)
    refine RE_univ_of hW hipi (RT_ipi_intro hW hipi fun k' σ => ?_)
    have := (RE_univ_iff hW).1 (fund_ty h1 hc (k' + 1) ((c.restr hW σ).up hW))
    rw [CSub.up_restr_subst] at this; exact this.2.2
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 => fun hc k c => by
    have hipi : HasTy S k .one [] (.ipi (A.subst (dupS c.γ) (I.up c.σ.τ))) (.univ l) := c.ty hW h0
    have hp : HasTy S k .one [] (.plam (t.subst (dupS c.γ) (I.up c.σ.τ))) (.ipi (A.subst (dupS c.γ) (I.up c.σ.τ))) :=
      c.ty hW (HasTy0.ilam h0 h1)
    show RE S k (.ipi (A.subst (dupS c.γ) (I.up c.σ.τ))) (.plam (t.subst (dupS c.γ) (I.up c.σ.τ)))
    refine RE_ipi_intro hW hipi hp fun k' σ r hr => ?_
    have ih := fund_ty h1 hc k' ((c.restr hW σ).cons r hr)
    rw [CSub.cons_restr_subst, CSub.cons_restr_subst] at ih
    have hpσ := HasTy.isubS hW hp σ
    rw [isub_ipi] at hpσ
    have happ := HasTy.iapp hpσ hr
    exact ih.conv hW (TyEq.refl _) (EqTm.symm (EqTm.pathBeta happ))
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 => fun hc k c => by
    rw [dinst_subst]
    exact RE_ipi_elim hW (fund_ty h0 hc k c) _ (I.scoped_subst h1 c.σ.sc)
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 => fun hc k c => by
    have hsp := c.ty hW (HasTy0.split h0 h1 h2 h3 h4 h5 h6)
    have hor : (ival (idEnv k) ((I.or φ ψ).subst c.σ.τ)).holds := entails_holds (ent_subst h2 _) c.face_holds
    rcases holds_or hor with hφ | hψ
    · have he := entails_of_holds (I.scoped_subst h0 c.σ.sc) hφ
      have ih := fund_ty h4 hc.1 k (c.cof he)
      exact ih.conv hW (TyEq.refl _) (EqTm.symm (EqTm.splitL he hsp))
    · have he := entails_of_holds (I.scoped_subst h1 c.σ.sc) hψ
      have ih := fund_ty h5 hc.2 k (c.cof he)
      exact ih.conv hW (TyEq.refl _) (EqTm.symm (EqTm.splitR he hsp))
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 => fun hc k c => by
    exfalso
    exact not_holds_zero (entails_holds (ent_subst h0 c.σ.τ) c.face_holds)
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => fun hc k c => by
    sorry
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => fun hc k c => by
    sorry
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => fun hc k c => by
    have ih := fund_tele h2
    sorry
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => fun hc k c => by
    have ihp := fund_tele h4
    have iha := fund_tele h5
    sorry
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => fun hc k c => by
    have iht := fund_ty h9
    sorry

theorem fund_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ts.ConstsLt n → ∀ k (c : CSub S Ψ Φ Γ k),
    TeleComp S k (ts.subst c.γ c.σ.τ) Δ (prev.map (·.subst c.γ c.σ.τ))
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => fun _ k c => by simp [TeleComp, Tm.subst]
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => fun hc k c => by
    have iha := fund_ty h0 hc.1 k c
    have ihas := fund_tele h1 hc.2 k c
    sorry

end

end

end Model.Canon
