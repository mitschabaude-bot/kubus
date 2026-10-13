import Model.Canon.Kan
import Model.Canon.ArgConv

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
  data : ∀ d < n, ∀ (D : DataDecl), S[d]? = some (.data D) → ∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ k (ps args : List Tm),
    ps.length = D.params.length →
    (∀ j (hj : j < ps.length) (hj' : j < D.params.length), RE S k (D.params[j].substList (ps.take j).reverse) ps[j]) →
    args.length < C.args.length → C.isRec args.length = false →
    (∀ i (hi : i < args.length), C.isRec i = false →
      RE S k ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ ps.reverse)) args[i]) →
    RT S k ((C.argTy d D.params.length args.length).substList (args.reverse ++ ps.reverse))

/-- Computability of the elements of a telescope, instantiated by a substitution. -/
def TeleCompS (S : Sig) (k : ℕ) (γ : ℕ → Tm) (τ : ℕ → I) : Tm → List Tm → List Tm → Prop
  | .tnil, [], _ => True
  | .tcons a as, A :: Δ, prev => RE S k ((A.substList prev).subst γ τ) (a.subst γ τ) ∧ TeleCompS S k γ τ as Δ (a :: prev)
  | _, _, _ => False



theorem tele_length {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {ts : Tm} {Δ prev : List Tm}, HasTele0 S Ψ Φ Γ ts Δ prev →
    ts.toList.length = Δ.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ h1 => by simp only [Tm.toList, List.length_cons]; rw [tele_length h1]

theorem teleCompS_get {γ : ℕ → Tm} {τ : ℕ → I} : ∀ {ts : Tm} {Δ prev : List Tm}, TeleCompS S k γ τ ts Δ prev →
    ∀ j (hj : j < ts.toList.length) (hΔ : j < Δ.length),
      RE S k ((Δ[j].substList ((ts.toList.take j).reverse ++ prev)).subst γ τ) (ts.toList[j].subst γ τ)
  | .tcons a as, A :: Δ, prev, ⟨h1, h2⟩ => fun j hj hΔ => by
    cases j with
    | zero => simpa [Tm.toList] using h1
    | succ j =>
      have := teleCompS_get h2 j (by simp [Tm.toList] at hj; omega) (by simp at hΔ; omega)
      simpa [Tm.toList, List.take_succ_cons, List.reverse_cons, List.append_assoc] using this
  | .tnil, [], _, _ => fun j hj => by simp [Tm.toList] at hj
  | .tnil, _ :: _, _, h => h.elim
  | .tcons _ _, [], _, h => h.elim

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
    have hty : HasTy S k .one [] (.transp (A.subst (dupS c.γ) (I.up c.σ.τ)) (φ.subst c.σ.τ) (a.subst c.γ c.σ.τ))
        ((A.subst (dupS c.γ) (I.up c.σ.τ)).dinst .one) := by
      have := c.ty hW (HasTy0.transp h0 h1 h2 h3); rwa [dinst_subst] at this
    have hA := (RE_univ_iff hW).1 (fund_ty h0 hc.1 (k + 1) (c.up hW))
    have ha := fund_ty h3 hc.2 k c
    rw [dinst_subst] at ha ⊢
    exact kan_transp hW (l := l) hA.2.2 hty ha
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => fun hc k c => by
    have hty : HasTy S k .one [] (.hcomp (A.subst c.γ c.σ.τ) (φ.subst c.σ.τ) (u.subst (dupS c.γ) (I.up c.σ.τ))
        (a.subst c.γ c.σ.τ)) (A.subst c.γ c.σ.τ) := c.ty hW (HasTy0.hcomp h0 h1 h2 h3 h4)
    have hA := (RE_univ_iff hW).1 (fund_ty h0 hc.1 k c)
    refine kan_hcomp hW hA.2.2 hty (fun k' σ r hr hh => ?_) (fund_ty h3 hc.2.2 k c)
    have hface : I.Entails .one (φ.subst (c.restr hW σ).σ.τ) := by
      rw [show φ.subst (c.restr hW σ).σ.τ = (φ.subst c.σ.τ).subst σ.τ from (I_subst_subst _ _ _).symm]
      exact entails_of_holds (I.scoped_subst (I.scoped_subst h1 c.σ.sc) σ.sc) hh
    have ih := fund_ty h2 hc.2.1 k' (((c.restr hW σ).cof hface).cons r hr)
    have eA : A.dshift.subst (((c.restr hW σ).cof hface).cons r hr).γ (((c.restr hW σ).cof hface).cons r hr).σ.τ =
        (A.subst c.γ c.σ.τ).isub σ := by
      show A.dshift.subst (c.restr hW σ).γ (consI r (c.restr hW σ).σ.τ) = _
      rw [dshift_consI, CSub.restr_subst]
    have eu : u.subst (((c.restr hW σ).cof hface).cons r hr).γ (((c.restr hW σ).cof hface).cons r hr).σ.τ =
        ((u.subst (dupS c.γ) (I.up c.σ.τ)).isub σ.up).dinst r := CSub.cons_restr_subst hW c σ r hr u
    rw [eA, eu] at ih; exact ih
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => fun hc k c => by
    sorry
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => fun hc k c => by
    sorry
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => fun hc k c => by
    have hty : HasTy S k .one [] (.data d (ps.subst c.γ c.σ.τ)) (.univ D.level) :=
      c.ty hW (HasTy0.data h0 h1 h2)
    have hpl := tele_isList h2
    have hpl' : ps.subst c.γ c.σ.τ = Tm.ofList (ps.subst c.γ c.σ.τ).toList := isList_subst hpl _ _
    have hpsl : ps.toList.length = D.params.length := by simpa using tele_length h2
    have hS := sigClosed_of_wfSig hW
    show RE S k (.univ D.level) (.data d (ps.subst c.γ c.σ.τ))
    refine RE_univ_of hW hty (RT_data_of hW h0 hty hpl' fun k' σ c' C hC args hlt hnr hpt => ?_)
    have iht := fund_tele h2 hc.2 k' (c.restr hW σ)
    have e : (ps.subst c.γ c.σ.τ).isub σ = ps.subst (c.restr hW σ).γ (c.restr hW σ).σ.τ :=
      (CSub.restr_subst hW c ps σ).symm
    rw [e] at hpt ⊢
    refine hH.data d hc.1 D h0 c' C hC k' _ args (by rw [toList_subst hpl]; simpa using hpsl) (fun j hj hj' => ?_)
      hlt hnr hpt
    have hj0 : j < ps.toList.length := by rw [toList_subst hpl] at hj; simpa using hj
    have h := teleCompS_get iht j hj0 hj'
    have hcl : (D.params[j]).closedB ((ps.toList.take j).reverse ++ []).length 0 = true := by
      simpa [Nat.min_eq_left hj0.le] using params_closed hS h0 j _ (List.getElem?_eq_getElem hj')
    rw [substList_subst hcl, List.append_nil, List.map_reverse, List.map_take, ← toList_subst hpl] at h
    simpa [toList_subst hpl] using h
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => fun hc k c' => by
    have iha := fund_tele h5 hc.2.2 k c'
    have hpsT : HasTy S k .one [] (.data d (ps.subst c'.γ c'.σ.τ)) (.univ D.level) := c'.ty hW h3
    have hal := tele_isList h5
    have hlen := tele_length h5
    simp only [Ctor.argTys, List.length_map, List.length_range] at hlen
    have hpl' : ps.subst c'.γ c'.σ.τ = Tm.ofList (ps.subst c'.γ c'.σ.τ).toList := isList_subst h2 _ _
    have hpsl : ps.toList.length = D.params.length := by
      have := tele_length h4; simpa using this
    have hsyn := ((sigOK_of_wfSig _ S rfl hW).2 d D h0).1
    have hty : HasTy S k .one [] (.con d c (ps.subst c'.γ c'.σ.τ) (args.subst c'.γ c'.σ.τ)
        (rs.map (·.subst c'.σ.τ))) (.data d (ps.subst c'.γ c'.σ.τ)) := c'.ty hW (HasTy0.con h0 h1 h2 h3 h4 h5 h6 h7)
    show RE S k (.data d (ps.subst c'.γ c'.σ.τ)) (.con d c (ps.subst c'.γ c'.σ.τ) (args.subst c'.γ c'.σ.τ)
      (rs.map (·.subst c'.σ.τ)))
    have hal' : args.subst c'.γ c'.σ.τ = Tm.ofList (args.toList.map (·.subst c'.γ c'.σ.τ)) := by
      conv_lhs => rw [hal]
      exact ofList_subst _ _ _
    rw [hal'] at hty ⊢
    have hargC : ∀ j (hj : j < args.toList.length),
        RE S k ((C.argTy d D.params.length j).substList
          (((args.toList.map (·.subst c'.γ c'.σ.τ)).take j).reverse ++ (ps.subst c'.γ c'.σ.τ).toList.reverse))
          ((args.toList.map (·.subst c'.γ c'.σ.τ))[j]'(by simpa using hj)) := by
      intro j hj
      have h := teleCompS_get iha j hj (by simp [Ctor.argTys]; omega)
      simp only [Ctor.argTys, List.getElem_map, List.getElem_range] at h
      have hcl : (C.argTy d D.params.length j).closedB
          (((args.toList.take j).reverse ++ ps.toList.reverse)).length 0 = true := by
        simp only [List.length_append, List.length_reverse, List.length_take, hpsl]
        rw [Nat.min_eq_left hj.le]
        unfold Ctor.argTy; split
        · rename_i A hA
          have := (hsyn.2.2.1 c C h1 j A hA).1
          rw [Nat.add_comm]; exact this
        · rw [Nat.add_comm]; exact paramVars_closed _ _
      rw [substList_subst hcl, List.map_append, List.map_reverse, List.map_reverse, ← toList_subst h2] at h
      simp only [List.getElem_map, List.map_take]
      rwa [List.map_take] at h
    refine RE_con hW h0 hpsT hpl' h1 (by simp; omega) (by simp [h6]) (fun r hr => ?_) hty (fun j hj hr => ?_)
      (fun j hj hr => hargC j (by simpa using hj))
    · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr; exact I.scoped_subst (h7 r0 hr0) c'.σ.sc
    · have := hargC j (by simpa using hj)
      have harg : C.argTy d D.params.length j = .data d (Ctor.paramVars D.params.length j) := by
        have hjC : j < C.args.length := by simp at hj; omega
        cases h' : C.args[j]'hjC with
        | point A => simp [Ctor.isRec, List.getElem?_eq_getElem hjC, h'] at hr
        | recur => simp [Ctor.argTy, List.getElem?_eq_getElem hjC, h']
      rw [harg, Tm.substList] at this
      rw [show (Tm.data d (Ctor.paramVars D.params.length j)).subst _ I.var =
          Tm.data d ((Ctor.paramVars D.params.length j).substList _) from rfl] at this
      have hjl : j < args.toList.length := by simpa using hj
      rwa [Meta.paramVars_substList (isList_subst h2 _ _) (by rw [toList_subst h2]; simp [hpsl])
        (by rw [List.length_reverse, List.length_take, List.length_map]; exact Nat.min_eq_left hjl.le)] at this
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => fun hc k c => by
    have iht := fund_ty h9
    sorry

theorem fund_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ts.ConstsLt n → ∀ k (c : CSub S Ψ Φ Γ k),
    TeleCompS S k c.γ c.σ.τ ts Δ prev
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => fun _ k c => trivial
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => fun hc k c =>
    ⟨fund_ty h0 hc.1 k c, fund_tele h1 hc.2 k c⟩

end

end

end Model.Canon
