import Model.Whnf.Valid2Comp

/-!
# Typing and validity together

`VTy` (`VEq`) pairs a minimal typing (equation) derivation with its validity. The rules below build
both at once, so that derived terms (the contracta of the computation rules, transport along a line as
an equivalence) are shown valid by following their typing derivations step by step. The Kan rules take
the Kan property of the instances of the types they compose or transport in.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

/-- A typed and valid term. -/
structure VTy (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t A : Tm) : Prop where
  ty : HasTy0 S Ψ Φ Γ t A
  v : Valid2 S Ψ Φ Γ t t A

/-- A derivable and valid equation. -/
structure VEq (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t u A : Tm) : Prop where
  eq : EqTm0 S Ψ Φ Γ t u A
  v : Valid2 S Ψ Φ Γ t u A

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- The type of a typed term is closed. -/
theorem closedT_of_ty {t A : Tm} (h : HasTy0 S Ψ Φ Γ t A) : A.closedB Γ.length Ψ = true := by
  rcases pre_ty (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 h with ⟨l, h'⟩ | ⟨l, rfl, -⟩
  · exact closed_ty h'
  · rfl

/-! ### Structure -/

omit hW in
theorem VEq.refl' {t A : Tm} (h : VTy S Ψ Φ Γ t A) : VEq S Ψ Φ Γ t t A := ⟨EqTm0.refl h.ty, h.v⟩

theorem VEq.symm' {t u A : Tm} (h : VEq S Ψ Φ Γ t u A) : VEq S Ψ Φ Γ u t A :=
  ⟨EqTm0.symm h.eq, valid_symm hW h.v⟩

theorem VEq.trans' {t u v A : Tm} (h1 : VEq S Ψ Φ Γ t u A) (h2 : VEq S Ψ Φ Γ u v A) : VEq S Ψ Φ Γ t v A :=
  ⟨EqTm0.trans h1.eq h2.eq, valid_trans hW h1.v h2.v⟩

theorem VTy.conv' {t A B : Tm} {l : ℕ} (h : VTy S Ψ Φ Γ t A) (e : VEq S Ψ Φ Γ A B (.univ l)) : VTy S Ψ Φ Γ t B :=
  ⟨HasTy0.conv h.ty e.eq, valid_conv hW h.v e.v⟩

theorem VEq.conv' {t u A B : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ t u A) (e : VEq S Ψ Φ Γ A B (.univ l)) :
    VEq S Ψ Φ Γ t u B :=
  ⟨EqTm0.conv h.eq e.eq, valid_conv hW h.v e.v⟩

theorem VTy.restrict' {Φ' : I} {t A : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) (h : VTy S Ψ Φ Γ t A) :
    VTy S Ψ Φ' Γ t A :=
  ⟨HasTy0.restrict hs he h.ty, valid_restrict hW he h.v⟩

theorem VEq.restrict' {Φ' : I} {t u A : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) (h : VEq S Ψ Φ Γ t u A) :
    VEq S Ψ Φ' Γ t u A :=
  ⟨EqTm0.restrict hs he h.eq, valid_restrict hW he h.v⟩

theorem VTy.var' {x : ℕ} {A : Tm} (hw : Wf0 S Ψ Φ Γ) (h : Γ.lookup x = some A) : VTy S Ψ Φ Γ (.var x) A :=
  ⟨HasTy0.var hw h, valid_var hW h⟩

theorem VEq.cumul' {A B : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel) (h : VEq S Ψ Φ Γ A B (.univ l)) :
    VEq S Ψ Φ Γ A B (.univ (l + 1)) :=
  ⟨EqTm0.cumul hl h.eq, valid_cumul hW hl h.v⟩

theorem VEq.local' {t u A : Tm} {φ ψ : I} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ) (hor : I.Entails Φ (.or φ ψ))
    (ht : VTy S Ψ Φ Γ t A) (hu : VTy S Ψ Φ Γ u A) (h1 : VEq S Ψ (cof Φ φ) Γ t u A) (h2 : VEq S Ψ (cof Φ ψ) Γ t u A) :
    VEq S Ψ Φ Γ t u A :=
  ⟨EqTm0.local hφ hψ hor ht.ty hu.ty h1.eq h2.eq, valid_local hφ hψ hor h1.v h2.v⟩

theorem VEq.absurd' {t u A : Tm} (hz : I.Entails Φ .zero) (ht : HasTy0 S Ψ Φ Γ t A) (hu : HasTy0 S Ψ Φ Γ u A) :
    VEq S Ψ Φ Γ t u A :=
  ⟨EqTm0.absurd hz ht hu, valid_absurd hz⟩

theorem VEq.faceU' {t : Tm} {i : ℕ} {d : Bool} {l : ℕ} (hi : i < Ψ) (hent : I.Entails Φ (I.lit i d))
    (h : VTy S Ψ Φ Γ t (.univ l)) : VEq S Ψ Φ Γ t (t.dset i (I.ofDir d)) (.univ l) :=
  ⟨EqTm0.faceU hi hent h.ty, valid_face hW hi hent h.v⟩

theorem VEq.face' {t A : Tm} {i : ℕ} {d : Bool} {l : ℕ} (hi : i < Ψ) (hent : I.Entails Φ (I.lit i d))
    (hA : HasTy0 S Ψ Φ Γ A (.univ l)) (h : VTy S Ψ Φ Γ t A) : VEq S Ψ Φ Γ t (t.dset i (I.ofDir d)) A :=
  ⟨EqTm0.face hi hent hA h.ty, valid_face hW hi hent h.v⟩

/-! ### Formers -/

theorem VTy.app' {f a A B : Tm} (hf : VTy S Ψ Φ Γ f (.pi A B)) (ha : VTy S Ψ Φ Γ a A) :
    VTy S Ψ Φ Γ (.app f a) (B.inst a) :=
  ⟨HasTy0.app hf.ty ha.ty, valid_app hW hf.v ha.v⟩

theorem VEq.app' {f f' a a' A B : Tm} (hf : VEq S Ψ Φ Γ f f' (.pi A B)) (ha : VEq S Ψ Φ Γ a a' A) :
    VEq S Ψ Φ Γ (.app f a) (.app f' a') (B.inst a) :=
  ⟨EqTm0.app hf.eq ha.eq, valid_app hW hf.v ha.v⟩

theorem VTy.lam' {A B t : Tm} {l : ℕ} (hpi : VTy S Ψ Φ Γ (.pi A B) (.univ l)) (ht : VTy S Ψ Φ (A :: Γ) t B) :
    VTy S Ψ Φ Γ (.lam A t) (.pi A B) := by
  have h := HasTy0.lam hpi.ty ht.ty
  exact ⟨h, valid_lam hW hpi.v ht.v h h (.refl h)⟩

theorem VEq.lam' {A B t t' : Tm} {l : ℕ} (hpi : VTy S Ψ Φ Γ (.pi A B) (.univ l)) (ht : VEq S Ψ Φ (A :: Γ) t t' B) :
    VEq S Ψ Φ Γ (.lam A t) (.lam A t') (.pi A B) := by
  have e := EqTm0.lam hpi.ty ht.eq
  exact ⟨e, valid_lam hW hpi.v ht.v (presup hW e).1 (presup hW e).2 e⟩

theorem VTy.pair' {A B a b : Tm} {l : ℕ} (hsig : VTy S Ψ Φ Γ (.sigma A B) (.univ l)) (ha : VTy S Ψ Φ Γ a A)
    (hb : VTy S Ψ Φ Γ b (B.inst a)) : VTy S Ψ Φ Γ (.pair a b) (.sigma A B) := by
  have h := HasTy0.pair hsig.ty ha.ty hb.ty
  exact ⟨h, valid_pair hW hsig.v ha.v hb.v h h (.refl h)⟩

theorem VTy.fst' {p A B : Tm} (h : VTy S Ψ Φ Γ p (.sigma A B)) : VTy S Ψ Φ Γ (.fst p) A :=
  ⟨HasTy0.fst h.ty, valid_fst hW h.v⟩

theorem VTy.snd' {p A B : Tm} (h : VTy S Ψ Φ Γ p (.sigma A B)) : VTy S Ψ Φ Γ (.snd p) (B.inst (.fst p)) :=
  ⟨HasTy0.snd h.ty, valid_snd hW h.v⟩

theorem VTy.iapp' {p A : Tm} {r : I} (h : VTy S Ψ Φ Γ p (.ipi A)) (hr : r.Scoped Ψ) :
    VTy S Ψ Φ Γ (.papp p r) (A.dinst r) :=
  ⟨HasTy0.iapp h.ty hr, valid_iapp hW h.v hr hr (I_eq_refl _)⟩

theorem VEq.iapp' {p p' A : Tm} {r r' : I} (h : VEq S Ψ Φ Γ p p' (.ipi A)) (hr : r.Scoped Ψ) (hr' : r'.Scoped Ψ)
    (hE : I.Eq r r') : VEq S Ψ Φ Γ (.papp p r) (.papp p' r') (A.dinst r) :=
  ⟨EqTm0.iapp h.eq hr hr' hE, valid_iapp hW h.v hr hr' hE⟩

theorem VTy.ilam' {A t : Tm} {l : ℕ} (hipi : VTy S Ψ Φ Γ (.ipi A) (.univ l)) (ht : VTy S (Ψ + 1) Φ.shift Γ.dshift t A) :
    VTy S Ψ Φ Γ (.plam t) (.ipi A) := by
  have h := HasTy0.ilam hipi.ty ht.ty
  exact ⟨h, valid_ilam hW hipi.v ht.v h h (.refl h)⟩

theorem VEq.ilam' {A t t' : Tm} {l : ℕ} (hipi : VTy S Ψ Φ Γ (.ipi A) (.univ l))
    (ht : VEq S (Ψ + 1) Φ.shift Γ.dshift t t' A) : VEq S Ψ Φ Γ (.plam t) (.plam t') (.ipi A) := by
  have e := EqTm0.ilam hipi.ty ht.eq
  exact ⟨e, valid_ilam hW hipi.v ht.v (presup hW e).1 (presup hW e).2 e⟩

theorem VTy.papp' {p L a b : Tm} {r : I} (h : VTy S Ψ Φ Γ p (.path L a b)) (hr : r.Scoped Ψ) :
    VTy S Ψ Φ Γ (.papp p r) (L.dinst r) :=
  ⟨HasTy0.papp h.ty hr, valid_papp hW h.v hr hr (I_eq_refl _)⟩

theorem VEq.papp' {p p' L a b : Tm} {r r' : I} (h : VEq S Ψ Φ Γ p p' (.path L a b)) (hr : r.Scoped Ψ)
    (hr' : r'.Scoped Ψ) (hE : I.Eq r r') : VEq S Ψ Φ Γ (.papp p r) (.papp p' r') (L.dinst r) :=
  ⟨EqTm0.papp h.eq hr hr' hE, valid_papp hW h.v hr hr' hE⟩

theorem VTy.plam' {L a b t : Tm} {l : ℕ} (hpath : VTy S Ψ Φ Γ (.path L a b) (.univ l))
    (ht : VTy S (Ψ + 1) Φ.shift Γ.dshift t L) (h0 : VEq S Ψ Φ Γ (t.dinst .zero) a (L.dinst .zero))
    (h1 : VEq S Ψ Φ Γ (t.dinst .one) b (L.dinst .one)) : VTy S Ψ Φ Γ (.plam t) (.path L a b) := by
  have h := HasTy0.plam hpath.ty ht.ty h0.eq h1.eq
  exact ⟨h, valid_plam hW hpath.v ht.v h0.v h1.v h⟩

/-! ### Injectivity of type formers -/

theorem VEq.piInjDom' {A A' B B' : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l)) :
    VEq S Ψ Φ Γ A A' (.univ l) := by
  have e := EqTm0.piInjDom h.eq
  exact ⟨e, valid_piInjDom hW h.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.piInjCod' {A A' B B' a : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l))
    (ha : VTy S Ψ Φ Γ a A) : VEq S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  have e := EqTm0.piInjCod h.eq ha.ty
  exact ⟨e, valid_piInjCod hW h.v ha.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.sigmaInjDom' {A A' B B' : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l)) :
    VEq S Ψ Φ Γ A A' (.univ l) := by
  have e := EqTm0.sigmaInjDom h.eq
  exact ⟨e, valid_sigmaInjDom hW h.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.sigmaInjCod' {A A' B B' a : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l))
    (ha : VTy S Ψ Φ Γ a A) : VEq S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  have e := EqTm0.sigmaInjCod h.eq ha.ty
  exact ⟨e, valid_sigmaInjCod hW h.v ha.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.ipiInj' {A A' : Tm} {r : I} {l : ℕ} (h : VEq S Ψ Φ Γ (.ipi A) (.ipi A') (.univ l)) (hr : r.Scoped Ψ) :
    VEq S Ψ Φ Γ (A.dinst r) (A'.dinst r) (.univ l) := by
  have e := EqTm0.ipiInj h.eq hr
  exact ⟨e, valid_ipiInj hW h.v hr (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.sigmaEta' {A B p : Tm} (h : VTy S Ψ Φ Γ p (.sigma A B)) :
    VEq S Ψ Φ Γ p (.pair (.fst p) (.snd p)) (.sigma A B) := by
  have e := EqTm0.sigmaEta h.ty
  exact ⟨e, valid_sigmaEta hW h.v h.ty (presup hW e).2 e⟩

theorem VEq.piEta' {A B f : Tm} (h : VTy S Ψ Φ Γ f (.pi A B)) :
    VEq S Ψ Φ Γ f (.lam A (.app f.shift (.var 0))) (.pi A B) := by
  have e := EqTm0.piEta h.ty
  exact ⟨e, valid_piEta hW h.v h.ty (presup hW e).2 e⟩

theorem VEq.ipiEta' {A p : Tm} (h : VTy S Ψ Φ Γ p (.ipi A)) :
    VEq S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.ipi A) := by
  have e := EqTm0.ipiEta h.ty
  exact ⟨e, valid_ipiEta hW h.v h.ty (presup hW e).2 e⟩

theorem VEq.pathEta' {L a b p : Tm} (h : VTy S Ψ Φ Γ p (.path L a b)) :
    VEq S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.path L a b) := by
  have e := EqTm0.pathEta h.ty
  exact ⟨e, valid_pathEta hW h.v h.ty (presup hW e).2 e⟩

theorem VEq.pair' {A B a a' b b' : Tm} {l : ℕ} (hsig : VTy S Ψ Φ Γ (.sigma A B) (.univ l)) (ha : VEq S Ψ Φ Γ a a' A)
    (hb : VEq S Ψ Φ Γ b b' (B.inst a)) : VEq S Ψ Φ Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  have e := EqTm0.pair hsig.ty ha.eq hb.eq
  exact ⟨e, valid_pair hW hsig.v ha.v hb.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.fst' {A B p p' : Tm} (h : VEq S Ψ Φ Γ p p' (.sigma A B)) : VEq S Ψ Φ Γ (.fst p) (.fst p') A :=
  ⟨EqTm0.fst h.eq, valid_fst hW h.v⟩

theorem VEq.snd' {A B p p' : Tm} (h : VEq S Ψ Φ Γ p p' (.sigma A B)) :
    VEq S Ψ Φ Γ (.snd p) (.snd p') (B.inst (.fst p)) :=
  ⟨EqTm0.snd h.eq, valid_snd hW h.v⟩

/-! ### Systems -/

theorem VTy.split' {A t u : Tm} {φ ψ : I} {l : ℕ} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ)
    (hor : I.Entails Φ (.or φ ψ)) (hA : HasTy0 S Ψ Φ Γ A (.univ l)) (ht : VTy S Ψ (cof Φ φ) Γ t A)
    (hu : VTy S Ψ (cof Φ ψ) Γ u A) (htu : VEq S Ψ (cof (cof Φ φ) ψ) Γ t u A) : VTy S Ψ Φ Γ (.split φ t ψ u) A := by
  have h := HasTy0.split hφ hψ hor hA ht.ty hu.ty htu.eq
  exact ⟨h, valid_split hW hφ hψ hor ht.v hu.v htu.v h h⟩

theorem VEq.splitL' {A t u : Tm} {φ ψ : I} (hφ0 : I.Entails Φ φ) (h : VTy S Ψ Φ Γ (.split φ t ψ u) A) :
    VEq S Ψ Φ Γ (.split φ t ψ u) t A := by
  have e := EqTm0.splitL hφ0 h.ty
  exact ⟨e, valid_splitL hW hφ0 h.v h.ty (presup hW e).2⟩

theorem VEq.splitR' {A t u : Tm} {φ ψ : I} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ) (hψ0 : I.Entails Φ ψ)
    (h : VTy S Ψ Φ Γ (.split φ t ψ u) A) (hu : VTy S Ψ (cof Φ ψ) Γ u A) (htu : VEq S Ψ (cof (cof Φ φ) ψ) Γ t u A) :
    VEq S Ψ Φ Γ (.split φ t ψ u) u A := by
  have e := EqTm0.splitR hψ0 h.ty
  exact ⟨e, valid_splitR hW hφ hψ hψ0 hu.v htu.v h.ty (presup hW e).2⟩

/-! ### Kan operations -/

theorem VTy.transp' {A a : Tm} {φ : I} {l : ℕ}
    (hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)) (hφ : φ.Scoped Ψ)
    (hc : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (ha : VTy S Ψ Φ Γ a (A.dinst .zero)) : VTy S Ψ Φ Γ (.transp A φ a) (A.dinst .one) := by
  have h := HasTy0.transp hA.ty hφ hc.eq ha.ty
  exact ⟨h, valid_transp hW hφ (ent_refl _) (ent_refl _) hA.v hc.v ha.v h h (.refl h)⟩

theorem VEq.transp' {A A' a a' : Tm} {φ φ' : I} {l l' : ℕ}
    (hφ : φ.Scoped Ψ) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hty : HasTy0 S Ψ Φ Γ (.transp A φ a) (A.dinst .one)) (hty' : HasTy0 S Ψ Φ Γ (.transp A' φ' a') (A.dinst .one))
    (hA : VEq S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l))
    (hc : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l'))
    (ha : VEq S Ψ Φ Γ a a' (A.dinst .zero)) : VEq S Ψ Φ Γ (.transp A φ a) (.transp A' φ' a') (A.dinst .one) := by
  have e := EqTm0.transp hty hty' hA.eq h12 h21 ha.eq
  exact ⟨e, valid_transp hW hφ h12 h21 hA.v hc ha.v hty hty' e⟩

theorem VTy.hcomp' {A u a : Tm} {φ : I} {l : ℕ}
    (hA : VTy S Ψ Φ Γ A (.univ l)) (hφ : φ.Scoped Ψ) (hu : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift)
    (ha : VTy S Ψ Φ Γ a A) (hs : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) a A) : VTy S Ψ Φ Γ (.hcomp A φ u a) A := by
  have h := HasTy0.hcomp hA.ty hφ hu.ty ha.ty hs.eq
  exact ⟨h, valid_hcomp hW hφ (ent_refl _) (ent_refl _) hA.v hu.v ha.v hs.v hs.v h h (.refl h) (.refl hu.ty)⟩

theorem VEq.transpFace' {A a T : Tm} {φ : I} (hφ0 : I.Entails Φ φ) (h : VTy S Ψ Φ Γ (.transp A φ a) T) :
    VEq S Ψ Φ Γ (.transp A φ a) a T := by
  have e := EqTm0.transpFace hφ0 h.ty
  exact ⟨e, valid_transpFace hW hφ0 h.v h.ty (presup hW e).2⟩

theorem VEq.hcompFace' {A u a T : Tm} {φ : I} (hφ0 : I.Entails Φ φ) (h : VTy S Ψ Φ Γ (.hcomp A φ u a) T) :
    VEq S Ψ Φ Γ (.hcomp A φ u a) (u.dinst .one) T := by
  have e := EqTm0.hcompFace hφ0 h.ty
  exact ⟨e, valid_hcompFace hW hφ0 h.v h.ty (presup hW e).2⟩

/-! ### Structural rules -/

theorem VTy.dwk' {t A : Tm} (h : VTy S Ψ Φ Γ t A) : VTy S (Ψ + 1) Φ.shift Γ.dshift t.dshift A.dshift :=
  ⟨HasTy0.dwk (sigClosed_of_wfSig hW) h.ty,
    valid_dwk' (closed_ty h.ty) (closed_ty h.ty) (closedT_of_ty hW h.ty) (scoped_of_ty h.ty) h.v⟩

theorem VEq.dwk' {t u A : Tm} (h : VEq S Ψ Φ Γ t u A) : VEq S (Ψ + 1) Φ.shift Γ.dshift t.dshift u.dshift A.dshift :=
  ⟨EqTm0.dwk (sigClosed_of_wfSig hW) h.eq,
    valid_dwk' (closed_ty (presup hW h.eq).1) (closed_ty (presup hW h.eq).2) (closedT_of_ty hW (presup hW h.eq).1)
      (scoped_of_ty (presup hW h.eq).1) h.v⟩

theorem VTy.wk' {t A B : Tm} {l : ℕ} (hB : HasTy0 S Ψ Φ Γ B (.univ l)) (h : VTy S Ψ Φ Γ t A) :
    VTy S Ψ Φ (B :: Γ) t.shift A.shift :=
  ⟨HasTy0.wk (sigClosed_of_wfSig hW) hB h.ty, valid_wk B h.v⟩

theorem VEq.wk' {t u A B : Tm} {l : ℕ} (hB : HasTy0 S Ψ Φ Γ B (.univ l)) (h : VEq S Ψ Φ Γ t u A) :
    VEq S Ψ Φ (B :: Γ) t.shift u.shift A.shift :=
  ⟨EqTm0.wk (sigClosed_of_wfSig hW) hB h.eq, valid_wk B h.v⟩

theorem VTy.dsubst' {t A : Tm} (r : I) (hr : r.Scoped Ψ) (h : VTy S (Ψ + 1) Φ.shift Γ.dshift t A) :
    VTy S Ψ Φ Γ (t.dinst r) (A.dinst r) :=
  ⟨HasTy0.dsubst (sigClosed_of_wfSig hW) h.ty hr,
    valid_dinst' r hr (closed_ty h.ty) (closed_ty h.ty) (closedT_of_ty hW h.ty)
      (scoped_of_wf (wf_unshift (sigClosed_of_wfSig hW) (wf_of_ty h.ty))) h.v⟩

theorem VEq.dsubst' {t u A : Tm} (r : I) (hr : r.Scoped Ψ) (h : VEq S (Ψ + 1) Φ.shift Γ.dshift t u A) :
    VEq S Ψ Φ Γ (t.dinst r) (u.dinst r) (A.dinst r) :=
  ⟨EqTm0.dsubst (sigClosed_of_wfSig hW) h.eq hr,
    valid_dinst' r hr (closed_ty (presup hW h.eq).1) (closed_ty (presup hW h.eq).2)
      (closedT_of_ty hW (presup hW h.eq).1)
      (scoped_of_wf (wf_unshift (sigClosed_of_wfSig hW) (wf_of_eq h.eq))) h.v⟩

theorem VTy.subst' {A B t a : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l)) (h : VTy S Ψ Φ (A :: Γ) t B)
    (ha : VTy S Ψ Φ Γ a A) : VTy S Ψ Φ Γ (t.inst a) (B.inst a) :=
  ⟨HasTy0.subst (sigClosed_of_wfSig hW) h.ty ha.ty, valid_inst hW hA.v ha.v h.v⟩

theorem VTy.inst_congr' {A B t a a' : Tm} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l)) (h : VTy S Ψ Φ (A :: Γ) t B)
    (ha : VEq S Ψ Φ Γ a a' A) : VEq S Ψ Φ Γ (t.inst a) (t.inst a') (B.inst a) :=
  ⟨HasTy0.inst_congr (sigClosed_of_wfSig hW) h.ty (presup hW ha.eq).1 (presup hW ha.eq).2 ha.eq,
    valid_inst hW hA.v ha.v h.v⟩

omit hW in
theorem ctxI_dren {n m : ℕ} (τ : ℕ → I) (hτs : ∀ i, τ (i + n) = .var (i + m)) (Γ0 : Ctx) :
    ctxI τ (Ctx.dren n Γ0) = Ctx.dren m Γ0 := by
  simp only [ctxI, Ctx.dren, List.map_map]
  congr 1; funext t
  simp only [Function.comp, ren_eq_subst, subst_subst]
  apply subst_congr
  · intro x; rfl
  · intro i; simp only [I.subst]; exact hτs i

omit hW in
theorem isubL_bound {n m Ψ0 : ℕ} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) : ∀ i < Ψ0 + n, (τ i).Scoped (Ψ0 + m) := by
  intro i hi
  by_cases hin : i < n
  · exact hτ i hin
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
    rw [hτs]; show j + m < Ψ0 + m; omega

/-- Interval substitution of the innermost interval variables. -/
theorem VTy.isubL {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} {t A : Tm} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n)) (hent : I.Entails Φ' (Φs.subst τ))
    (hw : Wf0 S (Ψ0 + m) Φ' (Ctx.dren m Γ0)) (h : VTy S (Ψ0 + n) Φs (Ctx.dren n Γ0) t A) :
    VTy S (Ψ0 + m) Φ' (Ctx.dren m Γ0) (t.dsubst τ) (A.dsubst τ) := by
  refine ⟨?_, valid_dsub τ hτ hτs hΦs hent (closed_ty h.ty) (closed_ty h.ty) (closedT_of_ty hW h.ty) h.v⟩
  have := HasTy0.isub (sigClosed_of_wfSig hW) h.ty (isubL_bound τ hτ hτs) hent (by rw [ctxI_dren τ hτs]; exact hw)
  rwa [ctxI_dren τ hτs] at this

theorem VEq.isubL {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} {t u A : Tm} (τ : ℕ → I) (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m))
    (hτs : ∀ i, τ (i + n) = .var (i + m)) (hΦs : Φs.Scoped (Ψ0 + n)) (hent : I.Entails Φ' (Φs.subst τ))
    (hw : Wf0 S (Ψ0 + m) Φ' (Ctx.dren m Γ0)) (h : VEq S (Ψ0 + n) Φs (Ctx.dren n Γ0) t u A) :
    VEq S (Ψ0 + m) Φ' (Ctx.dren m Γ0) (t.dsubst τ) (u.dsubst τ) (A.dsubst τ) := by
  refine ⟨?_, valid_dsub τ hτ hτs hΦs hent (closed_ty (presup hW h.eq).1) (closed_ty (presup hW h.eq).2)
    (closedT_of_ty hW (presup hW h.eq).1) h.v⟩
  have := EqTm0.isub (sigClosed_of_wfSig hW) h.eq (isubL_bound τ hτ hτs) hent (by rw [ctxI_dren τ hτs]; exact hw)
  rwa [ctxI_dren τ hτs] at this

/-- A typed term at two pointwise equal interval substitutions of the innermost variables. -/
theorem VTy.ieqL {n m Ψ0 : ℕ} {Φs Φ' : I} {Γ0 : Ctx} {t A : Tm} (τ τ' : ℕ → I)
    (hτ : ∀ i < n, (τ i).Scoped (Ψ0 + m)) (hτs : ∀ i, τ (i + n) = .var (i + m))
    (hτ' : ∀ i < n, (τ' i).Scoped (Ψ0 + m)) (hτs' : ∀ i, τ' (i + n) = .var (i + m))
    (heq : ∀ i < n, I.Eq (τ i) (τ' i)) (hΦs : Φs.Scoped (Ψ0 + n)) (hent : I.Entails Φ' (Φs.subst τ))
    (hent' : I.Entails Φ' (Φs.subst τ'))
    (hw : Wf0 S (Ψ0 + m) Φ' (Ctx.dren m Γ0)) (h : VTy S (Ψ0 + n) Φs (Ctx.dren n Γ0) t A) :
    VEq S (Ψ0 + m) Φ' (Ctx.dren m Γ0) (t.dsubst τ) (t.dsubst τ') (A.dsubst τ) := by
  refine ⟨?_, valid_dsub2 τ τ' hτ hτs hτ' hτs' heq hΦs hent (closed_ty h.ty) (closed_ty h.ty)
    (closedT_of_ty hW h.ty) h.v⟩
  have := HasTy0.ieq (sigClosed_of_wfSig hW) h.ty (isubL_bound τ hτ hτs) (isubL_bound τ' hτ' hτs') hent hent'
    (fun i hi => by
      by_cases hin : i < n
      · exact heq i hin
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
        rw [hτs, hτs']; exact I_eq_refl _)
    (by rw [ctxI_dren τ hτs, ctxI_dren τ' hτs']) (by rw [ctxI_dren τ hτs]; exact hw)
  rwa [ctxI_dren τ hτs] at this

/-! ### Common interval substitutions -/

/-- Renaming a line past a new interval variable, with the line variable set to `r`. -/
theorem VTy.bind2' {t A : Tm} {X r : I} (hr : r.Scoped (Ψ + 2)) (hΦ : Φ.Scoped Ψ) (hX : I.Entails X Φ.shift.shift)
    (hw : Wf0 S (Ψ + 1 + 1) X Γ.dshift.dshift) (h : VTy S (Ψ + 1) Φ.shift Γ.dshift t A) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift (t.dsubst (Tm.bind2 r)) (A.dsubst (Tm.bind2 r)) := by
  have := VTy.isubL hW (n := 1) (m := 2) (Ψ0 := Ψ) (Φs := Φ.shift) (Γ0 := Γ) (Tm.bind2 r)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl) (KubusCore.I.scoped_shift hΦ)
    (ent_bind2_shift r hX)
    (by rw [Ctx.dren_two]; exact hw) h
  rwa [Ctx.dren_two] at this

theorem VEq.bind2' {t u A : Tm} {X r : I} (hr : r.Scoped (Ψ + 2)) (hΦ : Φ.Scoped Ψ) (hX : I.Entails X Φ.shift.shift)
    (hw : Wf0 S (Ψ + 1 + 1) X Γ.dshift.dshift) (h : VEq S (Ψ + 1) Φ.shift Γ.dshift t u A) :
    VEq S (Ψ + 1 + 1) X Γ.dshift.dshift (t.dsubst (Tm.bind2 r)) (u.dsubst (Tm.bind2 r)) (A.dsubst (Tm.bind2 r)) := by
  have := VEq.isubL hW (n := 1) (m := 2) (Ψ0 := Ψ) (Φs := Φ.shift) (Γ0 := Γ) (Tm.bind2 r)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl) (KubusCore.I.scoped_shift hΦ)
    (ent_bind2_shift r hX)
    (by rw [Ctx.dren_two]; exact hw) h
  rwa [Ctx.dren_two] at this

/-- A line at `sk r k`, as a substitution of the innermost variable. -/
theorem VEq.sk2' {t u A : Tm} {X r : I} (hr : r.Scoped (Ψ + 2)) (hΦ : Φ.Scoped Ψ) (hX : I.Entails X Φ.shift.shift)
    (hw : Wf0 S (Ψ + 1 + 1) X Γ.dshift.dshift) (h : VEq S (Ψ + 1) Φ.shift Γ.dshift t u A) :
    VEq S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk r 2)) (u.subst Tm.var (sk r 2)) (A.subst Tm.var (sk r 2)) := by
  have := VEq.bind2' hW hr hΦ hX hw h
  simp only [Tm.dsubst, pw_L] at this; exact this

/-- Interval functionality of a line in its line variable (`line_ieq`). -/
theorem VTy.lineIeq {C T : Tm} (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C T) {k : ℕ} {X r r' : I}
    (hX : I.Entails X (Φ.subst (fun n => .var (n + k)))) (hr : r.Scoped (Ψ + k)) (hr' : r'.Scoped (Ψ + k))
    (he : I.Eq r r') (hw : Wf0 S (Ψ + k) X (Ctx.dren k Γ)) :
    VEq S (Ψ + k) X (Ctx.dren k Γ) (C.subst Tm.var (sk r k)) (C.subst Tm.var (sk r' k)) (T.subst Tm.var (sk r k)) :=
  VTy.ieqL hW (n := 1) (m := k) (Ψ0 := Ψ) (Φs := Φ.shift) (Γ0 := Γ) (sk r k) (sk r' k)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr') (fun i => rfl)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact he)
    (KubusCore.I.scoped_shift (scoped_of_wf (wf_unshift (sigClosed_of_wfSig hW) (wf_of_ty hC.ty)))) (ent_skk _ _ hX)
    (ent_skk _ _ hX) hw hC

/-! ### Transport filler -/

/-- `transpFill_typed`, with validity. -/
theorem VTy.transpFill' {A a : Tm} {φ : I} {l : ℕ}
    (hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)) (hφ : φ.Scoped Ψ)
    (hcD : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (ha : VTy S Ψ Φ Γ a (A.dinst .zero)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.transpFill A φ a) A ∧
      VEq S Ψ Φ Γ ((Tm.transpFill A φ a).dinst .zero) a (A.dinst .zero) ∧
      VEq S Ψ Φ Γ ((Tm.transpFill A φ a).dinst .one) (.transp A φ a) (A.dinst .one) ∧
      VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (Tm.transpFill A φ a) a.dshift A := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hA.ty)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hψ : (I.or φ.shift (.neg (.var 0))).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hφ, hv0⟩
  have hL := VTy.bind2' hW (X := Φ.shift.shift) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs (ent_refl _)
    (hw0.dwk2 hS) hA
  rw [univ_dsubst] at hL
  let Y : I := (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift ⟨KubusCore.I.scoped_shift hs, hψ⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_and_left _ _
  have hwY : Wf0 S (Ψ + 1 + 1) Y (Ctx.dren 2 Γ) := by
    rw [Ctx.dren_two]; exact (hw0.dwk2 hS).restrict hYs hYΦ
  have hLY := VTy.restrict' hW hYs hYΦ hL
  have hL0Y := VTy.restrict' hW hYs hYΦ (VTy.dwk' hW (VTy.dsubst' hW (Φ := Φ.shift) (Γ := Γ.dshift) .zero trivial hL))
  have hconst : VEq S (Ψ + 1 + 1) Y Γ.dshift.dshift
      (A.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      ((A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (.univ l) := by
    refine VEq.local' hW (φ := φ.shift.shift) (ψ := .neg (.var 1)) (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ))
      hv1 (ent_and_right _ _) hLY hL0Y ?_ ?_
    · have hZs : (cof Y φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hYs, KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ)⟩
      have hZ : I.Entails (cof Y φ.shift.shift) (cof Φ φ).shift.shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) hYΦ) (ent_and_right _ _)
      have key : ∀ r : I, r.Scoped (Ψ + 1 + 1) →
          VEq S (Ψ + 1 + 1) (cof Y φ.shift.shift) Γ.dshift.dshift
            (A.subst Tm.var (sk r 2)) (A.dinst .zero).dshift.dshift (.univ l) := by
        intro r hr
        have := VEq.sk2' hW (Φ := cof Φ φ) (X := cof Y φ.shift.shift) hr ⟨hs, hφ⟩ hZ
          ((hw0.dwk2 hS).restrict hZs (ent_trans hZ (ent_shift (ent_shift (ent_and_left _ _))))) hcD
        rwa [tsf_A0] at this
      have e1 := key (.and (.var 1) (.var 0)) ⟨hv1, hv0'⟩
      have e2 := key (.and (.var 1) .zero) ⟨hv1, trivial⟩
      rw [tf_L0s, pw_L]
      exact VEq.trans' hW e1 (VEq.symm' hW e2)
    · have hZs : (cof Y (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hZΦ : I.Entails (cof Y (.neg (.var 1))) (Φ.subst (fun n => .var (n + 2))) := by
        rw [I_add2]; exact ent_trans (ent_and_left _ _) hYΦ
      have hwZ : Wf0 S (Ψ + 2) (cof Y (.neg (.var 1))) (Ctx.dren 2 Γ) := hwY.restrict hZs (ent_and_left _ _)
      have hY1 : I.Entails (cof Y (.neg (.var 1))) (I.lit 1 false) := ent_and_right _ (.neg (.var 1))
      have e1 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 (VTy.restrict' hW hZs (ent_and_left _ _) hLY)
      rw [tf_L1] at e1
      have e2 := VTy.lineIeq hW hA (k := 2) (r := .and .zero (.var 0)) (r' := .zero) hZΦ
        ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hwZ
      rw [Ctx.dren_two] at e2
      have hL0Z := VTy.restrict' hW hZs (ent_and_left _ _) hL0Y
      rw [tf_L0s] at hL0Z
      have e3 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 hL0Z
      rw [tf_L0s1] at e3
      have e4 := VTy.lineIeq hW hA (k := 2) (r := .and .zero .zero) (r' := .zero) hZΦ
        ⟨trivial, trivial⟩ trivial (I_eq_and_zero _) hwZ
      rw [Ctx.dren_two] at e4
      rw [tf_L0s]
      exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW (VEq.trans' hW e3 e4)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 Γ) := wf_of_ty hA.ty
  have ha' : VTy S (Ψ + 1) Φ.shift Γ.dshift a.dshift ((A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := VTy.lineIeq hW hA (k := 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [sk_zero1] at e
    exact VTy.conv' hW (VTy.dwk' hW ha) e
  have ht0 := VTy.transp' hW hL hψ hconst ha'
  have eC : VEq S (Ψ + 1) Φ.shift Γ.dshift ((A.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) A (.univ l) := by
    have e := VTy.lineIeq hW hA (k := 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (I_eq_and_one_r _) hwX
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  have htf : VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.transpFill A φ a) A := VTy.conv' hW ht0 eC
  refine ⟨htf, ?_, ?_, ?_⟩
  · have h0 := VTy.dsubst' hW .zero trivial ht0
    have eC0 := VEq.dsubst' hW .zero trivial eC
    have hf : VEq S Ψ Φ Γ ((Tm.transpFill A φ a).dinst .zero) (a.dshift.dinst .zero) _ :=
      VEq.transpFace' hW (φ := (I.or φ.shift (.neg (.var 0))).subst (I.inst0 .zero))
        (by rw [cofn_inst]; exact ent_trans (ent_negzero Φ) (ent_or_right _ _)) h0
    rw [dshift_dinst] at hf
    exact VEq.conv' hW hf eC0
  · have h1 : VTy S Ψ Φ Γ ((Tm.transpFill A φ a).dinst .one) _ := VTy.dsubst' hW .one trivial ht0
    rw [tf_d1_eq, tsf_L11] at h1
    have hline : VEq S (Ψ + 1) Φ.shift Γ.dshift (A.subst Tm.var (sk (.and .one (.var 0)) 1)) A (.univ l) := by
      have e := VTy.lineIeq hW hA (k := 1) (r := .and .one (.var 0)) (r' := .var 0) (ent_refl _)
        ⟨trivial, hv0⟩ hv0 (I_eq_and_one_l _) hwX
      rwa [sk_var1] at e
    have eL1 := VEq.dsubst' hW .one trivial hline
    have eL0 := VEq.dsubst' hW .zero trivial hline
    have h2 := VTy.transp' hW hA hφ hcD ha
    -- the constancy of the left line, through `A`
    have hψ1 : (I.or φ (.neg .one)).Scoped Ψ := ⟨hφ, trivial⟩
    have hX1s : (cof Φ (.or φ (.neg .one))).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hψ1⟩
    have hX1 : I.Entails (cof Φ (.or φ (.neg .one))).shift (cof Φ φ).shift :=
      ent_shift (ent_and_mono (ent_refl _) (ent_neg_one φ))
    have hX1Φ : I.Entails (cof Φ (.or φ (.neg .one))).shift Φ.shift := ent_shift (ent_and_left _ _)
    have hc1 : Valid2 S (Ψ + 1) (cof Φ (.or φ (.neg .one))).shift Γ.dshift
        (A.subst Tm.var (sk (.and .one (.var 0)) 1))
        ((A.subst Tm.var (sk (.and .one (.var 0)) 1)).dinst .zero).dshift (.univ l) := by
      have k1 := valid_restrict hW hX1Φ hline.v
      have k2 := valid_restrict hW hX1 hcD.v
      have k3 : Valid2 S (Ψ + 1) (cof Φ (.or φ (.neg .one))).shift Γ.dshift
          ((A.subst Tm.var (sk (.and .one (.var 0)) 1)).dinst .zero).dshift (A.dinst .zero).dshift (.univ l) :=
        valid_restrict hW hX1Φ (VEq.dwk' hW (VEq.dsubst' hW .zero trivial hline)).v
      exact valid_trans hW k1 (valid_trans hW k2 (valid_symm hW k3))
    have e := VEq.transp' hW  hψ1 (ent_neg_one φ) (ent_or_left _ _)
      h1.ty (HasTy0.conv h2.ty (VEq.symm' hW eL1).eq) hline hc1
      (VEq.refl' (VTy.conv' hW ha (VEq.symm' hW eL0)))
    rw [tf_d1_eq]
    exact VEq.conv' hW e eL1
  · exact VEq.transpFace' hW (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _))
      (VTy.restrict' hW (KubusCore.I.scoped_shift ⟨hs, hφ⟩) (ent_shift (ent_and_left _ _)) htf)

end

end Model.Whnf
