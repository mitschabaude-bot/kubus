import KubusCore.Meta.Final
import KubusCore.Meta.Near
import KubusCore.Meta.NearElim

/-!
# Metatheory: near typed terms are judgmentally equal

`near_ty`: if `t` is typed and `t'` is near `t` (`TmNear`: the same shape, interval terms equal in
the free De Morgan algebra, cofibrations mutually entailing) and has its interval variables in
scope, then `t ≡ t'` (so `t'` is typed). By induction on the typing derivation, using the
congruence rules; the near side's typing is rebuilt from its components.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem lookup_lt' : ∀ {Γ : Ctx} {x : Nat} {A : Tm}, Γ.lookup x = some A → x < Γ.length
  | [], _, _, h => by simp [Ctx.lookup] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: Γ, x + 1, A, h => by
    simp only [Ctx.lookup, Option.map_eq_some_iff] at h
    obtain ⟨B, hB, -⟩ := h
    have := lookup_lt' hB; simp; omega

theorem closedB_ofList' {n m : Nat} : ∀ {L : List Tm}, (∀ t ∈ L, t.closedB n m = true) → (Tm.ofList L).closedB n m = true
  | [], _ => rfl
  | t :: L, h => by
    simp only [Tm.ofList, Tm.closedB, Bool.and_eq_true]
    exact ⟨h t (List.mem_cons_self ..), closedB_ofList' fun t' ht' => h t' (List.mem_cons_of_mem _ ht')⟩

theorem scopedB_of' {r : I} {m : Nat} (h : r.Scoped m) : r.scopedB m = true := (I.scopedB_iff m r).2 h


mutual

theorem ty_closedB {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → t.closedB Γ.length Ψ = true
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 => by simp [Tm.closedB, lookup_lt' h1]
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => ty_closedB h0
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 => ty_closedB h2
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 => rfl
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 => rfl
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 => ty_closedB h1
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, by simpa using ty_closedB h1⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 => by
    have := ty_closedB h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢; exact ⟨this.1, by simpa using ty_closedB h1⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, ty_closedB h1⟩
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, by simpa using ty_closedB h1⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h1, ty_closedB h2⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 => by simp only [Tm.closedB]; exact ty_closedB h0
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 => by simp only [Tm.closedB]; exact ty_closedB h0
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using ty_closedB h0, ty_closedB h1⟩, ty_closedB h2⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using ty_closedB h1
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, scopedB_of' h1⟩
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using ty_closedB h1
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 => by
    simp only [Tm.closedB]; simpa [Ctx.dshift] using ty_closedB h1
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, scopedB_of' h1⟩
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨scopedB_of' h0, ty_closedB h4⟩, scopedB_of' h1⟩, ty_closedB h5⟩
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 => rfl
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨by simpa [Ctx.dshift] using ty_closedB h0, scopedB_of' h1⟩, ty_closedB h3⟩
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨ty_closedB h0, scopedB_of' h1⟩, by simpa [Ctx.dshift] using ty_closedB h2⟩, ty_closedB h3⟩
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    exact ⟨⟨⟨ty_closedB h0, scopedB_of' h1⟩, ty_closedB h2⟩, ty_closedB h3⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 => by
    have := ty_closedB h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨⟨this.1.1.2, ty_closedB h1⟩, ty_closedB h2⟩, ty_closedB h3⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 => by
    have := ty_closedB h0
    simp only [Tm.closedB, Bool.and_eq_true] at this ⊢
    exact ⟨⟨this.1.1.2, ty_closedB h2⟩, ty_closedB h3⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 => by simp only [Tm.closedB]; exact tele_closedB h2
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => by
    simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨tele_closedB h4, tele_closedB h5⟩, fun r hr => scopedB_of' (h7 r hr)⟩
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    simp only [Tm.closedB, Bool.and_eq_true]
    refine ⟨⟨⟨tele_closedB h3, by simpa using ty_closedB h4⟩, ?_⟩, ty_closedB h9⟩
    rw [h5]
    refine closedB_ofList' fun b hb => ?_
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨C, hC⟩ : ∃ C, D.ctors[c]? = some C :=
      ⟨D.ctors[c]'(by omega), List.getElem?_eq_getElem _⟩
    exact ty_closedB (h7 c C _ hC (List.getElem?_eq_getElem hc))

theorem tele_closedB {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ts.closedB Γ.length Ψ = true
  | @HasTele0.nil _ Ψ Φ Γ prev h0 => rfl
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 => by
    simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨ty_closedB h0, tele_closedB h1⟩

end

/-! ## Congruence of the types of equivalences -/

section
variable {S : Sig} (hS : SigClosed S) (hT0 : SigTyped0 S) (hC0 : ContractaTyped S)
include hS hT0 hC0

omit hT0 hC0 in
theorem pathC_congr0 {Ψ Φ Γ A A' a a' b b' l} (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (ha : EqTm0 S Ψ Φ Γ a a' A)
    (hb : EqTm0 S Ψ Φ Γ b b' A) : EqTm0 S Ψ Φ Γ (Tm.pathC A a b) (Tm.pathC A' a' b') (Tm.univ l) := by
  have hAd := EqTm0.dwk hS hA
  exact EqTm0.path hAd (by rw [Meta.dshift_dinst]; exact ha) (by rw [Meta.dshift_dinst]; exact hb)

theorem isContr_congr0 {Ψ Φ Γ X X' l} (hX : EqTm0 S Ψ Φ Γ X X' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.isContr X) (Tm.isContr X') (Tm.univ l) := by
  have hXt := (pre_eq hS hT0 hC0 hX).1
  have hX1t := HasTy0.wk hS hXt hXt
  have hX1 := EqTm0.wk hS hXt hX
  have hX2 := EqTm0.wk hS hX1t hX1
  have hv1 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (Tm.var 1) X.shift.shift := HasTy0.var (Wf0.cons hX1t) rfl
  have hv0 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (Tm.var 0) X.shift.shift := HasTy0.var (Wf0.cons hX1t) rfl
  exact EqTm0.sigma hX (EqTm0.pi hX1 (pathC_congr0 hS hX2 (EqTm0.refl hv1) (EqTm0.refl hv0)))

theorem fiber_congr0 {Ψ Φ Γ T T' A A' f f' y y' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l))
    (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (hf : EqTm0 S Ψ Φ Γ f f' (Tm.arrow T A)) (hy : EqTm0 S Ψ Φ Γ y y' A) :
    EqTm0 S Ψ Φ Γ (Tm.fiber T A f y) (Tm.fiber T' A' f' y') (Tm.univ l) := by
  have hTt := (pre_eq hS hT0 hC0 hT).1
  have hA1 := EqTm0.wk hS hTt hA
  have hf1 := EqTm0.wk hS hTt hf
  rw [Meta.arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (T :: Γ) (Tm.var 0) T.shift := HasTy0.var (Wf0.cons hTt) rfl
  have happ := EqTm0.app hf1 (EqTm0.refl hv)
  rw [Meta.shift_inst] at happ
  exact EqTm0.sigma hT (pathC_congr0 hS hA1 happ (EqTm0.wk hS hTt hy))

theorem isEquiv_congr0 {Ψ Φ Γ T T' A A' f f' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l))
    (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (hf : EqTm0 S Ψ Φ Γ f f' (Tm.arrow T A)) :
    EqTm0 S Ψ Φ Γ (Tm.isEquiv T A f) (Tm.isEquiv T' A' f') (Tm.univ l) := by
  have hAt := (pre_eq hS hT0 hC0 hA).1
  have hT1 := EqTm0.wk hS hAt hT
  have hA1 := EqTm0.wk hS hAt hA
  have hf1 := EqTm0.wk hS hAt hf
  rw [Meta.arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (A :: Γ) (Tm.var 0) A.shift := HasTy0.var (Wf0.cons hAt) rfl
  exact EqTm0.pi hA (isContr_congr0 hS hT0 hC0 (fiber_congr0 hS hT0 hC0 hT1 hA1 hf1 (EqTm0.refl hv)))

theorem arrow_congr0 {Ψ Φ Γ T T' A A' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l)) (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.arrow T A) (Tm.arrow T' A') (Tm.univ l) :=
  EqTm0.pi hT (EqTm0.wk hS (pre_eq hS hT0 hC0 hT).1 hA)

theorem equiv_congr0 {Ψ Φ Γ T T' A A' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l)) (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.equiv T A) (Tm.equiv T' A') (Tm.univ l) := by
  have hTA := arrow_congr0 hS hT0 hC0 hT hA
  have hTAt := (pre_eq hS hT0 hC0 hTA).1
  have hv : HasTy0 S Ψ Φ (Tm.arrow T A :: Γ) (Tm.var 0) (Tm.arrow T A).shift := HasTy0.var (Wf0.cons hTAt) rfl
  rw [Meta.arrow_shift] at hv
  exact EqTm0.sigma hTA (isEquiv_congr0 hS hT0 hC0 (EqTm0.wk hS hTAt hT) (EqTm0.wk hS hTAt hA) (EqTm0.refl hv))

theorem piPath_congr0 {Ψ Φ Γ X X' c c' l} (hX : EqTm0 S Ψ Φ Γ X X' (Tm.univ l)) (hc : EqTm0 S Ψ Φ Γ c c' X) :
    EqTm0 S Ψ Φ Γ (.pi X (Tm.pathC X.shift c.shift (.var 0))) (.pi X' (Tm.pathC X'.shift c'.shift (.var 0))) (Tm.univ l) := by
  have hXt := (pre_eq hS hT0 hC0 hX).1
  have hv : HasTy0 S Ψ Φ (X :: Γ) (Tm.var 0) X.shift := HasTy0.var (Wf0.cons hXt) rfl
  exact EqTm0.pi hX (pathC_congr0 hS (EqTm0.wk hS hXt hX) (EqTm0.wk hS hXt hc) (EqTm0.refl hv))

end

/-! ## Near terms -/

theorem ctx_dshift_length (Γ : Ctx) : Γ.dshift.length = Γ.length := List.length_map _

section
variable (hS : SigClosed S) (hT : SigTyped0 S) (hC : ContractaTyped S)
include hS hT hC

theorem eqR0 {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) : HasTy0 S Ψ Φ Γ u A := (pre_eq hS hT hC h).2.1

omit hS hT hC in
theorem ieqL_length : ∀ {rs rs' : List I}, IEqL rs rs' → rs.length = rs'.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [ieqL_length h]

omit hS hT hC in
theorem ieqL_get : ∀ {rs rs' : List I}, IEqL rs rs' → ∀ (k : Nat) (r r' : I), rs[k]? = some r → rs'[k]? = some r' →
    I.Eq r r'
  | _, _, .nil => fun k r r' h _ => by simp at h
  | _, _, .cons e h => fun k r r' h1 h2 => by
    cases k with
    | zero => simp at h1 h2; subst h1 h2; exact e
    | succ k => simp at h1 h2; exact ieqL_get h k r r' h1 h2

variable (hW : WfSig S)
include hW

mutual

theorem near_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → ∀ {t'}, TmNear t t' → t'.closedB Γ.length Ψ = true →
    EqTm0 S Ψ Φ Γ t t' A
  | @HasTy0.var _ Ψ Φ Γ x A hw hx => fun hn _ => by cases hn; exact EqTm0.refl (HasTy0.var hw hx)
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 => fun hn hc => EqTm0.conv (near_ty h0 hn hc) h1
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A hs he h0 => fun hn hc => EqTm0.restrict hs he (near_ty h0 hn hc)
  | @HasTy0.const _ Ψ Φ Γ k t A hw hk => fun hn _ => by cases hn; exact EqTm0.refl (HasTy0.const hw hk)
  | @HasTy0.univ _ Ψ Φ Γ l hl hw => fun hn _ => by cases hn; exact EqTm0.refl (HasTy0.univ hl hw)
  | @HasTy0.cumul _ Ψ Φ Γ A l hl h0 => fun hn hc => EqTm0.cumul hl (near_ty h0 hn hc)
  | @HasTy0.pi _ Ψ Φ Γ A B l hA hB => fun hn hc => by
    cases hn with
    | pi nA nB =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.pi (near_ty hA nA hc.1) (near_ty hB nB (by simpa using hc.2))
  | @HasTy0.sigma _ Ψ Φ Γ A B l hA hB => fun hn hc => by
    cases hn with
    | sigma nA nB =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.sigma (near_ty hA nA hc.1) (near_ty hB nB (by simpa using hc.2))
  | @HasTy0.app _ Ψ Φ Γ A B f a hf ha => fun hn hc => by
    cases hn with
    | app nf na =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.app (near_ty hf nf hc.1) (near_ty ha na hc.2)
  | @HasTy0.pair _ Ψ Φ Γ A B a b l hs ha hb => fun hn hc => by
    cases hn with
    | pair na nb =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.pair hs (near_ty ha na hc.1) (near_ty hb nb hc.2)
  | @HasTy0.fst _ Ψ Φ Γ A B p hp => fun hn hc => by
    cases hn with
    | fst np => exact EqTm0.fst (near_ty hp np hc)
  | @HasTy0.snd _ Ψ Φ Γ A B p hp => fun hn hc => by
    cases hn with
    | snd np => exact EqTm0.snd (near_ty hp np hc)
  | @HasTy0.lam _ Ψ Φ Γ A B t l hP ht => fun hn hc => by
    cases hn with
    | lam nA nt =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      obtain ⟨l1, ⟨hA0, hB0⟩, -⟩ := gen_pi hS hP rfl
      have hBc : B.closedB (Γ.length + 1) Ψ = true := by simpa using ty_closedB hB0
      have ePi := near_ty hP (TmNear.pi nA (TmNear.refl B)) (by simp [Tm.closedB, hc.1, hBc])
      have eA := EqTm0.piInjDom ePi
      have hA' := eqR0 hS hT hC eA
      have et := near_ty ht nt (by simpa using hc.2)
      have ht'' := HasTy0.ctxConv hS (eqR0 hS hT hC et) hA' (EqTm0.symm eA)
      have hlam' := HasTy0.lam (eqR0 hS hT hC ePi) ht''
      exact lam_congr' hS hA0 hP (HasTy0.conv hlam' (EqTm0.symm ePi)) et
  | @HasTy0.path _ Ψ Φ Γ A a b l hA ha hb => fun hn hc => by
    cases hn with
    | path nA na nb =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.path (near_ty hA nA (by rw [ctx_dshift_length]; exact hc.1.1)) (near_ty ha na hc.1.2)
        (near_ty hb nb hc.2)
  | @HasTy0.plam _ Ψ Φ Γ A a b t l hP ht h0 h1 => fun hn hc => by
    cases hn with
    | plam nt =>
      simp only [Tm.closedB] at hc
      have et := near_ty ht nt (by rw [ctx_dshift_length]; exact hc)
      have ht' := eqR0 hS hT hC et
      have e0 := EqTm0.dsubst hS et (r := .zero) trivial
      have e1 := EqTm0.dsubst hS et (r := .one) trivial
      have hp' := HasTy0.plam hP ht' (EqTm0.trans (EqTm0.symm e0) h0) (EqTm0.trans (EqTm0.symm e1) h1)
      exact EqTm0.plam hP (HasTy0.plam hP ht h0 h1) hp' et
  | @HasTy0.papp _ Ψ Φ Γ A a b p r hp hr => fun hn hc => by
    cases hn with
    | papp np e =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.papp (near_ty hp np hc.1) hr ((I.scopedB_iff _ _).1 hc.2) e
  | @HasTy0.ipi _ Ψ Φ Γ A l hw hA => fun hn hc => by
    cases hn with
    | ipi nA =>
      simp only [Tm.closedB] at hc
      exact EqTm0.ipi hw (near_ty hA nA (by rw [ctx_dshift_length]; exact hc))
  | @HasTy0.ilam _ Ψ Φ Γ A t l hP ht => fun hn hc => by
    cases hn with
    | plam nt =>
      simp only [Tm.closedB] at hc
      exact EqTm0.ilam hP (near_ty ht nt (by rw [ctx_dshift_length]; exact hc))
  | @HasTy0.iapp _ Ψ Φ Γ A p r hp hr => fun hn hc => by
    cases hn with
    | papp np e =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTm0.iapp (near_ty hp np hc.1) hr ((I.scopedB_iff _ _).1 hc.2) e
  | @HasTy0.abort _ Ψ Φ Γ A l he hA => fun hn _ => by cases hn; exact EqTm0.refl (HasTy0.abort he hA)
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l hφ hψ hor hA ht hu htu => fun hn hc => by
    cases hn with
    | @split _ φ' _ ψ' _ t' _ u' eφ nt eψ nu =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1.1
      have hψ' : ψ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.2
      have hs : Φ.Scoped Ψ := scoped_of_ty hA
      have et := near_ty ht nt hc.1.1.2
      have eu := near_ty hu nu hc.2
      have c1 : I.Entails (cof Φ φ') (cof Φ φ) := ent_and_mono (ent_refl _) eφ.2
      have c2 : I.Entails (cof Φ ψ') (cof Φ ψ) := ent_and_mono (ent_refl _) eψ.2
      have hs1 : (cof Φ φ').Scoped Ψ := ⟨hs, hφ'⟩
      have hs2 : (cof Φ ψ').Scoped Ψ := ⟨hs, hψ'⟩
      have hs12 : (cof (cof Φ φ') ψ').Scoped Ψ := ⟨hs1, hψ'⟩
      have ht' := HasTy0.restrict hs1 c1 (eqR0 hS hT hC et)
      have hu' := HasTy0.restrict hs2 c2 (eqR0 hS hT hC eu)
      have htu' : EqTm0 S Ψ (cof (cof Φ φ') ψ') Γ t' u' A :=
        EqTm0.trans (EqTm0.restrict hs12 (ent_trans (ent_and_left _ _) c1) (EqTm0.symm et))
          (EqTm0.trans (EqTm0.restrict hs12 (ent_and_mono c1 eψ.2) htu)
            (EqTm0.restrict hs12 (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _))
              (ent_trans (ent_and_right _ _) eψ.2)) eu))
      have hor' : I.Entails Φ (.or φ' ψ') :=
        ent_trans hor (ent_or_elim (ent_trans eφ.1 (ent_or_left _ _)) (ent_trans eψ.1 (ent_or_right _ _)))
      have hsp := HasTy0.split hφ hψ hor hA ht hu htu
      have hsp' := HasTy0.split hφ' hψ' hor' hA ht' hu' htu'
      refine EqTm0.local hφ hψ hor hsp hsp' ?_ ?_
      · have hc1 : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
        exact EqTm0.trans (EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc1 (ent_and_left _ _) hsp))
          (EqTm0.trans et (EqTm0.symm (EqTm0.splitL (ent_trans (ent_and_right _ _) eφ.1)
            (HasTy0.restrict hc1 (ent_and_left _ _) hsp'))))
      · have hc2 : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
        exact EqTm0.trans (EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc2 (ent_and_left _ _) hsp))
          (EqTm0.trans eu (EqTm0.symm (EqTm0.splitR (ent_trans (ent_and_right _ _) eψ.1)
            (HasTy0.restrict hc2 (ent_and_left _ _) hsp'))))
  | @HasTy0.transp _ Ψ Φ Γ A φ a l hA hφ hc0 ha => fun hn hc => by
    cases hn with
    | @transp _ A' _ a' _ φ' nA eφ na =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.2
      have hs : Φ.Scoped Ψ := scoped_of_ty ha
      have eA := near_ty hA nA (by rw [ctx_dshift_length]; exact hc.1.1)
      have ea := near_ty ha na hc.2
      have e0 := EqTm0.dsubst hS eA (r := .zero) trivial
      have e1 := EqTm0.dsubst hS eA (r := .one) trivial
      have hX : (cof Φ φ').shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ'⟩
      have hXΦ : I.Entails (cof Φ φ').shift Φ.shift := ent_shift (ent_and_left _ _)
      have hXφ : I.Entails (cof Φ φ').shift (cof Φ φ).shift := ent_shift (ent_and_mono (ent_refl _) eφ.2)
      have hconst' : EqTm0 S (Ψ + 1) (cof Φ φ').shift Γ.dshift A' (A'.dinst .zero).dshift (univ l) :=
        EqTm0.trans (EqTm0.restrict hX hXΦ (EqTm0.symm eA))
          (EqTm0.trans (EqTm0.restrict hX hXφ hc0) (EqTm0.restrict hX hXΦ (EqTm0.dwk hS e0)))
      have htr' := HasTy0.transp (eqR0 hS hT hC eA) hφ' hconst' (HasTy0.conv (eqR0 hS hT hC ea) e0)
      exact EqTm0.transp (HasTy0.transp hA hφ hc0 ha) (HasTy0.conv htr' (EqTm0.symm e1)) eA eφ.1 eφ.2 ea
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l hA hφ hu ha hside => fun hn hc => by
    cases hn with
    | @hcomp _ A' _ u' _ a' _ φ' nA eφ nu na =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1.2
      have hs : Φ.Scoped Ψ := scoped_of_ty ha
      have eA := near_ty hA nA hc.1.1.1
      have eu := near_ty hu nu (by rw [ctx_dshift_length]; exact hc.1.2)
      have ea := near_ty ha na hc.2
      have hX : (cof Φ φ').shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ'⟩
      have hXφ : I.Entails (cof Φ φ').shift (cof Φ φ).shift := ent_shift (ent_and_mono (ent_refl _) eφ.2)
      have hu' : HasTy0 S (Ψ + 1) (cof Φ φ').shift Γ.dshift u' A'.dshift :=
        HasTy0.conv (HasTy0.restrict hX hXφ (eqR0 hS hT hC eu))
          (EqTm0.restrict hX (ent_shift (ent_and_left _ _)) (EqTm0.dwk hS eA))
      have hs1 : (cof Φ φ').Scoped Ψ := ⟨hs, hφ'⟩
      have c1 : I.Entails (cof Φ φ') (cof Φ φ) := ent_and_mono (ent_refl _) eφ.2
      have eu0 := EqTm0.dsubst hS eu (r := .zero) trivial
      rw [Meta.dshift_dinst] at eu0
      have hside' : EqTm0 S Ψ (cof Φ φ') Γ (u'.dinst .zero) a' A' :=
        EqTm0.conv (EqTm0.trans (EqTm0.restrict hs1 c1 (EqTm0.symm eu0))
          (EqTm0.trans (EqTm0.restrict hs1 c1 hside) (EqTm0.restrict hs1 (ent_and_left _ _) ea)))
          (EqTm0.restrict hs1 (ent_and_left _ _) eA)
      have hc' := HasTy0.hcomp (eqR0 hS hT hC eA) hφ' hu' (HasTy0.conv (eqR0 hS hT hC ea) eA) hside'
      exact EqTm0.hcomp (HasTy0.hcomp hA hφ hu ha hside) (HasTy0.conv hc' (EqTm0.symm eA)) eA eφ.1 eφ.2 eu ea
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l hA hφ hT0 he => fun hn hc => by
    cases hn with
    | @glue _ A' _ T' _ e' _ φ' nA eφ nT ne =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1.2
      have hs : Φ.Scoped Ψ := scoped_of_ty hA
      have eA := near_ty hA nA hc.1.1.1
      have eT := near_ty hT0 nT hc.1.2
      have ee := near_ty he ne hc.2
      have hs1 : (cof Φ φ').Scoped Ψ := ⟨hs, hφ'⟩
      have c1 : I.Entails (cof Φ φ') (cof Φ φ) := ent_and_mono (ent_refl _) eφ.2
      have eT1 := EqTm0.restrict hs1 c1 eT
      have eA1 := EqTm0.restrict hs1 (ent_and_left _ _) eA
      have eqv := equiv_congr0 hS hT hC eT1 eA1
      have hG' := HasTy0.glue (eqR0 hS hT hC eA) hφ' (eqR0 hS hT hC eT1)
        (HasTy0.conv (HasTy0.restrict hs1 c1 (eqR0 hS hT hC ee)) eqv)
      exact EqTm0.glue (HasTy0.glue hA hφ hT0 he) hG' eA eφ.1 eφ.2 eT ee
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l hG he ht ha hcoh => fun hn hc => by
    cases hn with
    | @glueEl _ e' _ t' _ a' _ φ' eφ ne nt na =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1.1
      have hs : Φ.Scoped Ψ := scoped_of_ty ha
      have hcG := ty_closedB hG
      simp only [Tm.closedB, Bool.and_eq_true] at hcG
      have eG := near_ty hG (TmNear.glue (TmNear.refl A) eφ (TmNear.refl T) ne)
        (by simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨⟨⟨hcG.1.1.1, hc.1.1.1⟩, hcG.1.2⟩, hc.1.1.2⟩)
      have ee := near_ty he ne hc.1.1.2
      have et := near_ty ht nt hc.1.2
      have ea := near_ty ha na hc.2
      have hs1 : (cof Φ φ').Scoped Ψ := ⟨hs, hφ'⟩
      have c1 : I.Entails (cof Φ φ') (cof Φ φ) := ent_and_mono (ent_refl _) eφ.2
      have he' := HasTy0.restrict hs1 c1 (eqR0 hS hT hC ee)
      have ht' := HasTy0.restrict hs1 c1 (eqR0 hS hT hC et)
      have eapp := EqTm0.app (EqTm0.fst (EqTm0.restrict hs1 c1 (EqTm0.symm ee))) (EqTm0.restrict hs1 c1 (EqTm0.symm et))
      rw [shift_inst] at eapp
      have hcoh' : EqTm0 S Ψ (cof Φ φ') Γ (app (fst e') t') a' A :=
        EqTm0.trans eapp (EqTm0.trans (EqTm0.restrict hs1 c1 hcoh) (EqTm0.restrict hs1 (ent_and_left _ _) ea))
      have hgl' := HasTy0.glueEl (eqR0 hS hT hC eG) he' ht' (eqR0 hS hT hC ea) hcoh'
      exact EqTm0.glueEl (HasTy0.glueEl hG he ht ha hcoh) (HasTy0.conv hgl' (EqTm0.symm eG)) eφ.1 eφ.2 ee et ea
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l hG hA he hg => fun hn hc => by
    cases hn with
    | @unglue _ e' _ g' _ φ' eφ ne ng =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1
      have hs : Φ.Scoped Ψ := scoped_of_ty hA
      have hcG := ty_closedB hG
      simp only [Tm.closedB, Bool.and_eq_true] at hcG
      have eG := near_ty hG (TmNear.glue (TmNear.refl A) eφ (TmNear.refl T) ne)
        (by simp only [Tm.closedB, Bool.and_eq_true]; exact ⟨⟨⟨hcG.1.1.1, hc.1.1⟩, hcG.1.2⟩, hc.1.2⟩)
      have ee := near_ty he ne hc.1.2
      have eg := near_ty hg ng hc.2
      have hs1 : (cof Φ φ').Scoped Ψ := ⟨hs, hφ'⟩
      have c1 : I.Entails (cof Φ φ') (cof Φ φ) := ent_and_mono (ent_refl _) eφ.2
      have hu' := HasTy0.unglue (eqR0 hS hT hC eG) hA (HasTy0.restrict hs1 c1 (eqR0 hS hT hC ee))
        (HasTy0.conv (eqR0 hS hT hC eg) eG)
      exact EqTm0.unglue (HasTy0.unglue hG hA he hg) hu' eφ.1 eφ.2 ee eg
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 hl h2 => fun hn hc => by
    cases hn with
    | data nps =>
      simp only [Tm.closedB] at hc
      have es := near_teleC h2 nps hc
      have ht' := params_tele hS hW h0 (eqR0 hS hT hC) h2 es
      exact EqTm0.data h0 (HasTy0.data h0 hl h2) (HasTy0.data h0 hl ht') es.toEqTele0
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 => fun hn hc => by
    cases hn with
    | @con _ _ _ ps' _ args' _ rs' nps nargs hrs =>
      simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hc
      have es := near_teleC h4 nps hc.1.1
      have eas := near_teleC h5 nargs hc.1.2
      have edata := near_ty h3 (TmNear.data nps) (by simpa [Tm.closedB] using hc.1.1)
      have hpt' := params_tele hS hW h0 (eqR0 hS hT hC) h4 es
      have hat' := args_near hS hW h0 h1 (eqR0 hS hT hC) h4 es h5 eas edata
      have hrs' : rs'.length = C.dims := by rw [← ieqL_length hrs]; exact h6
      have hcon' := HasTy0.con h0 h1 es.isList' (eqR0 hS hT hC edata) hpt' hat' hrs'
        (fun r hr => (I.scopedB_iff _ _).1 (hc.2 r hr))
      exact EqTm0.con h0 h1 (HasTy0.con h0 h1 h2 h3 h4 h5 h6 h7) (HasTy0.conv hcon' (EqTm0.symm edata))
        es.toEqTele0 eas.toEqTele0 (ieqL_length hrs) (fun k r r' h1 h2 => ieqL_get hrs k r r' h1 h2)
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => fun hn hc => by
    cases hn with
    | @elim _ _ ps' _ P' _ bs' _ t' nps nP nbs nt =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hpres : ∀ {Ψ Φ Γ t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ u A := fun h => eqR0 hS hT hC h
      have es := near_teleC h3 nps hc.1.1.1
      have edata := near_ty h2 (TmNear.data nps) (by simpa [Tm.closedB] using hc.1.1.1)
      have eP := near_ty h4 nP (by simpa using hc.1.1.2)
      have et := near_ty h9 nt hc.2
      rw [h5] at nbs
      obtain ⟨hbs', hbl, hnb⟩ := near_list bs.toList nbs
      have hbcl := closed_toList hc.1.2
      have eb : ∀ (c : Nat) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
          bs'.toList[c]? = some b' → EqTm0 S Ψ Φ Γ b b' (D.branchTy d c C ps P) :=
        fun c C b b' hC hb hb' => near_ty (h7 c C b hC hb) (hnb c b b' hb hb')
          (hbcl b' (List.mem_of_getElem? hb'))
      have hmP : m ≤ maxLevel := IsTypB.lvl (pre_ty hS hT hC h4)
      have hpt' := params_tele hS hW h0 hpres h3 es
      have hdata' := HasTy0.data h0 (hW.2 d D h0).1 hpt'
      have hP' := HasTy0.ctxConv hS (hpres eP) hdata' (EqTm0.symm edata)
      have hbr' : ∀ (c : Nat) (C : Ctor) (b' : Tm), D.ctors[c]? = some C → bs'.toList[c]? = some b' →
          HasTy0 S Ψ Φ Γ b' (D.branchTy d c C ps' P') := by
        intro c C b' hC hb'
        obtain ⟨b, hb⟩ : ∃ b, bs.toList[c]? = some b :=
          ⟨bs.toList[c]'(by have := (List.getElem?_eq_some_iff.1 hb').1; omega), List.getElem?_eq_getElem _⟩
        exact HasTy0.conv (hpres (eb c C b b' hC hb hb'))
          (branchTy_congr hS hW h0 hC hpres h3 es edata eP hmP)
      have hcoh' : ∀ (c : Nat) (C : Ctor) (b' : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C →
          bs'.toList[c]? = some b' → C.bnd[k]? = some (ψ, e) →
          EqTm0 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps' P' Γ)
            (DataDecl.branchApp C b') (D.bndElim C ps' bs' e) (DataDecl.branchBody d c C ps' P') := by
        intro c C b' k ψ e hC hb' hk
        obtain ⟨b, hb⟩ : ∃ b, bs.toList[c]? = some b :=
          ⟨bs.toList[c]'(by have := (List.getElem?_eq_some_iff.1 hb').1; omega), List.getElem?_eq_getElem _⟩
        have hco := h8 c C b k ψ e hC hb hk
        rw [branchCtx_eq] at hco ⊢
        have hw := wf_of_eq hco
        have hΞ := scoped_of_eq hco
        have he : I.Entails (cof (Φ.ren (· + C.dims)) ψ) (Φ.subst (wkIv C.dims)) := by
          rw [← I_ren_add_eq]; exact ent_and_left _ _
        have eA := branchApp_congr hS hW h0 hC hpres h3 es edata eP (eb c C b b' hC hb hb') hw he
        have eB := bndElim_congr hS hW h0 hC hpres h3 es edata eP h5 hbs' hbl.symm eb hk hw he (ent_and_right _ _)
        have X := EqTm0.trans (EqTm0.symm eA) (EqTm0.trans hco eB)
        have T := ctxConv_branch hS hW h0 hC hpres h3 es edata eP hΞ he
        have X' := (sub_eq hS X).2 T
        have eBody := (sub_eq hS (body_congr hS hW h0 hC hpres h3 es edata eP hw he)).2 T
        rw [subst_var, subst_var, subst_var] at X'
        rw [subst_var, subst_var] at eBody
        exact EqTm0.conv X' eBody
      have ht' := HasTy0.conv (hpres et) edata
      have hel' := HasTy0.elim h0 es.isList' hdata' hpt' hP' hbs' (by rw [hbl, h6]) hbr' hcoh' ht'
      have eT := EqTm0.subst hS eP (hpres eP) h9 (hpres et) et
      exact EqTm0.elim h0 (HasTy0.elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (HasTy0.conv hel' (EqTm0.symm eT))
        es.toEqTele0 eP h5 hbs' hbl.symm (fun c C b b' hC hb hb' => eb c C b b' hC hb hb') et

theorem near_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ∀ {ts'}, TmNear ts ts' →
    ts'.closedB Γ.length Ψ = true → EqTele0 S Ψ Φ Γ ts ts' Δ prev
  | @HasTele0.nil _ Ψ Φ Γ prev hw => fun hn _ => by cases hn; exact EqTele0.nil hw
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev ha has => fun hn hc => by
    cases hn with
    | tcons na nas =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTele0.cons (near_ty ha na hc.1) (near_tele has nas hc.2)

theorem near_teleC {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ∀ {ts'}, TmNear ts ts' →
    ts'.closedB Γ.length Ψ = true → EqTeleS S Ψ Φ Γ ts ts' Δ prev
  | @HasTele0.nil _ Ψ Φ Γ prev hw => fun hn _ => by cases hn; exact EqTeleS.nil hw
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev ha has => fun hn hc => by
    cases hn with
    | tcons na nas =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTeleS.cons (near_ty ha na hc.1) (near_teleC has nas hc.2)

end

end


end KubusCore.Meta
