import Model.Whnf.Near
import Model.Whnf.EquivCongr

/-!
# Near typed terms are judgmentally equal

`near_ty`: if `t` is typed and `t'` is near `t` (`TmNear`: the same shape, interval points equal as
elements of the De Morgan algebra, faces mutually entailing) and has its interval variables in scope,
then `t ≡ t'`. By induction on the typing derivation, using the congruence rules; the right side's
typing is rebuilt from its components.
-/

set_option autoImplicit false

namespace KubusCore.Meta

open Tm Model.Whnf

variable {S : Sig}

theorem ctx_dshift_length (Γ : Ctx) : Γ.dshift.length = Γ.length := List.length_map _

section
variable (hS : SigClosed S) (hT : SigTyped0 S) (hC : ContractaTyped S)
include hS hT hC

theorem eqR0 {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) : HasTy0 S Ψ Φ Γ u A := (pre_eq hS hT hC h).2.1

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
      have hBc : B.closedB (Γ.length + 1) Ψ = true := by simpa using Model.Canon.closed_ty hB0
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
      have eqv := Model.Whnf.equiv_congr hS hT hC eT1 eA1
      have hG' := HasTy0.glue (eqR0 hS hT hC eA) hφ' (eqR0 hS hT hC eT1)
        (HasTy0.conv (HasTy0.restrict hs1 c1 (eqR0 hS hT hC ee)) eqv)
      exact EqTm0.glue (HasTy0.glue hA hφ hT0 he) hG' eA eφ.1 eφ.2 eT ee
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l hG he ht ha hcoh => fun hn hc => by
    cases hn with
    | @glueEl _ e' _ t' _ a' _ φ' eφ ne nt na =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      have hφ' : φ'.Scoped Ψ := (I.scopedB_iff _ _).1 hc.1.1.1
      have hs : Φ.Scoped Ψ := scoped_of_ty ha
      have hcG := Model.Canon.closed_ty hG
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
      have hcG := Model.Canon.closed_ty hG
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
  | _ => sorry

theorem near_tele {Ψ Φ Γ ts Δ prev} : HasTele0 S Ψ Φ Γ ts Δ prev → ∀ {ts'}, TmNear ts ts' →
    ts'.closedB Γ.length Ψ = true → EqTele0 S Ψ Φ Γ ts ts' Δ prev
  | @HasTele0.nil _ Ψ Φ Γ prev hw => fun hn _ => by cases hn; exact EqTele0.nil hw
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev ha has => fun hn hc => by
    cases hn with
    | tcons na nas =>
      simp only [Tm.closedB, Bool.and_eq_true] at hc
      exact EqTele0.cons (near_ty ha na hc.1) (near_tele has nas hc.2)

end

end

end KubusCore.Meta
