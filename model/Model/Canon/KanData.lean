import Model.Canon.KanDerived
import Model.Canon.ArgConv
import Model.Canon.KanPath
import Model.Canon.DataKripke

/-!
# Canonicity: the Kan operations at inductive types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

theorem dataMem_of_ty {Θ : SData m} {f : Hom k m} {T t : Tm} (hsem : semK S k T = res f (dataC Θ))
    (ht : HasTy S k .one [] t T) : dataMem S Θ f k (Hom.id k) t := by
  have := mem_of_ty hW ht
  rw [hsem, El_res, Hom.comp_id, El_dataC] at this
  unfold dataMem
  rw [Hom.comp_id, delemSet_restr, Hom.comp_id]; exact this

theorem kanH_data {Θ : SData m} (hKR : KR S m (dataC Θ)) {f : Hom k m} {T : Tm}
    (hT : (Comp S (dataC Θ) m k f).ty T) : KanH S k T := by
  intro φ u a hty hu ha
  obtain ⟨-, ⟨-, hφ, -, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  by_cases hh : (ival (idEnv k) φ).holds
  · exact RE_hcomp_face hW hty hu hh
  have hT' := hT
  rw [Comp_dataC] at hT'
  obtain ⟨⟨hTy, hsem⟩, ps, hE, hpl, -⟩ := hT'
  unfold RE at ha ⊢
  rw [← Comp_eq_semK hT] at ha ⊢
  rw [Comp_dataC] at ha ⊢
  obtain ⟨hat, -, -, hadr⟩ := ha
  have hMem : ∀ k1 (f1 : Hom k1 k) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t → dataMem S Θ f k1 f1 t' :=
    fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  have hmem : semK S k (.hcomp T φ u a) ∈ El (res f (dataC Θ)) (Hom.id k) := by
    rw [← hsem]; exact mem_of_ty hW hty
  cases hH : (dataD S Θ.idx).isHIT
  · sorry
  · refine ⟨hty, hmem, hty, DR.hcomp (u := u) (a := a) (dataMem_of_ty hW hsem hty) hH hφ hh hpl hE ?_
      (DR.conv hW hMem hadr hE (EqTm.refl (hat.tyConv hE))) (fun k' σ r hr hh' => ?_)⟩
    · rcases hE with rfl | ⟨l, e⟩
      · exact EqTm.refl hty
      · exact (hcomp_retype hW hty e).2
    · have h1 := hu k' σ r hr hh'
      have hTσ := (hKR k f k' σ T T).1 hT
      unfold RE at h1
      rw [← Comp_eq_semK hTσ, Comp_dataC] at h1
      obtain ⟨h1t, -, -, h1dr⟩ := h1
      have h2 := DR.unbase f h1dr
      rw [Hom.comp_id] at h2
      rw [Hom.id_comp]
      exact DR.conv hW hMem h2 (hE.isub hW σ) (EqTm.refl (h1t.tyConv (hE.isub hW σ)))

/-- A computable element of an inductive type, from its relation. -/
theorem RE_of_DR {Θ : SData m} {k0 : ℕ} {f : Hom k0 m} {k' : ℕ} {g : Hom k' k0} {A t : Tm}
    (hty : (Comp S (dataC Θ) m k' (f.comp g)).ty A)
    (hr : DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t) : RE S k' A t := by
  unfold RE; rw [← Comp_eq_semK hty, Comp_dataC]
  refine ⟨hr.typed, ?_, hr.typed, DR.rebase f hr g (Hom.id k') (Hom.comp_id _).symm⟩
  have := hr.mem
  unfold dataMem at this
  rw [res_dataC, El_dataC, delemSet_restr, Hom.comp_id]
  rw [delemSet_restr, Hom.comp_id] at this; exact this

/-- The relation of a computable element of an inductive type. -/
theorem DR_of_RE {Θ : SData m} {k0 : ℕ} {f : Hom k0 m} {k' : ℕ} {g : Hom k' k0} {A t : Tm}
    (hty : (Comp S (dataC Θ) m k' (f.comp g)).ty A) (ht : RE S k' A t) :
    DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t := by
  unfold RE at ht; rw [← Comp_eq_semK hty, Comp_dataC] at ht
  have := DR.unbase f ht.2.2.2
  rwa [Hom.comp_id] at this

omit hW in
theorem skip_isub {τ : ℕ → I} (h0 : τ 0 = .var 0) (h1 : ∀ n, τ (n + 1) = .var (n + 2)) (X u : Tm) (ψ : I)
    {k'' : ℕ} (r : I) (hr : r.Scoped k'') (σ : ISub k'' k') :
    (Tm.transp (X.dsubst τ) ψ.shift u).isub (ISub.cons r hr σ) =
      .transp (X.isub σ.up) (ψ.subst σ.τ) (u.isub (ISub.cons r hr σ)) := by
  show Tm.transp ((X.dsubst τ).subst .var (ISub.cons r hr σ).up.τ) (ψ.shift.subst (ISub.cons r hr σ).τ)
    (u.isub (ISub.cons r hr σ)) = _
  rw [I_shift_cons]
  congr 1
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rw [h0]; rfl
  · rw [h1]; rfl

omit hW in
theorem cons0_comp {k'' : ℕ} (σ : ISub k'' k') :
    (ISub.cons .zero trivial (ISub.id k')).comp σ = σ.up.comp (ISub.cons .zero trivial (ISub.id k'')) := by
  ext i
  rcases i with _ | i
  · rfl
  · show ((ISub.id k').τ i).subst σ.τ = ((σ.τ i).shift).subst (ISub.cons .zero trivial (ISub.id k'')).τ
    rw [I_shift_cons]
    by_cases h : i < k'
    · simp only [ISub.id, if_pos h]
      exact (ISub.I.subst_scoped_id (σ.sc i h) fun j hj => by simp [ISub.id, hj]).symm
    · simp only [ISub.id, if_neg h]; rw [σ.hi i (by omega)]; rfl

/-- Transport along a restriction of a line of inductive types, by induction on the relation of
the transported element (at all its restrictions). -/
theorem transp_data_DR {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hKR : KR S m (dataC Θ)) {k0 : ℕ} {f : Hom (k0 + 1) m} {P : Tm}
    (hT : (Comp S (dataC Θ) m (k0 + 1) f).ty (.data Θ.idx P)) :
    ∀ {k' : ℕ} {g : Hom k' (k0 + 1)} {A t : Tm},
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t →
      ∀ k'' (σ' : ISub k'' k') (ρ : ISub (k'' + 1) (k0 + 1)),
      g.comp σ'.hom = (ρ.comp (ISub.cons .zero trivial (ISub.id k''))).hom →
      TyEq S k'' (A.isub σ') (.data Θ.idx ((P.isub ρ).dinst .zero)) → ∀ ψ : I,
      HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .one)) →
      RE S k'' (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) := by
  have hS := sigClosed_of_wfSig hW
  have hMem : ∀ k1 (f1 : Hom k1 (k0 + 1)) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t →
      dataMem S Θ f k1 f1 t' := fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  -- the common part: the face, and inductive types without parameters
  have common : ∀ {k' : ℕ} {g : Hom k' (k0 + 1)} {A t : Tm},
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t →
      ∀ k'' (σ' : ISub k'' k') (ρ : ISub (k'' + 1) (k0 + 1)),
      g.comp σ'.hom = (ρ.comp (ISub.cons .zero trivial (ISub.id k''))).hom →
      TyEq S k'' (A.isub σ') (.data Θ.idx ((P.isub ρ).dinst .zero)) → ∀ ψ : I,
      HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .one)) →
      ∀ D, S[Θ.idx]? = some (.data D) → ((ival (idEnv k'') ψ).holds ∨ D.params = []) →
      RE S k'' (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) := by
    intro k' g A t hdr k'' σ' ρ hg hA ψ htyT D hD hcase
    obtain ⟨l0, ⟨hLt, hψ, hc, hbase⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW htyT) rfl
    obtain ⟨D', hD', hPt⟩ := gen_data_tele hLt rfl
    rw [hD] at hD'; cases hD'
    have hTρ := (hKR (k0 + 1) f (k'' + 1) ρ (.data Θ.idx P) (.data Θ.idx P)).1 hT
    have hT0 := ty_dinst hW hKR hTρ .zero trivial
    rw [Hom.comp_assoc, ← ISub.hom_comp, ← hg] at hT0
    have hdr' := DR.isub hW hΘ f ihT hdr k'' σ'
    have htRE : RE S k'' (.data Θ.idx ((P.isub ρ).dinst .zero)) (t.isub σ') :=
      RE_of_DR hW hT0 (DR.conv hW hMem hdr' hA (EqTm.refl ((hdr'.typed).tyConv hA)))
    rcases hcase with hh | hp
    · exact RE_transp_face hW htyT hh htRE
    · have e := EqTm.transpData0 hD hp htyT
      have hnil : P.isub ρ = .tnil := by
        have h1 := tele_isList hPt
        have h2 := tele_length hPt
        rw [hp] at h2
        rw [h1, List.eq_nil_of_length_eq_zero h2]; rfl
      rw [hnil] at htRE e ⊢
      exact htRE.conv hW (TyEq.refl _) (EqTm.symm e)
  intro k' g A t h
  induction h with
  | @con k' g A t qs c C args rs hm hC hrs hsc hqs hAeq he hlen hrec hpt ihrec =>
    sorry
  | @hcomp k' g A t qs u a ψ' hm hH hsc hn hqs hAeq he ha hu iha ihu =>
    intro k'' σ' ρ hg hA ψ htyT
    have hdr : DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t := DR.hcomp hm hH hsc hn hqs hAeq he ha hu
    obtain ⟨l0, ⟨hLt, hψ, hc, hbase⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW htyT) rfl
    obtain ⟨D, hD, hPt⟩ := gen_data_tele hLt rfl
    have hdD := dataD_eq hW hD
    by_cases hcase : (ival (idEnv k'') ψ).holds ∨ D.params = []
    · exact common hdr k'' σ' ρ hg hA ψ htyT D hD hcase
    have hp : D.params ≠ [] := fun h => hcase (.inr h)
    have hTρ := (hKR (k0 + 1) f (k'' + 1) ρ (.data Θ.idx P) (.data Θ.idx P)).1 hT
    have hT1 := ty_dinst hW hKR hTρ .one trivial
    -- the restricted composition
    have he' := EqTm.isubS hW he σ'
    have hAeq' := hAeq.isub hW σ'
    have hqL : TyEq S k'' (.data Θ.idx (qs.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .zero)) := hAeq'.symm.trans hW hA
    have hL0 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) hLt (r := .zero) trivial)
    obtain ⟨lq, eq⟩ := tyEq_eq hW hqL ⟨_, hL0⟩
    have hhq : HasTy S k'' .one [] (.hcomp (.data Θ.idx (qs.isub σ')) (ψ'.subst σ'.τ) (u.isub σ'.up) (a.isub σ'))
        (.data Θ.idx (qs.isub σ')) := (HasTy.eqR he').tyConv hAeq'
    obtain ⟨hh0, -⟩ := hcomp_retype hW hhq eq
    have htyT2 : HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ
        (.hcomp (.data Θ.idx (qs.isub σ')) (ψ'.subst σ'.τ) (u.isub σ'.up) (a.isub σ')))
        (.data Θ.idx ((P.isub ρ).dinst .one)) :=
      HasTy.transp (minimal_to_spec hLt) hψ (minimal_to_spec_eq hc) ((HasTy.eqR he').tyConv hA)
    have eb := EqTm.transp htyT htyT2 (EqTm.refl (minimal_to_spec hLt)) (ent_refl _) (ent_refl _) (he'.tyConv hA)
    rw [hdD] at hH
    have eT := EqTm.transpHcomp hD hp hH hh0 htyT2
    have KH := kanH_data hW hKR hT1
    have hbase := iha k'' σ' ρ hg hqL ψ
      (HasTy.transp (minimal_to_spec hLt) hψ (minimal_to_spec_eq hc) ((HasTy.isubS hW ha.typed σ').tyConv hqL))
    refine (KH _ _ _ (HasTy.eqR eT) (fun k3 σ3 r hr hh3 => ?_) hbase).conv hW (TyEq.refl _)
      (EqTm.symm (EqTm.trans eb eT))
    obtain ⟨-, ⟨-, hψ', htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW (HasTy.eqR eT)) rfl
    have hT' := minimal_to_spec (HasTy0.isub hS (Ψ' := k3) (Φ' := .one) (τ := (ISub.cons r hr σ3).τ) htube
      (fun i hi => (ISub.cons r hr σ3).sc i hi) (ent_cof_cons hW hψ' r hr σ3 hh3) (Wf0.nil trivial))
    rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons, skip_isub (by rfl) (fun n => rfl)] at hT'
    rw [isub_up_dinst _ σ3 r hr, skip_isub (by rfl) (fun n => rfl)]
    have eP1 : (Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3 = .data Θ.idx ((P.isub (ρ.comp σ3.up)).dinst .one) := by
      show Tm.data Θ.idx (((P.isub ρ).dinst .one).isub σ3) = _
      rw [isub_dinst, Tm.isub_isub]; rfl
    have eP0 : (Tm.data Θ.idx ((P.isub ρ).dinst .zero)).isub σ3 = .data Θ.idx ((P.isub (ρ.comp σ3.up)).dinst .zero) := by
      show Tm.data Θ.idx (((P.isub ρ).dinst .zero).isub σ3) = _
      rw [isub_dinst, Tm.isub_isub]; rfl
    have eL : (Tm.data Θ.idx (P.isub ρ)).isub σ3.up = .data Θ.idx (P.isub (ρ.comp σ3.up)) := by
      show Tm.data Θ.idx ((P.isub ρ).isub σ3.up) = _
      rw [Tm.isub_isub]
    change HasTy S k3 .one [] _ ((Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3) at hT'
    show RE S k3 ((Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3) _
    have eu : (u.isub σ'.up).isub (ISub.cons r hr σ3) = (u.isub (σ'.comp σ3).up).dinst r := isub_isub_up_cons u σ' r hr σ3
    rw [eP1, eL, eu] at hT' ⊢
    have hcl : ((u.isub (σ'.comp σ3).up).dinst r).closedB 0 k3 = true := by
      have := closed_of_ty hW hT'; simp only [Tm.closedB, Bool.and_eq_true] at this; exact this.2
    have hq' := hqL.isub hW σ3
    rw [eP0] at hq'
    have key := ihu k3 (σ'.comp σ3) r hr (by rw [I_subst_comp]; exact hh3) k3 (ISub.id k3) (ρ.comp σ3.up) ?_ ?_
      (ψ.subst σ3.τ) (by rw [isub_id_of_closed hcl]; exact hT')
    · rwa [isub_id_of_closed hcl] at key
    · rw [ISub.hom_id, Hom.comp_id, ISub.hom_comp, ← Hom.comp_assoc, hg, ← ISub.hom_comp]
      congr 1
      rw [ISub.comp_assoc, cons0_comp, ← ISub.comp_assoc]
    · rw [Tm.isub_isub, ISub.comp_id, ← Tm.isub_isub]; exact hq'
