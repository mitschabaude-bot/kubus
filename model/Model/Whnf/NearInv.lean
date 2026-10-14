import Model.Whnf.NearRel
import Model.Whnf.PerAll

/-!
# The binary relation is invariant under near terms

`NI2 S m X`: at every restriction of the code `X`, a type related to `A'` is related to every typed type
near `A'`, and an element related to `t'` is related to every typed term near `t'` (`TmNear`: interval
points equal in the free De Morgan algebra, faces mutually entailing). By induction on codes, assuming
`NearTy S` (near typed terms are judgmentally equal): the normal forms of near terms are near
(`RedT.near`, `RedE.near`), and the relations are defined through normal forms and eliminations, which
preserve nearness.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

/-- The relations of a code are invariant under near terms on the right. -/
def NI2 (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) (A A' A'' t t' t'' : Tm),
    ((Comp2 S X m k f).ty A A' → TmNear A' A'' → IsTyK S k A'' → (Comp2 S X m k f).ty A A'') ∧
    ((Comp2 S X m k f).ty A A → (Comp2 S X m k f).el A t t' → TmNear t' t'' → HasTy S k .one [] t'' A →
      (Comp2 S X m k f).el A t t'')

variable {S : Sig} {k k' : ℕ}

/-! ### Invariance on both sides, from invariance on the right and the PER properties -/

section
variable {m : ℕ} {X : V} {f : Hom k m} (per : PER2 S m X) (ni : NI2 S m X)
include per ni

omit per in
theorem NI2.tyR {A A' A'' : Tm} (h : (Comp2 S X m k f).ty A A') (hn : TmNear A' A'') (hA : IsTyK S k A'') :
    (Comp2 S X m k f).ty A A'' :=
  (ni k f A A' A'' A A A).1 h hn hA

theorem NI2.tyL {A A' A'' : Tm} (h : (Comp2 S X m k f).ty A' A) (hn : TmNear A' A'') (hA : IsTyK S k A'') :
    (Comp2 S X m k f).ty A'' A :=
  (per k f).symTy (NI2.tyR ni ((per k f).symTy h) hn hA)

theorem NI2.ty2 {A A' B B' : Tm} (h : (Comp2 S X m k f).ty A B) (hA : TmNear A A') (hA' : IsTyK S k A')
    (hB : TmNear B B') (hB' : IsTyK S k B') : (Comp2 S X m k f).ty A' B' :=
  NI2.tyL per ni (NI2.tyR ni h hB hB') hA hA'

theorem NI2.elR {A B t t' t'' : Tm} (hAB : (Comp2 S X m k f).ty A B) (h : (Comp2 S X m k f).el A t t')
    (hn : TmNear t' t'') (ht : HasTy S k .one [] t'' A) : (Comp2 S X m k f).el A t t'' :=
  (ni k f A A A t t' t'').2 ((per k f).reflTy hAB) h hn ht

theorem NI2.elL {A B t t' t'' : Tm} (hAB : (Comp2 S X m k f).ty A B) (h : (Comp2 S X m k f).el A t' t)
    (hn : TmNear t' t'') (ht : HasTy S k .one [] t'' A) : (Comp2 S X m k f).el A t'' t :=
  (per k f).symEl hAB (NI2.elR per ni hAB ((per k f).symEl hAB h) hn ht)

theorem NI2.el2 {A B t t' u u' : Tm} (hAB : (Comp2 S X m k f).ty A B) (h : (Comp2 S X m k f).el A t u)
    (ht : TmNear t t') (ht' : HasTy S k .one [] t' A) (hu : TmNear u u') (hu' : HasTy S k .one [] u' A) :
    (Comp2 S X m k f).el A t' u' :=
  NI2.elL per ni hAB (NI2.elR per ni hAB h hu hu') ht ht'

end


variable (hW : WfSig S)
include hW

theorem good_of_ty {t A : Tm} {Φ : I} (h : HasTy S k Φ [] t A) : goodB S k t = true :=
  good_ty (spec_to_minimal hW h)

theorem good_of_isTyK {A : Tm} (h : IsTyK S k A) : goodB S k A = true := by
  obtain ⟨l, h | rfl⟩ := h
  · exact good_of_ty hW h
  · rfl

/-- A type instance of a `Π`/`Σ` codomain at a typed argument is a type. -/
theorem inst_tyK {A1 B1 a : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A1 B1) (.univ l))
    (ha : HasTy S k .one [] a A1) : IsTyK S k (B1.inst a) :=
  ⟨l, .inl (HasTy.eqL (cod_inst_eq hW hpi (EqTm.refl ha)))⟩

theorem inst_tyKS {A1 B1 a : Tm} {l : ℕ} (hs : HasTy S k .one [] (.sigma A1 B1) (.univ l))
    (ha : HasTy S k .one [] a A1) : IsTyK S k (B1.inst a) :=
  ⟨l, .inl (HasTy.eqL (cod_inst_eqS hW hs (EqTm.refl ha)))⟩

theorem pi_dom {A1 B1 : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A1 B1) (.univ l)) : IsTyK S k A1 :=
  ⟨l, .inl (minimal_to_spec (HasTy0.piDom (sigClosed_of_wfSig hW) (spec_to_minimal hW hpi)))⟩

theorem sigma_dom {A1 B1 : Tm} {l : ℕ} (hs : HasTy S k .one [] (.sigma A1 B1) (.univ l)) : IsTyK S k A1 :=
  ⟨l, .inl (minimal_to_spec (HasTy0.sigmaDom (sigClosed_of_wfSig hW) (spec_to_minimal hW hs)))⟩

variable (hN : NearTy S)
include hN

/-! ### `Π` types -/

section pi
variable {m : ℕ} {A B : V} (hA : A ≠ ∅) (perA : PER2 S m A) (niA : NI2 S m A)
  (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
  (niB : ∀ k (f : Hom k m), ∀ a ∈ El A f, NI2 S k (apZ (dat B k f) a))
include hA perA niA perB niB

omit hA in
theorem cohPi_near {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T') (hn : TmNear T T')
    (hc : cohPi S A B f T) : cohPi S A B f T' := by
  intro k' σ k'' σ' A1 B1 A2 B2 r1 r2
  obtain ⟨W1, r1', w1⟩ := RedT.near hW hN r1 (hT'.isub hW σ) (hn.symm.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases w1 with | pi nA1 nB1 =>
  obtain ⟨W2, r2', w2⟩ := RedT.near hW hN r2 (hT'.isub hW _) (hn.symm.isub _) (good_of_isTyK hW (hT.isub hW _))
  cases w2 with | pi nA2 nB2 =>
  obtain ⟨l1, hpi1⟩ := redT_ty hW (hT'.isub hW σ) r1 (fun l h => by cases h)
  obtain ⟨l2, hpi2⟩ := redT_ty hW (hT'.isub hW _) r2 (fun l h => by cases h)
  have hpi1' := HasTy.isubS hW hpi1 σ'
  rw [isub_pi] at hpi1'
  obtain ⟨c1, c2⟩ := hc k' σ k'' σ' _ _ _ _ r1' r2'
  have P := perA k'' (f.comp (σ.comp σ').hom)
  have hA1 := pi_dom hW hpi1'
  have hA2 := pi_dom hW hpi2
  have d1 := NI2.ty2 perA niA c1 (nA1.isub σ').symm hA1 nA2.symm hA2
  refine ⟨d1, fun a a' ha => ?_⟩
  have e12 : (Comp2 S A m k'' (f.comp (σ.comp σ').hom)).ty (A1.isub σ') (_ : Tm) :=
    NI2.tyL perA niA (P.reflTy c1) (nA1.isub σ').symm hA1
  have ha' := P.conv e12 ha
  have c := c2 a a' ha'
  have hEa := (Comp2_el ha).1
  have hB2 : IsTyK S k'' (B2.inst a') :=
    inst_tyK hW hpi2 (hEa.2.1.tyConv (Comp2_ty_base d1).2.2.2.2.2)
  exact NI2.ty2 (perB _ _ _ (fib_mem ha)) (niB _ _ _ (fib_mem ha)) c
    ((nB1.isub σ').symm.inst (TmNear.refl a)) (inst_tyK hW hpi1' hEa.1) (nB2.symm.inst (TmNear.refl a')) hB2

theorem niTy_piC {f : Hom k m} {T T' T'' : Tm} (h : (Comp2 S (piC m A B) m k f).ty T T') (hn : TmNear T' T'')
    (hT : IsTyK S k T'') : (Comp2 S (piC m A B) m k f).ty T T'' := by
  rw [Comp2_piC A B hA] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  have hT' := hb.2.1
  obtain ⟨e', -⟩ := tyEq_near hW hN hT' hn (good_of_isTyK hW hT)
  refine ⟨⟨hb.1, hT, hb.2.2.1, (semK_tyEq hW e').symm.trans hb.2.2.2.1, hb.2.2.2.2.trans hW e'⟩, fun k' σ => ?_, hc,
    cohPi_near hW hN perA niA perB niB hT' hT hn hc'⟩
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
  obtain ⟨W, h2'', hw⟩ := RedT.near hW hN h2 (hT'.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases hw with | pi nA nB =>
  obtain ⟨l, hpi⟩ := redT_ty hW (hT.isub hW σ) h2'' (fun l h => by cases h)
  have d := NI2.tyR niA h3 nA (pi_dom hW hpi)
  refine ⟨A1, B1, _, _, h1, h2'', d, fun a a'' ha => ?_⟩
  have hEa := (Comp2_el ha).1
  exact NI2.tyR (niB _ _ _ (fib_mem ha)) (h4 a a'' ha)
    (nB.inst (TmNear.refl a'')) (inst_tyK hW hpi (hEa.2.1.tyConv (Comp2_ty_base d).2.2.2.2.2))

omit perA niA in
theorem niEl_piC {f : Hom k m} {T t t' t'' : Tm} (hTT : (Comp2 S (piC m A B) m k f).ty T T)
    (h : (Comp2 S (piC m A B) m k f).el T t t') (hn : TmNear t' t'') (hu : HasTy S k .one [] t'' T) :
    (Comp2 S (piC m A B) m k f).el T t t'' := by
  rw [Comp2_piC A B hA] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨A1, B1, hR, hcod⟩ := hall k1 σ1
  refine ⟨A1, B1, hR, fun a a' ha => ?_⟩
  simp only [ISub.id_comp, ISub.hom_id] at ha hcod ⊢
  have x := hcod a a' ha
  obtain ⟨l1, hpi⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have ea : EqTm S k1 .one [] a' a A1 := ((Comp2_el ha).1.2.2).symm
  have hu1 : HasTy S k1 .one [] (t''.isub σ1) (.pi A1 B1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hBB : (Comp2 S (apZ (dat B k1 (f.comp σ1.hom)) (semK S k1 a)) k1 k1 (Hom.id k1)).ty (B1.inst a) (B1.inst a) := by
    obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, hB⟩ := hTall k1 σ1
    obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
      have := RedW.unique hx.1 hR.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
      have := RedW.unique hy.1 hR.1; injection this; constructor <;> assumption
    exact (perB k1 _ _ (fib_mem ha) k1 (Hom.id k1)).reflTy (hB a a' ha)
  exact NI2.elR (perB _ _ _ (fib_mem ha)) (niB _ _ _ (fib_mem ha)) hBB x (.app (hn.isub σ1) (TmNear.refl a'))
    ((HasTy.app hu1 (Comp2_el ha).1.2.1).tyConv (.inr ⟨l1, cod_inst_eq hW hpi ea⟩))

end pi

/-! ### `Σ` types -/

section sigma
variable {m : ℕ} {A B : V} (hA : A ≠ ∅) (perA : PER2 S m A) (niA : NI2 S m A)
  (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
  (niB : ∀ k (f : Hom k m), ∀ a ∈ El A f, NI2 S k (apZ (dat B k f) a))
include hA perA niA perB niB

omit hA in
theorem cohSigma_near {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T') (hn : TmNear T T')
    (hc : cohSigma S A B f T) : cohSigma S A B f T' := by
  intro k' σ k'' σ' A1 B1 A2 B2 r1 r2
  obtain ⟨W1, r1', w1⟩ := RedT.near hW hN r1 (hT'.isub hW σ) (hn.symm.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases w1 with | sigma nA1 nB1 =>
  obtain ⟨W2, r2', w2⟩ := RedT.near hW hN r2 (hT'.isub hW _) (hn.symm.isub _) (good_of_isTyK hW (hT.isub hW _))
  cases w2 with | sigma nA2 nB2 =>
  obtain ⟨l1, hsg1⟩ := redT_ty hW (hT'.isub hW σ) r1 (fun l h => by cases h)
  obtain ⟨l2, hsg2⟩ := redT_ty hW (hT'.isub hW _) r2 (fun l h => by cases h)
  have hsg1' := HasTy.isubS hW hsg1 σ'
  rw [isub_sigma] at hsg1'
  obtain ⟨c1, c2⟩ := hc k' σ k'' σ' _ _ _ _ r1' r2'
  have P := perA k'' (f.comp (σ.comp σ').hom)
  have hA1 := sigma_dom hW hsg1'
  have hA2 := sigma_dom hW hsg2
  have d1 := NI2.ty2 perA niA c1 (nA1.isub σ').symm hA1 nA2.symm hA2
  refine ⟨d1, fun a a' ha => ?_⟩
  have e12 : (Comp2 S A m k'' (f.comp (σ.comp σ').hom)).ty (A1.isub σ') (_ : Tm) :=
    NI2.tyL perA niA (P.reflTy c1) (nA1.isub σ').symm hA1
  have ha' := P.conv e12 ha
  have c := c2 a a' ha'
  have hEa := (Comp2_el ha).1
  have hB2 : IsTyK S k'' (B2.inst a') :=
    inst_tyKS hW hsg2 (hEa.2.1.tyConv (Comp2_ty_base d1).2.2.2.2.2)
  exact NI2.ty2 (perB _ _ _ (fib_mem ha)) (niB _ _ _ (fib_mem ha)) c
    ((nB1.isub σ').symm.inst (TmNear.refl a)) (inst_tyKS hW hsg1' hEa.1) (nB2.symm.inst (TmNear.refl a')) hB2

theorem niTy_sigmaC {f : Hom k m} {T T' T'' : Tm} (h : (Comp2 S (sigmaC m A B) m k f).ty T T') (hn : TmNear T' T'')
    (hT : IsTyK S k T'') : (Comp2 S (sigmaC m A B) m k f).ty T T'' := by
  rw [Comp2_sigmaC A B hA] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  have hT' := hb.2.1
  obtain ⟨e', -⟩ := tyEq_near hW hN hT' hn (good_of_isTyK hW hT)
  refine ⟨⟨hb.1, hT, hb.2.2.1, (semK_tyEq hW e').symm.trans hb.2.2.2.1, hb.2.2.2.2.trans hW e'⟩, fun k' σ => ?_, hc,
    cohSigma_near hW hN perA niA perB niB hT' hT hn hc'⟩
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
  obtain ⟨W, h2'', hw⟩ := RedT.near hW hN h2 (hT'.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases hw with | sigma nA nB =>
  obtain ⟨l, hsg⟩ := redT_ty hW (hT.isub hW σ) h2'' (fun l h => by cases h)
  have d := NI2.tyR niA h3 nA (sigma_dom hW hsg)
  refine ⟨A1, B1, _, _, h1, h2'', d, fun a a'' ha => ?_⟩
  have hEa := (Comp2_el ha).1
  exact NI2.tyR (niB _ _ _ (fib_mem ha)) (h4 a a'' ha)
    (nB.inst (TmNear.refl a'')) (inst_tyKS hW hsg (hEa.2.1.tyConv (Comp2_ty_base d).2.2.2.2.2))

theorem niEl_sigmaC {f : Hom k m} {T t t' t'' : Tm} (hTT : (Comp2 S (sigmaC m A B) m k f).ty T T)
    (h : (Comp2 S (sigmaC m A B) m k f).el T t t') (hn : TmNear t' t'') (hu : HasTy S k .one [] t'' T) :
    (Comp2 S (sigmaC m A B) m k f).el T t t'' := by
  rw [Comp2_sigmaC A B hA] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have e' := eq_near hW hN hE.2.1 hn (good_of_ty hW hu)
  have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans e'⟩
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨A1, B1, hR, hfst, hsnd⟩ := hall k1 σ1
  simp only [ISub.id_comp, ISub.hom_id] at hfst hsnd ⊢
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, hB⟩ := hTall k1 σ1
  obtain ⟨rfl, rfl⟩ : A1 = A1x ∧ B1 = B1x := by
    have := RedW.unique hR.1 hx.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1 = A1y ∧ B1 = B1y := by
    have := RedW.unique hR.1 hy.1; injection this; constructor <;> assumption
  obtain ⟨l1, hsig⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have hu1 : HasTy S k1 .one [] (t''.isub σ1) (.sigma A1 B1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hfst' := NI2.elR perA niA hAA hfst (.fst (hn.isub σ1)) (HasTy.fst hu1)
  refine ⟨A1, B1, hR, hfst', ?_⟩
  have hfT := (Comp2_el hfst).1
  have ef : EqTm S k1 .one [] (.fst (t'.isub σ1)) (.fst (t''.isub σ1)) A1 :=
    EqTm.fst ((EqTm.isubS hW e' σ1).tyConv hR.2)
  have eB : EqTm S k1 .one [] (B1.inst (.fst (t''.isub σ1))) (B1.inst (.fst (t.isub σ1))) (.univ l1) :=
    cod_inst_eqS hW hsig ((hfT.2.2.trans ef).symm)
  have hBB := (perB k1 _ _ (fib_mem hfst) k1 (Hom.id k1)).reflTy (hB _ _ hfst)
  exact NI2.elR (perB _ _ _ (fib_mem hfst)) (niB _ _ _ (fib_mem hfst)) hBB hsnd (.snd (hn.isub σ1))
    ((HasTy.snd hu1).tyConv (.inr ⟨l1, eB⟩))

end sigma


end

end Model.Whnf
