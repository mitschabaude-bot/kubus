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

theorem HasTy.near' {t t' A : Tm} (h : HasTy S k .one [] t A) (hn : TmNear t t') (hg : goodB S k t' = true) :
    HasTy S k .one [] t' A :=
  HasTy.eqR (eq_near hW hN h hn hg)

omit hW hN in
theorem good_isub {t : Tm} (h : goodB S k t = true) (σ : ISub k' k) : goodB S k' (t.isub σ) = true :=
  goodB_subst t h (fun _ => rfl) fun i hi => sc_iff.2 (σ.sc i hi)

omit hN in
/-- The normal form of a good type is good. -/
theorem good_whnf {T W : Tm} (h : RedT S k T W) (hg : goodB S k T = true) : goodB S k W = true :=
  red_good hW h.1.1 hg

omit hN in
theorem RedT.isTyK {T W : Tm} (h : RedT S k T W) (hT : IsTyK S k T) : IsTyK S k W := by
  rcases h.2 with e | ⟨l, e⟩
  · exact e ▸ hT
  · exact ⟨l, .inl (HasTy.eqR e)⟩

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


/-! ### Path types -/

section path
variable {m : ℕ} {L a0 a1 : V} (hLne : L ≠ ∅) (perL : PER2 S (m + 1) L) (niL : NI2 S (m + 1) L)
include hLne perL niL

omit hLne in
theorem cohPath_near {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T') (hn : TmNear T T')
    (hc : cohPath S L f T)
    (hrefl : ∀ k' (σ : ISub k' k) L2 c0 c1, RedT S k' (T.isub σ) (.path L2 c0 c1) → ∀ (r : I) (hr : r.Scoped k'),
      (Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r hr σ).hom)).ty (L2.dinst r) (L2.dinst r)) :
    cohPath S L f T' := by
  intro k' σ k'' σ' L1 b0 b1 L2 c0 c1 r1 r2
  have g1 := good_whnf hW r1 (good_of_isTyK hW (hT'.isub hW σ))
  have g2 := good_whnf hW r2 (good_of_isTyK hW (hT'.isub hW _))
  simp only [goodB, Bool.and_eq_true] at g1 g2
  obtain ⟨W1, r1', w1⟩ := RedT.near hW hN r1 (hT'.isub hW σ) (hn.symm.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases w1 with | path nL1 nb0 nb1 =>
  obtain ⟨W2, r2', w2⟩ := RedT.near hW hN r2 (hT'.isub hW _) (hn.symm.isub _) (good_of_isTyK hW (hT.isub hW _))
  cases w2 with | path nL2 nc0 nc1 =>
  obtain ⟨c1x, c2x, c3x⟩ := hc k' σ k'' σ' _ _ _ _ _ _ r1' r2'
  have bL := Comp2_ty_base c1x
  have hL1 := (tyEq_near hW hN bL.2.1 (nL1.isub σ'.up).symm (good_isub g1.1.1 σ'.up)).2
  have hL2 := (tyEq_near hW hN bL.2.2.1 nL2.symm g2.1.1).2
  refine ⟨NI2.ty2 perL niL c1x (nL1.isub σ'.up).symm hL1 nL2.symm hL2, ?_, ?_⟩
  · have hR := hrefl k'' (σ.comp σ') _ _ _ r2' .zero trivial
    have hd := (tyEq_near hW hN (Comp2_ty_base hR).2.1 (nL2.symm.dinst (I_eq_refl _)) (goodB_dinst g2.1.1 rfl)).2
    have e := NI2.tyR niL hR (nL2.symm.dinst (I_eq_refl _)) hd
    have x := (perL _ _).conv e c2x
    have hx := (Comp2_el x).1
    exact NI2.el2 perL niL ((perL _ _).reflTy' e) x (nb0.isub σ').symm
      (HasTy.near' hW hN hx.1 (nb0.isub σ').symm (good_isub g1.1.2 σ')) nc0.symm
      (HasTy.near' hW hN hx.2.1 nc0.symm g2.1.2)
  · have hR := hrefl k'' (σ.comp σ') _ _ _ r2' .one trivial
    have hd := (tyEq_near hW hN (Comp2_ty_base hR).2.1 (nL2.symm.dinst (I_eq_refl _)) (goodB_dinst g2.1.1 rfl)).2
    have e := NI2.tyR niL hR (nL2.symm.dinst (I_eq_refl _)) hd
    have x := (perL _ _).conv e c3x
    have hx := (Comp2_el x).1
    exact NI2.el2 perL niL ((perL _ _).reflTy' e) x (nb1.isub σ').symm
      (HasTy.near' hW hN hx.1 (nb1.isub σ').symm (good_isub g1.2 σ')) nc1.symm
      (HasTy.near' hW hN hx.2.1 nc1.symm g2.2)

theorem niTy_pathC {f : Hom k m} {T T' T'' : Tm} (h : (Comp2 S (pathC m L a0 a1) m k f).ty T T')
    (hn : TmNear T' T'') (hT : IsTyK S k T'') : (Comp2 S (pathC m L a0 a1) m k f).ty T T'' := by
  rw [Comp2_pathC L a0 a1 hLne] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  have hT' := hb.2.1
  obtain ⟨e', -⟩ := tyEq_near hW hN hT' hn (good_of_isTyK hW hT)
  have hrefl : ∀ k' (σ : ISub k' k) L2 c0 c1, RedT S k' (T'.isub σ) (.path L2 c0 c1) → ∀ (r : I) (hr : r.Scoped k'),
      (Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r hr σ).hom)).ty (L2.dinst r) (L2.dinst r) := by
    intro k' σ L2 c0 c1 hR r hr
    obtain ⟨L1, b0, b1, L1', b0', b1', -, h2, -, h4, -, -⟩ := hall k' σ
    obtain ⟨rfl, -, -⟩ : L1' = L2 ∧ b0' = c0 ∧ b1' = c1 := by
      have := RedW.unique h2.1 hR.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
    exact (perL _ _).reflTy' (h4 r r hr hr (I_eq_refl _))
  refine ⟨⟨hb.1, hT, hb.2.2.1, (semK_tyEq hW e').symm.trans hb.2.2.2.1, hb.2.2.2.2.trans hW e'⟩, fun k' σ => ?_, hc,
    cohPath_near hW hN perL niL hT' hT hn hc' hrefl⟩
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5, h6⟩ := hall k' σ
  obtain ⟨W, h2'', hw⟩ := RedT.near hW hN h2 (hT'.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases hw with | path nL n0 n1 =>
  have g := good_whnf hW h2'' (good_of_isTyK hW (hT.isub hW σ))
  simp only [goodB, Bool.and_eq_true] at g
  have hL := (tyEq_near hW hN (Comp2_ty_base h3).2.2.1 nL g.1.1).2
  refine ⟨L1, b0, b1, _, _, _, h1, h2'', NI2.tyR niL h3 nL hL, fun r r' hr hr' he => ?_, ?_, ?_⟩
  · have x := h4 r r' hr hr' he
    exact NI2.tyR niL x (nL.dinst (I_eq_refl _))
      (tyEq_near hW hN (Comp2_ty_base x).2.2.1 (nL.dinst (I_eq_refl _)) (goodB_dinst g.1.1 (sc_iff.2 hr'))).2
  · exact NI2.elR perL niL ((perL _ _).reflTy (h4 .zero .zero trivial trivial (I_eq_refl _))) h5 n0
      (HasTy.near' hW hN (Comp2_el h5).1.2.1 n0 g.1.2)
  · exact NI2.elR perL niL ((perL _ _).reflTy (h4 .one .one trivial trivial (I_eq_refl _))) h6 n1
      (HasTy.near' hW hN (Comp2_el h6).1.2.1 n1 g.2)

theorem niEl_pathC {f : Hom k m} {T t t' t'' : Tm} (hTT : (Comp2 S (pathC m L a0 a1) m k f).ty T T)
    (h : (Comp2 S (pathC m L a0 a1) m k f).el T t t') (hn : TmNear t' t'') (hu : HasTy S k .one [] t'' T) :
    (Comp2 S (pathC m L a0 a1) m k f).el T t t'' := by
  rw [Comp2_pathC L a0 a1 hLne] at h hTT ⊢
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨L1, b0, b1, hR, hp, e0, e1⟩ := hall k1 σ1
  refine ⟨L1, b0, b1, hR, fun r r' hr hr' he => ?_, e0, e1⟩
  simp only [ISub.id_comp] at hp ⊢
  have x := hp r r' hr hr' he
  have hx := (Comp2_el x).1
  have hn1 : TmNear (Tm.papp (t'.isub σ1) r') (Tm.papp (t''.isub σ1) r') := .papp (hn.isub σ1) (I_eq_refl _)
  have hg : goodB S k1 (Tm.papp (t''.isub σ1) r') = true := by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_isub (good_of_ty hW hu) σ1, sc_iff.2 hr'⟩
  have hLL : (Comp2 S L (m + 1) k1 ((Hom.lift f).comp (ISub.cons r hr σ1).hom)).ty (L1.dinst r) (L1.dinst r) := by
    obtain ⟨L1x, b0x, b1x, L1y, b0y, b1y, hx, hy, -, hrr, -, -⟩ := hTT.2.1 k1 σ1
    obtain ⟨rfl, -, -⟩ : L1x = L1 ∧ True ∧ True := by
      have := RedW.unique hx.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
    obtain ⟨rfl, -, -⟩ : L1y = L1x ∧ True ∧ True := by
      have := RedW.unique hy.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
    exact (perL _ _).reflTy (hrr r r hr hr (I_eq_refl _))
  exact NI2.elR perL niL hLL x hn1 (HasTy.near' hW hN hx.2.1 hn1 hg)

end path

/-! ### `(i : I) → L` -/

section ipi
variable {m : ℕ} {L : V} (hLne : L ≠ ∅) (perL : PER2 S (m + 1) L) (niL : NI2 S (m + 1) L)
include hLne perL niL

omit hLne in
theorem cohIPi_near {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T') (hn : TmNear T T')
    (hc : cohIPi S L f T) : cohIPi S L f T' := by
  intro k' σ k'' σ' L1 L2 r1 r2
  have g1 := good_whnf hW r1 (good_of_isTyK hW (hT'.isub hW σ))
  have g2 := good_whnf hW r2 (good_of_isTyK hW (hT'.isub hW _))
  simp only [goodB] at g1 g2
  obtain ⟨W1, r1', w1⟩ := RedT.near hW hN r1 (hT'.isub hW σ) (hn.symm.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases w1 with | ipi nL1 =>
  obtain ⟨W2, r2', w2⟩ := RedT.near hW hN r2 (hT'.isub hW _) (hn.symm.isub _) (good_of_isTyK hW (hT.isub hW _))
  cases w2 with | ipi nL2 =>
  have c1x := hc k' σ k'' σ' _ _ r1' r2'
  have bL := Comp2_ty_base c1x
  have hL1 := (tyEq_near hW hN bL.2.1 (nL1.isub σ'.up).symm (good_isub g1 σ'.up)).2
  have hL2 := (tyEq_near hW hN bL.2.2.1 nL2.symm g2).2
  exact NI2.ty2 perL niL c1x (nL1.isub σ'.up).symm hL1 nL2.symm hL2

theorem niTy_ipiC {f : Hom k m} {T T' T'' : Tm} (h : (Comp2 S (ipiC m L) m k f).ty T T')
    (hn : TmNear T' T'') (hT : IsTyK S k T'') : (Comp2 S (ipiC m L) m k f).ty T T'' := by
  rw [Comp2_ipiC L hLne] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  have hT' := hb.2.1
  obtain ⟨e', -⟩ := tyEq_near hW hN hT' hn (good_of_isTyK hW hT)
  refine ⟨⟨hb.1, hT, hb.2.2.1, (semK_tyEq hW e').symm.trans hb.2.2.2.1, hb.2.2.2.2.trans hW e'⟩, fun k' σ => ?_, hc,
    cohIPi_near hW hN perL niL hT' hT hn hc'⟩
  obtain ⟨L1, L1', h1, h2, h3, h4⟩ := hall k' σ
  obtain ⟨W, h2'', hw⟩ := RedT.near hW hN h2 (hT'.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
  cases hw with | ipi nL =>
  have g := good_whnf hW h2'' (good_of_isTyK hW (hT.isub hW σ))
  simp only [goodB] at g
  have hL := (tyEq_near hW hN (Comp2_ty_base h3).2.2.1 nL g).2
  refine ⟨L1, _, h1, h2'', NI2.tyR niL h3 nL hL, fun r r' hr hr' he => ?_⟩
  have x := h4 r r' hr hr' he
  exact NI2.tyR niL x (nL.dinst (I_eq_refl _))
    (tyEq_near hW hN (Comp2_ty_base x).2.2.1 (nL.dinst (I_eq_refl _)) (goodB_dinst g (sc_iff.2 hr'))).2

theorem niEl_ipiC {f : Hom k m} {T t t' t'' : Tm} (hTT : (Comp2 S (ipiC m L) m k f).ty T T)
    (h : (Comp2 S (ipiC m L) m k f).el T t t') (hn : TmNear t' t'') (hu : HasTy S k .one [] t'' T) :
    (Comp2 S (ipiC m L) m k f).el T t t'' := by
  rw [Comp2_ipiC L hLne] at h hTT ⊢
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨L1, hR, hp⟩ := hall k1 σ1
  refine ⟨L1, hR, fun r r' hr hr' he => ?_⟩
  simp only [ISub.id_comp] at hp ⊢
  have x := hp r r' hr hr' he
  have hx := (Comp2_el x).1
  have hn1 : TmNear (Tm.papp (t'.isub σ1) r') (Tm.papp (t''.isub σ1) r') := .papp (hn.isub σ1) (I_eq_refl _)
  have hg : goodB S k1 (Tm.papp (t''.isub σ1) r') = true := by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_isub (good_of_ty hW hu) σ1, sc_iff.2 hr'⟩
  have hLL : (Comp2 S L (m + 1) k1 ((Hom.lift f).comp (ISub.cons r hr σ1).hom)).ty (L1.dinst r) (L1.dinst r) := by
    obtain ⟨L1x, L1y, hx, hy, -, hrr⟩ := hTT.2.1 k1 σ1
    obtain rfl : L1x = L1 := by have := RedW.unique hx.1 hR.1; injection this
    obtain rfl : L1y = L1x := by have := RedW.unique hy.1 hR.1; injection this
    exact (perL _ _).reflTy (hrr r r hr hr (I_eq_refl _))
  exact NI2.elR perL niL hLL x hn1 (HasTy.near' hW hN hx.2.1 hn1 hg)

end ipi

/-! ### The empty type and universes -/

theorem base_near {m : ℕ} {X : V} {f : Hom k m} {T T' T'' : Tm}
    (hb : IsTyK S k T ∧ IsTyK S k T' ∧ semK S k T = res f X ∧ semK S k T' = res f X ∧ TyEq S k T T')
    (hn : TmNear T' T'') (hT : IsTyK S k T'') :
    IsTyK S k T ∧ IsTyK S k T'' ∧ semK S k T = res f X ∧ semK S k T'' = res f X ∧ TyEq S k T T'' := by
  obtain ⟨e', -⟩ := tyEq_near hW hN hb.2.1 hn (good_of_isTyK hW hT)
  exact ⟨hb.1, hT, hb.2.2.1, (semK_tyEq hW e').symm.trans hb.2.2.2.1, hb.2.2.2.2.trans hW e'⟩

theorem ni2_emptyC {m : ℕ} : NI2 S m (emptyC m) := by
  intro k f T T' T'' t t' t''
  rw [Comp2_emptyC]
  exact ⟨fun h hn hT => base_near hW hN h hn hT, fun _ h => h.elim⟩

theorem ni2_univC {m l : ℕ} (ih : ∀ m' X, WF l m' X → NI2 S m' X) : NI2 S m (univC m l) := by
  intro k f T T' T'' t t' t''
  rw [Comp2_univC]
  refine ⟨fun h hn hT => ⟨base_near hW hN h.1 hn hT, fun k' σ => ?_⟩, fun hTT h hn hu => ?_⟩
  · obtain ⟨h1, h2⟩ := h.2 k' σ
    obtain ⟨W, h2', hw⟩ := RedT.near hW hN h2 (h.1.2.1.isub hW σ) (hn.isub σ) (good_of_isTyK hW (hT.isub hW σ))
    cases hw
    exact ⟨h1, h2'⟩
  · obtain ⟨hE, hmem, hm, hty⟩ := h
    have hE' : EB S k T t t'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
    refine ⟨hE', hmem, hm, ?_⟩
    have hWF : WF l k (semK S k t) := (ZFSet.mem_sep.1 hm).2
    have hU : TyEq S k T (.univ l) := by
      have := (hTT.2 k (ISub.id k)).1.2
      rwa [isub_id_of_closed (closed_of_isTyK hW hTT.1.1)] at this
    exact (ih k _ hWF k (Hom.id k) t t' t'' t t' t'').1 hty hn (tyk (hu.tyConv hU))

omit hW hN in
/-- Mutually entailing cofibrations have the same face. -/
theorem face_eq_of_feq {φ ψ : I} (h : FEq φ ψ) : (ival (idEnv k) φ).face = (ival (idEnv k) ψ).face := by
  have hK : ∀ p : Pt k, p.IsK3 → Meta.K3Asg (Pt.rev p) := by
    intro p hp i
    simp only [Pt.rev]
    split
    · exact hp _
    · simp [Meta.isK3]
  ext p
  simp only [DM.face, Set.mem_setOf_eq, ival_idEnv_fn]
  constructor
  · rintro ⟨h3, hv⟩; exact ⟨h3, Meta.entails_iff.1 h.1 _ (hK p h3) hv⟩
  · rintro ⟨h3, hv⟩; exact ⟨h3, Meta.entails_iff.1 h.2 _ (hK p h3) hv⟩

/-! ### Families of relations: invariance of the element relations -/

/-- The element relation of a pack is invariant under near terms on the right, at types related to themselves. -/
def NIel (S : Sig) (k : ℕ) (R : Pack2) : Prop :=
  ∀ A t t' t'', R.ty A A → R.el A t t' → TmNear t' t'' → HasTy S k .one [] t'' A → R.el A t t''

/-- A family of packs whose element relations are invariant under near terms. -/
def FamNI (S : Sig) (n : ℕ) (P : (k' : ℕ) → ISub k' n → Pack2) : Prop := ∀ k' (σ : ISub k' n), NIel S k' (P k' σ)

section fam
variable {n : ℕ}

theorem piF_ni {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : FamOK S n D) (hC : FamOK S n Cf) (nC : FamNI S n Cf) :
    FamNI S n (piF S D Cf) := by
  intro k' σ X t t' t'' hXX h hn hu
  obtain ⟨hE, hall⟩ := h
  refine ⟨⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hR, hel⟩ := hall k'' σ'
  refine ⟨A1, B1, hR, fun a a' ha => ?_⟩
  simp only [ISub.id_comp] at ha hel ⊢
  have x := hel a a' ha
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, -, h4⟩ := hXX.2 k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hx.1 hR.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hy.1 hR.1; injection this; constructor <;> assumption
  have hBB := (hC.per _ _).reflTy (h4 a a' ha)
  have hx' := hC.elEB _ _ _ _ _ x
  have ha' := (hD.elEB _ _ _ _ _ ha).2.1
  have hn1 : TmNear (Tm.app (t'.isub σ') a') (Tm.app (t''.isub σ') a') := .app (hn.isub σ') (TmNear.refl _)
  have hg : goodB S k'' (Tm.app (t''.isub σ') a') = true := by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_isub (good_of_ty hW hu) σ', good_of_ty hW ha'⟩
  exact nC _ _ _ _ _ _ hBB x hn1 (HasTy.near' hW hN hx'.2.1 hn1 hg)

theorem sigF_ni {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : FamOK S n D) (hC : FamOK S n Cf) (nD : FamNI S n D)
    (nC : FamNI S n Cf) : FamNI S n (sigF S D Cf) := by
  intro k' σ X t t' t'' hXX h hn hu
  obtain ⟨hE, hall⟩ := h
  refine ⟨⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hR, hfst, hsnd⟩ := hall k'' σ'
  simp only [ISub.id_comp] at hfst hsnd ⊢
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, h4⟩ := hXX.2 k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hx.1 hR.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hy.1 hR.1; injection this; constructor <;> assumption
  have hg := good_isub (good_of_ty hW hu) σ'
  have n1 : TmNear (Tm.fst (t'.isub σ')) (Tm.fst (t''.isub σ')) := .fst (hn.isub σ')
  have n2 : TmNear (Tm.snd (t'.isub σ')) (Tm.snd (t''.isub σ')) := .snd (hn.isub σ')
  have hf := hD.elEB _ _ _ _ _ hfst
  have hs := hC.elEB _ _ _ _ _ hsnd
  refine ⟨_, _, hR, nD _ _ _ _ _ _ ((hD.per _ _).reflTy hAA) hfst n1 (HasTy.near' hW hN hf.2.1 n1 hg),
    nC _ _ _ _ _ _ ((hC.per _ _).reflTy (h4 _ _ hfst)) hsnd n2 (HasTy.near' hW hN hs.2.1 n2 hg)⟩

theorem pathF_ni {AP : (k' : ℕ) → ISub k' n → Pack2} (hA : FamOK S n AP) (nA : FamNI S n AP) :
    FamNI S n (pathF S AP) := by
  intro k' σ X t t' t'' hXX h hn hu
  obtain ⟨hE, hall⟩ := h
  refine ⟨⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩, fun k'' σ' => ?_⟩
  obtain ⟨L1, b0, b1, hR, hp, e0, e1⟩ := hall k'' σ'
  refine ⟨L1, b0, b1, hR, fun r r' hr hr' he => ?_, e0, e1⟩
  simp only [ISub.id_comp] at hp ⊢
  have x := hp r r' hr hr' he
  obtain ⟨L1x, b0x, b1x, L1y, b0y, b1y, hx, hy, -, hrr, -, -⟩ := hXX.2 k'' σ'
  obtain ⟨rfl, -, -⟩ : L1x = L1 ∧ True ∧ True := by
    have := RedW.unique hx.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
  obtain ⟨rfl, -, -⟩ : L1y = L1x ∧ True ∧ True := by
    have := RedW.unique hy.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
  have hLL := (hA.per _ _).reflTy (hrr r r hr hr (I_eq_refl _))
  have hx' := hA.elEB _ _ _ _ _ x
  have hn1 : TmNear (Tm.papp (t'.isub σ') r') (Tm.papp (t''.isub σ') r') := .papp (hn.isub σ') (I_eq_refl _)
  have hg : goodB S k'' (Tm.papp (t''.isub σ') r') = true := by
    simp only [goodB, Bool.and_eq_true]; exact ⟨good_isub (good_of_ty hW hu) σ', sc_iff.2 hr'⟩
  exact nA _ _ _ _ _ _ hLL x hn1 (HasTy.near' hW hN hx'.2.1 hn1 hg)

theorem equivF_ni {TP AP : (k' : ℕ) → ISub k' n → Pack2} (hT : FamOK S n TP) (hA : FamOK S n AP)
    (nT : FamNI S n TP) (nA : FamNI S n AP) : FamNI S n (equivF S TP AP) := by
  have hF := sigF_ok hW hT (pathF_ok hW hA)
  have nF := sigF_ni hW hN hT (pathF_ok hW hA) nT (pathF_ni hW hN hA nA)
  exact sigF_ni hW hN (piF_ok hW hT hA) (piF_ok hW hA (sigF_ok hW hF (piF_ok hW hF (pathF_ok hW hF))))
    (piF_ni hW hN hT hA nA)
    (piF_ni hW hN hA (sigF_ok hW hF (piF_ok hW hF (pathF_ok hW hF)))
      (sigF_ni hW hN hF (piF_ok hW hF (pathF_ok hW hF)) nF (piF_ni hW hN hF (pathF_ok hW hF) (pathF_ni hW hN hF nF))))

end fam

omit hW hN in
theorem famNI_comp2 {m n0 n : ℕ} {X : V} (ni : NI2 S m X) (g : Hom n0 m) (ρ : ISub n n0) :
    FamNI S n fun k3 σ3 => Comp2 S X m k3 (g.comp (ρ.comp σ3).hom) :=
  fun k3 σ3 A t t' t'' hAA h hn hu => (ni k3 _ A A A t t' t'').2 hAA h hn hu

omit hW hN in
theorem famNI_comp2_id {n : ℕ} {X : V} (ni : NI2 S n X) : FamNI S n fun k3 σ3 => Comp2 S X n k3 σ3.hom :=
  fun k3 σ3 A t t' t'' hAA h hn hu => (ni k3 _ A A A t t' t'').2 hAA h hn hu

/-! ### Glue types -/

section glue
variable {m : ℕ} {A Tp : V} {φ : Cof m} (perA : PER2 S m A) (krA : KR2 S m A) (niA : NI2 S m A)
  (perT : ∀ k (f : Hom k m), (φ.restr f).holds → PER2 S k (dat Tp k f))
  (krT : ∀ k (f : Hom k m), (φ.restr f).holds → KR2 S k (dat Tp k f))
  (niT : ∀ k (f : Hom k m), (φ.restr f).holds → NI2 S k (dat Tp k f)) (f : Hom k m)
include perA krA niA perT krT niT

theorem glueLocT_near {k' : ℕ} (σ : ISub k' k) {Y Z Z'' : Tm} (hY : IsTyK S k' Y) (hZ : IsTyK S k' Z)
    (hZ'' : IsTyK S k' Z'') (h : glueLocT S A Tp φ f k' σ Y Z) (hn : TmNear Z Z'') : glueLocT S A Tp φ f k' σ Y Z'' := by
  unfold glueLocT at h ⊢
  split_ifs at h ⊢ with hh
  · exact NI2.tyR (niT k' _ hh) h hn hZ''
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', h1, h2, s1, s2, f1, f2, hAA, hT⟩ := h
  obtain ⟨W, h2'', hw⟩ := RedT.near hW hN h2 hZ hn (good_of_isTyK hW hZ'')
  cases hw with | glue nA nφ nT ne =>
  have g := good_whnf hW h2'' (good_of_isTyK hW hZ'')
  simp only [goodB, Bool.and_eq_true] at g
  have hA1 := (tyEq_near hW hN (Comp2_ty_base hAA).2.2.1 nA g.1.1.1).2
  refine ⟨A1, φ1, T1, e1, _, _, _, _, h1, h2'', s1, sc_iff.1 g.1.1.2, f1, (face_eq_of_feq nφ).symm.trans f2,
    NI2.tyR niA hAA nA hA1, fun k'' σ' hh' => ?_⟩
  obtain ⟨c1, c2⟩ := hT k'' σ' hh'
  have hT1 := (tyEq_near hW hN (Comp2_ty_base c1).2.2.1 (nT.isub σ') (good_isub g.1.2 σ')).2
  refine ⟨NI2.tyR (niT k'' _ hh') c1 (nT.isub σ') hT1, ?_⟩
  have FT := famOK_comp2_id (perT k'' _ hh') (krT k'' _ hh')
  have FA := famOK_comp2 perA krA f (σ.comp σ')
  have hE := glue_equivTy hW perA krA perT krT f σ hY hY h1 h1 f1 f1 ((perA _ _).reflTy hAA) σ' hh'
    ((perT k'' _ hh' _ _).reflTy c1)
  have hx := ((equivF_ok hW _ _ FT FA).elEB _ _ _ _ _ c2)
  exact equivF_ni hW hN FT FA (famNI_comp2_id (niT k'' _ hh')) (famNI_comp2 niA f (σ.comp σ')) k'' (ISub.id k'')
    _ _ _ _ ((equivF_ok hW _ _ FT FA).per _ _ |>.reflTy hE) c2 (ne.isub σ')
    (HasTy.near' hW hN hx.2.1 (ne.isub σ') (good_isub g.2 σ'))

theorem glueLocE_near {k' : ℕ} (σ : ISub k' k) {X g g' g'' : Tm} (hX : glueLocT S A Tp φ f k' σ X X)
    (h : glueLocE S A Tp φ f k' σ X g g') (hn : TmNear g' g'') (hu : HasTy S k' .one [] g'' X) :
    glueLocE S A Tp φ f k' σ X g g'' := by
  unfold glueLocT at hX
  unfold glueLocE at h ⊢
  split_ifs at h hX ⊢ with hh
  · exact NI2.elR (perT k' _ hh) (niT k' _ hh) hX h hn hu
  obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', i1, i2, i3, i4, E0, E0', ha, hrest⟩ := h
  obtain ⟨A1x, φ1x, T1x, e1x, A1y, φ1y, T1y, e1y, hx1, hx2, -, -, -, -, hAA, hTT⟩ := hX
  obtain ⟨rfl, rfl, rfl, rfl⟩ : A1x = A1 ∧ φ1x = φ1 ∧ T1x = T1 ∧ e1x = e1 := by
    have := RedW.unique hx1.1 r1.1; injection this; exact ⟨by assumption, by assumption, by assumption, by assumption⟩
  obtain ⟨w, rg'', hw⟩ := RedE.near hW hN rg' (HasTy.eqL rg'.2) hn (good_of_ty hW hu)
  cases hw with | glueEl nψ ne0 nt0 na0 =>
  have g := red_good hW rg''.1.1 (good_of_ty hW hu)
  simp only [goodB, Bool.and_eq_true] at g
  have ht0 := HasTy.eqL E0'
  have E0'' := (hN ht0 ne0 (closed_of_near_good ne0 (closed_ty (spec_to_minimal hW ht0)) g.1.1.2)).symm.trans E0'
  have hAr := (perA _ _).reflTy hAA
  have ha' := (Comp2_el ha).1
  refine ⟨A1x, φ1x, T1x, e1x, ψ, e0, t0, a0, _, _, _, _, r1, rg, rg'', i1, i2, ent_trans nψ.2 i3, ent_trans i4 nψ.1,
    E0, E0'', NI2.elR perA niA hAr ha na0 (HasTy.near' hW hN ha'.2.1 na0 g.2), fun k'' σ' hh' => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hrest k'' σ' hh'
  have hT1 := (perT k'' _ hh' _ _).reflTy (hTT k'' σ' hh').1
  have hA1 : (Comp2 S A m k'' (f.comp (σ.comp σ').hom)).ty (A1x.isub σ') (A1x.isub σ') := by
    have := (krA k' (f.comp σ.hom) k'' σ' A1x A1x A1x A1x).1 hAr
    rwa [ISub.comp_hom] at this
  have x1 := (Comp2_el c1).1
  have x3 := (Comp2_el c3).1
  have na := na0.isub σ'
  have nt := nt0.isub σ'
  have napp := TmNear.app (.fst (TmNear.refl (e1x.isub σ'))) nt
  have ge1 : goodB S k'' (e1x.isub σ') = true := by
    have := good_whnf hW hx1 (good_of_isTyK hW (isTyK_of_ty hW (HasTy.eqL rg.2)))
    simp only [goodB, Bool.and_eq_true] at this
    exact good_isub this.2 σ'
  refine ⟨NI2.elR (perT k'' _ hh') (niT k'' _ hh') hT1 c1 nt (HasTy.near' hW hN x1.2.1 nt (good_isub g.1.2 σ')), c2,
    NI2.el2 perA niA hA1 c3 na (HasTy.near' hW hN x3.1 na (good_isub g.2 σ')) napp
      (HasTy.near' hW hN x3.2.1 napp ?_)⟩
  simp only [goodB, Bool.and_eq_true]
  exact ⟨ge1, good_isub g.1.2 σ'⟩

omit niA niT in
/-- Where the face does not hold, the normal forms of the right side of related Glue types are types. -/
theorem glueLocT_whnfR {k' : ℕ} (σ : ISub k' k) {Y Z W : Tm} (hh : ¬ (φ.restr (f.comp σ.hom)).holds)
    (h : glueLocT S A Tp φ f k' σ Y Z) (hZ : IsTyK S k' Z) (hw : RedW S Z W) : IsTyK S k' W := by
  unfold glueLocT at h
  rw [if_neg hh] at h
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', _, h2, _⟩ := h
  rw [RedW.unique hw h2.1]
  exact RedT.isTyK hW h2 hZ

theorem glueLocT_near2 {k' : ℕ} (σ : ISub k' k) {Y Y' Z Z' : Tm} (hY : IsTyK S k' Y) (hY' : IsTyK S k' Y')
    (hZ : IsTyK S k' Z) (hZ' : IsTyK S k' Z') (h : glueLocT S A Tp φ f k' σ Y Z) (hnY : TmNear Y Y')
    (hnZ : TmNear Z Z') : glueLocT S A Tp φ f k' σ Y' Z' := by
  have h1 := glueLocT_near hW hN perA krA niA perT krT niT f σ hY hZ hZ' h hnZ
  have h2 := glueLocT_symm hW perA krA perT krT f σ hY hZ' h1
  exact glueLocT_symm hW perA krA perT krT f σ hZ' hY'
    (glueLocT_near hW hN perA krA niA perT krT niT f σ hZ' hY hY' h2 hnY)

omit niA niT in
/-- Where the face does not hold, the normal forms of the right side of related Glue elements are typed. -/
theorem glueLocE_whnfR {k' : ℕ} (σ : ISub k' k) {X g g' w : Tm} (hh : ¬ (φ.restr (f.comp σ.hom)).holds)
    (h : glueLocE S A Tp φ f k' σ X g g') (hw : RedW S g' w) : HasTy S k' .one [] w X := by
  unfold glueLocE at h
  rw [if_neg hh] at h
  obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', _, _, rg', _⟩ := h
  rw [RedW.unique hw rg'.1]
  exact HasTy.eqR rg'.2

theorem glueLocE_near2 {k' : ℕ} (σ : ISub k' k) {X g g' u u' : Tm} (hX : glueLocT S A Tp φ f k' σ X X)
    (h : glueLocE S A Tp φ f k' σ X g u) (hg : TmNear g g') (hg' : HasTy S k' .one [] g' X) (hu : TmNear u u')
    (hu' : HasTy S k' .one [] u' X) : glueLocE S A Tp φ f k' σ X g' u' := by
  have h1 := glueLocE_near hW hN perA krA niA perT krT niT f σ hX h hu hu'
  have h2 := glueLocE_symm hW perA krA perT krT f σ hX h1
  exact glueLocE_symm hW perA krA perT krT f σ hX (glueLocE_near hW hN perA krA niA perT krT niT f σ hX h2 hg hg')

variable (hA : IsKV m A) (hφ : φ.IsCof)
  (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
  (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
include hA hφ hTp hTkv

theorem niTy_glueC {ep : V} {T T' T'' : Tm} (h : (Comp2 S (glueC m A φ Tp ep) m k f).ty T T') (hn : TmNear T' T'')
    (hT'' : IsTyK S k T'') : (Comp2 S (glueC m A φ Tp ep) m k f).ty T T'' := by
  by_cases hf : (φ.restr f).holds
  · rw [Comp2_glueC_at hφ hTp hTkv f, if_pos hf] at h ⊢
    exact NI2.tyR (niT k f hf) h hn hT''
  rw [Comp2_glueC_f hA hφ hTp hTkv f hf] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  have hT' := hb.2.1
  have hall'' : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T''.isub σ) := fun k' σ =>
    glueLocT_near hW hN perA krA niA perT krT niT f σ (hb.1.isub hW σ) (hT'.isub hW σ) (hT''.isub hW σ) (hall k' σ)
      (hn.isub σ)
  refine ⟨base_near hW hN hb hn hT'', hall'', hc, fun k' σ hnot W hWr k'' ρ => ?_⟩
  obtain ⟨W', hW', w⟩ := redW_near hWr (hn.symm.isub σ)
  have tW := glueLocT_whnfR hW hN perA krA perT krT f σ hnot (hall'' k' σ) (hT''.isub hW σ) hWr
  have tW' := glueLocT_whnfR hW hN perA krA perT krT f σ hnot (hall k' σ) (hT'.isub hW σ) hW'
  have x := hc' k' σ hnot W' hW' k'' ρ
  rw [← Tm.isub_isub] at x ⊢
  exact glueLocT_near2 hW hN perA krA niA perT krT niT f (σ.comp ρ) (tW'.isub hW ρ) (tW.isub hW ρ)
    ((hT'.isub hW σ).isub hW ρ) ((hT''.isub hW σ).isub hW ρ) x (w.symm.isub ρ) ((hn.isub σ).isub ρ)

theorem niEl_glueC {ep : V} {T g g' g'' : Tm} (hTT : (Comp2 S (glueC m A φ Tp ep) m k f).ty T T)
    (h : (Comp2 S (glueC m A φ Tp ep) m k f).el T g g') (hn : TmNear g' g'') (hu : HasTy S k .one [] g'' T) :
    (Comp2 S (glueC m A φ Tp ep) m k f).el T g g'' := by
  by_cases hf : (φ.restr f).holds
  · rw [Comp2_glueC_at hφ hTp hTkv f, if_pos hf] at h hTT ⊢
    exact (niT k f hf k (Hom.id k) T T T g g' g'').2 hTT h hn hu
  rw [Comp2_glueC_f hA hφ hTp hTkv f hf] at h hTT ⊢
  obtain ⟨hE, hmem, -, hall, hc, hc'⟩ := h
  have hE' : EB S k T g g'' := ⟨hE.1, hu, hE.2.2.trans (eq_near hW hN hE.2.1 hn (good_of_ty hW hu))⟩
  have hall'' : ∀ k' (σ : ISub k' k), glueLocE S A Tp φ f k' σ (T.isub σ) (g.isub σ) (g''.isub σ) := fun k' σ =>
    glueLocE_near hW hN perA krA niA perT krT niT f σ (hTT.2.1 k' σ) (hall k' σ) (hn.isub σ) (HasTy.isubS hW hu σ)
  refine ⟨hE', hmem, hE', hall'', hc, fun k' σ hnot w hw k'' ρ => ?_⟩
  obtain ⟨w', hw', nw⟩ := redW_near hw (hn.symm.isub σ)
  have x := hc' k' σ hnot w' hw' k'' ρ
  have tw := glueLocE_whnfR hW hN perA krA perT krT f σ hnot (hall'' k' σ) hw
  have gw := red_good hW hw.1 (good_isub (good_of_ty hW hu) σ)
  have hu2 := HasTy.isubS hW hu (σ.comp ρ)
  refine ⟨fun hh ψ e0 t0 a0 hwe => ?_, fun hh => ?_⟩
  · subst hwe
    cases nw with | glueEl nψ ne0 nt0 na0 =>
    have y := x.1 hh _ _ _ _ rfl
    have hTr := hTT.2.1 k'' (σ.comp ρ)
    unfold glueLocT at hTr; rw [if_pos hh] at hTr
    have hy := (Comp2_el y).1
    simp only [goodB, Bool.and_eq_true] at gw
    exact NI2.el2 (perT k'' _ hh) (niT k'' _ hh) hTr y (nt0.isub ρ).symm
      (HasTy.near' hW hN hy.1 (nt0.isub ρ).symm (good_isub gw.1.2 ρ)) (hn.isub (σ.comp ρ)) hu2
  · have tw2 := HasTy.isubS hW tw ρ
    rw [Tm.isub_isub] at tw2
    exact glueLocE_near2 hW hN perA krA niA perT krT niT f (σ.comp ρ) (hTT.2.1 k'' (σ.comp ρ)) (x.2 hh)
      (nw.symm.isub ρ) tw2 (hn.isub (σ.comp ρ)) hu2

end glue

end

end Model.Whnf
