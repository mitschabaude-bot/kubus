import Model.Whnf.Kan2Univ
import Model.Canon.KanDataH
import Model.Canon.KanDataCon

/-!
# The binary Kan operations at inductive types: reduction and the relation at literal types

Reduction of compositions and transports at inductive types (`hcompCon`, `transpCon`, ...), and
the binary relation of elements of an inductive type `data d ps` whose parameters are a literal
list, through the derivations `DR2` at the code of the type.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-! ### Reduction -/

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hD

/-- A constructor of an inductive type without path constructors is a weak-head normal form. -/
theorem step_con_nonHIT (hH : D.isHIT = false) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    (ps args : Tm) (rs : List I) : step S (.con d c ps args rs) = none := by
  simp [step, hD, hC, (nonHIT_ctor hH hC).2, firstBnd]

/-- A composition in an inductive type without path constructors reduces its base. -/
theorem step_hcomp_base (hH : D.isHIT = false) {ps u a a' : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (ha : step S a = some a') : step S (.hcomp (.data d ps) φ u a) = some (.hcomp (.data d ps) φ u a') := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, hH, ha]

theorem red_hcomp_base (hH : D.isHIT = false) {ps u a a' : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (h : Red S a a') : Red S (.hcomp (.data d ps) φ u a) (.hcomp (.data d ps) φ u a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (step_hcomp_base hD hH hn hs) ih

/-- `hcompCon` as a step. -/
theorem step_hcompCon (hH : D.isHIT = false) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {ps u qs : Tm} {φ : I} (hn : ¬ I.Entails .one φ) (args : List Tm) :
    step S (.hcomp (.data d ps) φ u (.con d c qs (Tm.ofList args) [])) =
      some (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps)
        ps.dshift.toList φ 0 [] ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u) args)) []) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, hH, hC, toList_ofList, (nonHIT_ctor hH hC).2, firstBnd]

/-- A composition in a higher inductive type whose type is normal and whose face does not hold is
a weak-head normal form. -/
theorem step_hcomp_HIT (hH : D.isHIT = true) {ps u a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.hcomp (.data d ps) φ u a) = none := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, hH]

end red

theorem step_data (d : ℕ) (ps : Tm) : step S (.data d ps) = none := by simp [step]




/-! ### Reductions on either side of a relation at one stage -/

section dr
variable (hW : WfSig S) {k0 : ℕ} {Θ : SData m} {f : Hom k0 m} {d : ℕ} {D : DataDecl} {g : Hom k k0}
include hW

/-- A related element of an inductive type at a stage, along a reduction on the left. -/
theorem DR2At.redL {A t t' u : Tm} (h : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t') (r : Red S t u)
    (e : EqTm S k .one [] t u A) : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A u t' := by
  cases h with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    exact .con (by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]) hm' (e.symm.trans heq) hC hA hpl
      ⟨red_redW r ht.1, e.symm.trans ht.2⟩ ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt
  | hcomp hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu =>
    exact .hcomp (by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]) hm' (e.symm.trans heq) hH hA hpl
      ⟨red_redW r ht.1, e.symm.trans ht.2⟩ ht' hs hs' h12 h21 ha hu

/-- A related element of an inductive type at a stage, through a reduct on the right. -/
theorem DR2At.expandR {A t t' u' : Tm} (h : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t u')
    (r : Red S t' u') (e : EqTm S k .one [] t' u' A) : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t' := by
  cases h with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    exact .con hm (by unfold dataMem at hm' ⊢; rwa [semK_eq hW e]) (heq.trans e.symm) hC hA hpl ht
      (RedE.of_red r e ht') hrs hrs' hreq hsc hsc' hl hl' hrec hpt
  | hcomp hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu =>
    exact .hcomp hm (by unfold dataMem at hm' ⊢; rwa [semK_eq hW e]) (heq.trans e.symm) hH hA hpl ht
      (RedE.of_red r e ht') hs hs' h12 h21 ha hu

end dr

/-! ### The relation at literal inductive types -/

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- The code of a literal inductive type, at a restriction. -/
theorem semK_dataLit {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) (ρ : ISub k' K) :
    semK S k' (.data d (P.isub ρ)) = res ρ.hom (dataC (ΘK S D d K P)) := by
  rw [show Tm.data d (P.isub ρ) = (Tm.data d P).isub ρ from rfl, semK_isubTy hW ⟨l, .inl hP⟩ ρ,
    semK_dataT hW hD hP]

/-- Related elements of a restriction of a literal inductive type, through the derivations at its code. -/
theorem RE2_dataLit_iff {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) (ρ : ISub k' K)
    {x y : Tm} :
    RE2 S k' (.data d (P.isub ρ)) x y ↔ EB S k' (.data d (P.isub ρ)) x y ∧
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k' ρ.hom
        (.data d (P.isub ρ)) x y := by
  unfold RE2
  rw [semK_dataLit hW hD hP ρ, Comp2_res (show dataC (ΘK S D d K P) ≠ ∅ from mkKV_ne_empty _), Hom.comp_id,
    Comp2_dataC]
  simp only [show (ΘK S D d K P).idx = d from rfl]
  constructor
  · rintro ⟨hE, -, -, hdr⟩
    refine ⟨hE, ?_⟩
    have := DR2.unbase (Θ := ΘK S D d K P) (Hom.id K) (h := ρ.hom) (g := Hom.id k')
      (by rw [Hom.id_comp]; exact hdr)
    rwa [Hom.comp_id] at this
  · rintro ⟨hE, hdr⟩
    refine ⟨hE, ?_, hE, ?_⟩
    · have := mem_of_ty hW hE.1
      rwa [semK_dataLit hW hD hP ρ] at this
    · have := DR2.rebase (Hom.id K) hdr ρ.hom (Hom.id k') (Hom.comp_id _).symm
      rwa [Hom.id_comp] at this

/-- The argument types of a typed literal inductive type are well-formed codes. -/
theorem ΘK_ty_wf {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) :
    ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → WF D.level n ((ΘK S D d K P).ty c j n g pre) :=
  fun c j n g pre hv =>
    ((((sigOK_of_wfSig _ S rfl hW).2 d D hD).2 _ _ (paramsOK_K hW hD hP)).2.1 c j n g pre).2 hv

/-- The parameter entries of a typed literal inductive type are well-formed codes. -/
theorem ΘK_pt_wf {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) :
    ∀ n (g : Hom n K) j t X, vnth ((ΘK S D d K P).pt n g) j = ZFSet.pair t X → WF D.level n X :=
  fun n g j t X e => (((((sigOK_of_wfSig _ S rfl hW).2 d D hD).2 _ _ (paramsOK_K hW hD hP)).2.2.2 n g).2 j t X e).2

theorem level_le {K : ℕ} : D.level ≤ maxLevel := by
  have := (((sigOK_of_wfSig _ S rfl hW).2 d D hD).1).1; omega

/-- The point argument relations of a typed literal inductive type are partial equivalences. -/
theorem perP_ΘK {K : ℕ} {P : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l)) :
    ∀ {n : ℕ} (h : Hom n K) (c j : ℕ) (pre : List V),
      PERP (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr h)) c j pre) n n (Hom.id n)) :=
  fun h c j pre => perP_tyLook (fun c j n g pre hv => per2_wf hW _ (level_le hW hD (K := K)) n _
    (ΘK_ty_wf hW hD hP c j n g pre hv)) h c j pre

/-- Composition and transport at the point argument types of a literal inductive type, from those
at their codes. -/
theorem kan_tyLook {K : ℕ} {P : Tm}
    (hArgK : ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → KanP2 S n ((ΘK S D d K P).ty c j n g pre))
    {n : ℕ} (h : Hom n K) (c j : ℕ) (pre : List V) {A A' : Tm}
    (hA : (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr h)) c j pre) n n (Hom.id n)).ty A A') :
    KanH2 S n A A' ∧ ∀ {n' : ℕ} (e : n = n' + 1), KanT2 S n' A A' := by
  rcases tyLook_cases ((ΘK S D d K P).restr h) c j pre with h0 | h0
  · rw [h0, Comp2_empty] at hA; exact hA.elim
  · rw [tyLook_eq h0] at hA
    have hv := ptValid_of_validPre h0
    have K2 := hArgK c j n (h.comp (Hom.id n)) pre hv
    refine ⟨K2.1 n (Hom.id n) A A' hA, fun {n'} e => ?_⟩
    subst e
    exact K2.2 n' (Hom.id (n' + 1)) A A' hA

/-- The clauses of related literal inductive types at a restriction. -/
theorem dataLit_rel {K : ℕ} {P Q : Tm} {l : ℕ} (hP : HasTy S K .one [] (.data d P) (.univ l))
    (hPQ : RT2 S K (.data d P) (.data d Q)) (σ : ISub k' K) :
    argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (P.isub σ) (Q.isub σ) ∧
    argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (Q.isub σ) (P.isub σ) ∧
    argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (P.isub σ) (P.isub σ) ∧
    argRelH (ΘK S D d K P) (Hom.id K) S k' σ.hom (Q.isub σ) (Q.isub σ) ∧
    parRel2 S (ΘK S D d K P) (Hom.id K) k' σ (P.isub σ) (Q.isub σ) ∧
    P.isub σ = Tm.ofList (P.isub σ).toList ∧ Q.isub σ = Tm.ofList (Q.isub σ).toList := by
  have h := hPQ
  unfold RT2 at h
  rw [semK_dataT hW hD hP, Comp2_dataC] at h
  obtain ⟨ps, ps', h1, h2, hl, hl', a12, a21, a11, a22, pr⟩ := h.2.1 k' σ
  obtain rfl : ps = P.isub σ := by have := RedW.unique h1.1 (redW_self (step_data d _)); injection this
  obtain rfl : ps' = Q.isub σ := by have := RedW.unique h2.1 (redW_self (step_data d _)); injection this
  exact ⟨(argRel2_iff _ σ).1 a12, (argRel2_iff _ σ).1 a21, (argRel2_iff _ σ).1 a11, (argRel2_iff _ σ).1 a22, pr,
    hl, hl'⟩

end lit

end

end Model.Whnf
