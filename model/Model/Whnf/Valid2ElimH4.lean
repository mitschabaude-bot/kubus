import Model.Whnf.Valid2ElimH3
import Model.Whnf.Kan2DataHITConRel

/-!
# Constructor cases of the higher inductive eliminator relation

Related constructor arguments and the induction hypotheses for recursive arguments give related
branch contracta, including the constructor's interval arguments.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Eliminations of related higher inductive elements, with computable motives. -/
def EM1H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) →
  ∀ Q M' bs', ElimRelH S d D K P M bs Q M' bs' →
    RE2 S k1 ((M.isub ρ).inst x) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x)
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x')

/-- Constructor contracta of related higher inductive elements. -/
def EMConH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) →
  ∀ Q M' bs', ElimRelH S d D K P M bs Q M' bs' →
  ∀ (c : ℕ) (C : Ctor) (qs : Tm) (X : List Tm) (rs : List I) (qs' : Tm) (X' : List Tm) (rs' : List I),
    D.ctors[c]? = some C → RedE S k1 A v (.con d c qs (Tm.ofList X) rs) →
    RedE S k1 A v' (.con d c qs' (Tm.ofList X') rs') →
    RE2 S k1 ((M.isub ρ).inst (.con d c (P.isub ρ) (Tm.ofList X) rs))
      (Tm.papps (ecTm d C c (P.isub ρ) (M.isub ρ) (bs.isub ρ) X) rs)
      (Tm.papps (ecTm d C c (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) X') rs')

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
  (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP hPP

/-- The constructor stage of elimination, including its interval arguments. -/
theorem em2_conH {k1 : ℕ} {g : Hom k1 K} {M bs A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor}
    {args args' : List Tm} {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 g A t t')
    (hC : (dataD S d).ctors[c]? = some C) (hA : RedT S k1 A (.data d ps))
    (ht : RedE S k1 A t (.con d c qs (Tm.ofList args) rs))
    (ht' : RedE S k1 A t' (.con d c qs' (Tm.ofList args') rs'))
    (hl : args.length = C.args.length) (hl' : args'.length = C.args.length)
    (ihrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      EM1H S d D K P M bs k1 g (.data d ps) args[j] args'[j]) :
    EMConH S d D K P M bs k1 g A t t' := by
  intro ρ hg hAe Q M' bs' hER c2 C2 qs2 X2 rs2 qs2' X2' rs2' hC2 hr hr'
  subst hg hAe
  have hdD := dataD_eq hW hD
  have hC' : D.ctors[c]? = some C := hdD ▸ hC
  obtain rfl : ps = P.isub ρ := redT_data_eq (Θ := ΘK S D d K P) hA
  have e1 := RedW.unique hr.1 ht.1
  have e2 := RedW.unique hr'.1 ht'.1
  simp only [Tm.con.injEq] at e1 e2
  obtain ⟨-, rfl, rfl, eX, rfl⟩ := e1
  obtain ⟨-, -, rfl, eX', rfl⟩ := e2
  have eX1 := congrArg Tm.toList eX
  have eX1' := congrArg Tm.toList eX'
  simp only [toList_ofList] at eX1 eX1'
  subst X2 X2' 
  rw [hC'] at hC2
  cases hC2
  have hZ : ∀ i (hi : i < C.args.length), RE2 S k1 ((C.argTy d D.params.length i).substList
      ((args.take i).reverse ++ (P.isub ρ).toList.reverse)) (args.getD i .abort) (args'.getD i .abort) := by
    rcases DR2At_cases hW hD hP hPP ρ hat with
      ⟨c3, C3, q3, Z, rs3, q3', Z', rs3', hC3, hZl, hZ'l, hr3, hr3', -, -, -, -, -, hZ⟩ |
      ⟨_, _, _, _, _, _, _, _, -, hr3, -⟩
    · have f1 := RedW.unique hr3.1 ht.1
      have f2 := RedW.unique hr3'.1 ht'.1
      simp only [Tm.con.injEq] at f1 f2
      obtain ⟨-, rfl, -, eZ, -⟩ := f1
      obtain ⟨-, -, -, eZ', -⟩ := f2
      have eZ1 := congrArg Tm.toList eZ
      have eZ1' := congrArg Tm.toList eZ'
      simp only [toList_ofList] at eZ1 eZ1'
      subst Z Z'
      rw [hC'] at hC3
      cases hC3
      exact hZ
    · cases RedW.unique hr3.1 ht.1
  obtain ⟨-, htele, -, hrs, hsc, -, -, -, -⟩ :=
    con_inv hW hD hC' (HasTy.eqR ht.2) (HasTy.isubS hW hP ρ)
  obtain ⟨-, -, -, hrs', hsc', -, -, -, -⟩ :=
    con_inv hW hD hC' (HasTy.eqR ht'.2) (HasTy.isubS hW hP ρ)
  have hreq : IEqL rs2 rs2' := by
    rcases DR2At_cases hW hD hP hPP ρ hat with
      ⟨_, _, _, _, _, _, _, _, -, -, -, h1, h2, hrl, hrr, he, -, -, -⟩ |
      ⟨_, _, _, _, _, _, _, _, -, h1, -⟩
    · have e1 := RedW.unique h1.1 ht.1
      have e2 := RedW.unique h2.1 ht'.1
      simp only [Tm.con.injEq] at e1 e2
      obtain ⟨-, -, -, -, rfl⟩ := e1
      obtain ⟨-, -, -, -, rfl⟩ := e2
      exact ieqL_iff.2 (forall2_ieq (hrl.trans hrr.symm) he)
    · cases RedW.unique h1.1 ht.1
  have hplen := Meta.tele_length htele
  refine elimCon_relH hW hD hC' hplen (hER.br k1 ρ _ C hC') hl hl'
    (fun i hi hi' => ?_) (fun j hj => ?_) hrs hreq hsc hsc'
  · have hh := hZ i (by omega)
    rwa [getD_eq_get' hi, getD_eq_get' hi'] at hh
  · obtain ⟨hjn, hjr⟩ := mem_recPos hj
    rw [getD_eq_get' (show j < args.length by omega), getD_eq_get' (show j < args'.length by omega)]
    exact ihrec j (by omega) (by omega) hjr ρ rfl rfl Q M' bs' hER

end lit

end

end Model.Whnf
