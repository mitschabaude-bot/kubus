import Model.Whnf.Valid2Kan
import Model.Whnf.Valid2GlueEta

/-!
# The hypotheses of the binary fundamental lemma

`Fund2` (`Fund2.lean`) proves every derivation of the minimal judgments valid (`Valid2`), for
derivations in a prefix `S'` of the signature `S`. It is parametrized by:

- `DefHyp2 S S'`: the definitions of `S'` are related to themselves (outer induction on the
  signature);
- `KanOracle2 S`: the Kan property of related types (`KanH2`, `KanT2`) and the closed instances of the
  computation rules of `transp`/`hcomp` per type former (`RedexOK`), to be discharged by the Kan lemma
  by induction on codes;
- `DataHyp2 S S'`: the validity of the rules of the inductive types of `S'`;
- `GlueBetaHyp2 S`: the validity of `glueBeta`, from the data that inverting the typing of its redex
  gives (see the remark at `GlueBetaHyp2`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Related telescopes: the elements are valid at the telescope's types, instantiated by the earlier
elements of the left list. -/
def VTele2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) : Tm → Tm → List Tm → List Tm → Prop
  | .tnil, .tnil, [], _ => True
  | .tcons a as, .tcons a' as', A :: Δ, prev => Valid2 S Ψ Φ Γ a a' (A.substList prev) ∧ VTele2 S Ψ Φ Γ as as' Δ (a :: prev)
  | _, _, _, _ => False

/-- Transfer of related elements from the instances of `X` to those of `Y`. -/
def ElTr2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (X Y : Tm) : Prop :=
  ∀ k (c : CSub2 S Ψ Φ Γ k) (x y : Tm), RE2 S k (c.L X) x y → RE2 S k (c.L Y) x y

/-- The definitions of `S'` are related to themselves (in `S`). -/
def DefHyp2 (S S' : Sig) : Prop :=
  ∀ (i : ℕ) (t A : Tm), S'[i]? = some (.defn t A) → ∀ k, RT2 S k A A ∧ RE2 S k A t t

/-- The Kan oracle: composition and transport in related types, and the closed instances of the
computation rules of the Kan operations. -/
structure KanOracle2 (S : Sig) : Prop where
  hcomp : ∀ k (A A' : Tm), RT2 S k A A' → KanH2 S k A A'
  transp : ∀ k (A A' : Tm), RT2 S (k + 1) A A' → KanT2 S k A A'
  transpPath : ∀ k (X A a b : Tm) (φ : I) (p0 : Tm),
    RedexOK S k X (.transp (.path A a b) φ p0) (Tm.transpPath A a b φ p0)
  transpGlue : ∀ k (X A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I), δ.Scoped k →
    I.Entails δ φ.forall0 → I.Entails φ.forall0 δ →
    RedexOK S k X (.transp (.glue A φ T e) ψ u0) (Tm.transpGlueWith δ A φ T e ψ u0)
  hcompGlue : ∀ k (X A : Tm) (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm),
    RedexOK S k X (.hcomp (.glue A φ T e) ψ u u0) (Tm.hcompGlue A φ T e ψ u u0)
  hcompU : ∀ k (X : Tm) (l : ℕ) (φ : I) (u u0 : Tm), RedexOK S k X (.hcomp (.univ l) φ u u0) (Tm.hcompU φ u u0)

/-- `glueBeta`. Inverting the typing of the redex `unglue φ e (glueEl φ e t a) : G` gives the
annotations `A`, `T` of the `unglue` and `A2`, `T2` of the `glueEl`, whose Glue types are related
(`ElTr2`). Where the face does not hold, this relates `A2` to `A`; where it holds, nothing relates
them, but the right-hand side needs the coherence `app (fst e) t ≡ a`, known at `A2`, at `A`. -/
def GlueBetaHyp2 (S : Sig) : Prop :=
  ∀ {Ψ : ℕ} {Φ : I} {Γ : Ctx} {φ : I} {e t a G A T A2 T2 : Tm} {l l2 : ℕ},
    HasTy0 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) G → HasTy0 S Ψ Φ Γ a G →
    Valid2 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) (.unglue φ e (.glueEl φ e t a)) G →
    Valid2 S Ψ Φ Γ a a G →
    -- the `unglue`
    HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l) → HasTy0 S Ψ Φ Γ A (.univ l) →
    HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A) → Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A) →
    Valid2 S Ψ Φ Γ A A (.univ l) → ElTr2 S Ψ Φ Γ A G →
    -- the `glueEl`
    HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A2 φ T2 e) → HasTy0 S Ψ Φ Γ (.glue A2 φ T2 e) (.univ l2) →
    HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T2 A2) → Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T2 A2) →
    Valid2 S Ψ (cof Φ φ) Γ t t T2 → Valid2 S Ψ Φ Γ a a A2 → Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A2 →
    ElTr2 S Ψ Φ Γ (.glue A2 φ T2 e) (.glue A φ T e) →
    Valid2 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) a G

/-- The validity of the rules of the inductive types of `S'` (judgments in `S`), given the validity of
their premises. -/
structure DataHyp2 (S S' : Sig) : Prop where
  data : ∀ {Ψ Φ Γ d D ps}, S'[d]? = some (.data D) → D.level + 1 ≤ maxLevel →
    HasTele0 S Ψ Φ Γ ps D.params [] → VTele2 S Ψ Φ Γ ps ps D.params [] →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level)
  con : ∀ {Ψ Φ Γ d D c C ps args rs}, S'[d]? = some (.data D) → D.ctors[c]? = some C →
    ps = Tm.ofList ps.toList → HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level) →
    HasTele0 S Ψ Φ Γ ps D.params [] →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
    rs.length = C.dims → (∀ r ∈ rs, r.Scoped Ψ) →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) → VTele2 S Ψ Φ Γ ps ps D.params [] →
    VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse →
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps args rs) (.data d ps)
  elim : ∀ {Ψ Φ Γ d D ps P bs t m}, S'[d]? = some (.data D) →
    ps = Tm.ofList ps.toList →
    HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level) → HasTele0 S Ψ Φ Γ ps D.params [] →
    HasTy0 S Ψ Φ (.data d ps :: Γ) P (.univ m) →
    bs = Tm.ofList bs.toList → bs.toList.length = D.ctors.length →
    (∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      HasTy0 S Ψ Φ Γ b (D.branchTy d c C ps P)) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm) (k : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      C.bnd[k]? = some (ψ, e) →
      EqTm0 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) →
    HasTy0 S Ψ Φ Γ t (.data d ps) →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) → VTele2 S Ψ Φ Γ ps ps D.params [] →
    Valid2 S Ψ Φ (.data d ps :: Γ) P P (.univ m) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps P)) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm) (k : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      C.bnd[k]? = some (ψ, e) →
      Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) →
    Valid2 S Ψ Φ Γ t t (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps P bs t) (P.inst t)
  dataEq : ∀ {Ψ Φ Γ d D ps ps'}, S'[d]? = some (.data D) →
    HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level) → HasTy0 S Ψ Φ Γ (.data d ps') (.univ D.level) →
    EqTele0 S Ψ Φ Γ ps ps' D.params [] →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) →
    Valid2 S Ψ Φ Γ (.data d ps') (.data d ps') (.univ D.level) → VTele2 S Ψ Φ Γ ps ps' D.params [] →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level)
  conEq : ∀ {Ψ Φ Γ d D c C ps ps' args args' rs rs'}, S'[d]? = some (.data D) → D.ctors[c]? = some C →
    HasTy0 S Ψ Φ Γ (.con d c ps args rs) (.data d ps) →
    HasTy0 S Ψ Φ Γ (.con d c ps' args' rs') (.data d ps) →
    EqTele0 S Ψ Φ Γ ps ps' D.params [] →
    EqTele0 S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse →
    rs.length = rs'.length → (∀ (k : ℕ) (r r' : I), rs[k]? = some r → rs'[k]? = some r' → I.Eq r r') →
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps args rs) (.data d ps) →
    Valid2 S Ψ Φ Γ (.con d c ps' args' rs') (.con d c ps' args' rs') (.data d ps) →
    VTele2 S Ψ Φ Γ ps ps' D.params [] →
    VTele2 S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse →
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps' args' rs') (.data d ps)
  elimEq : ∀ {Ψ Φ Γ d D ps ps' P P' bs bs' t t' m}, S'[d]? = some (.data D) →
    HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t) → HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') (P.inst t) →
    EqTele0 S Ψ Φ Γ ps ps' D.params [] → EqTm0 S Ψ Φ (.data d ps :: Γ) P P' (.univ m) →
    bs = Tm.ofList bs.toList → bs' = Tm.ofList bs'.toList →
    bs.toList.length = bs'.toList.length →
    (∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' →
      EqTm0 S Ψ Φ Γ b b' (D.branchTy d c C ps P)) →
    EqTm0 S Ψ Φ Γ t t' (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps P bs t) (P.inst t) →
    Valid2 S Ψ Φ Γ (.elim d ps' P' bs' t') (.elim d ps' P' bs' t') (P.inst t) →
    VTele2 S Ψ Φ Γ ps ps' D.params [] → Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m) →
    (∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' →
      Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P)) →
    Valid2 S Ψ Φ Γ t t' (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') (P.inst t)
  dataInj : ∀ {Ψ Φ Γ d D ps ps' l}, S'[d]? = some (.data D) →
    HasTele0 S Ψ Φ Γ ps D.params [] → HasTele0 S Ψ Φ Γ ps' D.params [] →
    EqTm0 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l) →
    VTele2 S Ψ Φ Γ ps ps D.params [] → VTele2 S Ψ Φ Γ ps' ps' D.params [] →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l) →
    VTele2 S Ψ Φ Γ ps ps' D.params []
  dataInjAt : ∀ {Ψ Φ Γ d} {D : DataDecl} {ps ps' : Tm} {l k : ℕ} {p p' A : Tm}, S'[d]? = some (.data D) →
    ps = Tm.ofList ps.toList → ps' = Tm.ofList ps'.toList →
    EqTm0 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l) →
    ps.toList[k]? = some p → ps'.toList[k]? = some p' → D.params[k]? = some A →
    HasTy0 S Ψ Φ Γ p (A.substList (ps.toList.take k).reverse) →
    HasTy0 S Ψ Φ Γ p' (A.substList (ps.toList.take k).reverse) →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l) →
    Valid2 S Ψ Φ Γ p p (A.substList (ps.toList.take k).reverse) →
    Valid2 S Ψ Φ Γ p' p' (A.substList (ps.toList.take k).reverse) →
    Valid2 S Ψ Φ Γ p p' (A.substList (ps.toList.take k).reverse)
  conBnd : ∀ {Ψ Φ Γ d D c C ps args rs} {k : ℕ} {ψ b T}, S'[d]? = some (.data D) → D.ctors[c]? = some C →
    C.bnd[k]? = some (ψ, b) → I.Entails Φ (Ctor.cofAt ψ rs) →
    ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTy0 S Ψ Φ Γ (.con d c ps args rs) T → HasTy0 S Ψ Φ Γ (Ctor.bndAt b ps.toList args.toList rs) T →
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (.con d c ps args rs) T →
    Valid2 S Ψ Φ Γ (.con d c ps args rs) (Ctor.bndAt b ps.toList args.toList rs) T
  elimCon : ∀ {Ψ Φ Γ d D c C ps P bs b qs args rs T}, S'[d]? = some (.data D) →
    D.ctors[c]? = some C → bs.toList[c]? = some b →
    ps = Tm.ofList ps.toList → args = Tm.ofList args.toList → bs = Tm.ofList bs.toList →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
    HasTy0 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) T →
    HasTy0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs) T →
    VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse →
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) (.elim d ps P bs (.con d c qs args rs)) T →
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs))
      (Tm.papps (Tm.apps b (args.toList ++
        C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs) T
  elimHcomp : ∀ {Ψ Φ Γ d D ps P bs qs φ u a T}, S'[d]? = some (.data D) → D.isHIT = true →
    HasTy0 S Ψ Φ Γ (.hcomp (.data d ps) φ u a) (.data d ps) →
    HasTy0 S Ψ Φ Γ (.elim d ps P bs (.hcomp (.data d qs) φ u a)) T →
    HasTy0 S Ψ Φ Γ (Tm.comp (P.subst (consSub (Tm.hfill (.data d ps) φ u a)) (fun i => .var (i + 1))) φ
      (.elim d ps.dshift P.dshift bs.dshift u) (.elim d ps P bs a)) T →
    Valid2 S Ψ Φ Γ (.hcomp (.data d ps) φ u a) (.hcomp (.data d ps) φ u a) (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.hcomp (.data d qs) φ u a)) (.elim d ps P bs (.hcomp (.data d qs) φ u a)) T →
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.hcomp (.data d qs) φ u a))
      (Tm.comp (P.subst (consSub (Tm.hfill (.data d ps) φ u a)) (fun i => .var (i + 1))) φ
        (.elim d ps.dshift P.dshift bs.dshift u) (.elim d ps P bs a)) T
  hcompCon : ∀ {Ψ Φ Γ d D c C ps φ u qs uargs args T}, S'[d]? = some (.data D) → D.isHIT = false →
    D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    uargs = Tm.ofList uargs.toList →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
    HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse →
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (.con d c ps.dshift uargs []) (.data d ps.dshift) →
    EqTele0 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse →
    HasTy0 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args [])) T →
    HasTy0 S Ψ Φ Γ (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps)
        ps.dshift.toList φ 0 [] uargs.toList args.toList)) []) T →
    VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) ps.toList.reverse →
    VTele2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs uargs (C.argTys d D.params.length) ps.dshift.toList.reverse →
    Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (.con d c ps.dshift uargs []) (.data d ps.dshift) →
    VTele2 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse →
    Valid2 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args [])) (.hcomp (.data d ps) φ u (.con d c qs args [])) T →
    Valid2 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args []))
      (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps) ps.dshift.toList φ 0 []
        uargs.toList args.toList)) []) T
  transpData0 : ∀ {Ψ Φ Γ d D ps φ a T}, S'[d]? = some (.data D) → D.params = [] →
    HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ a) T → HasTy0 S Ψ Φ Γ a T →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ a) (.transp (.data d ps) φ a) T →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ a) a T
  transpCon : ∀ {Ψ Φ Γ d D c C ps φ qs args rs T}, S'[d]? = some (.data D) → D.params ≠ [] →
    D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse →
    HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.con d c qs args rs)) T →
    HasTy0 S Ψ Φ Γ (.con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T →
    VTele2 S Ψ Φ Γ args args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d c qs args rs)) (.transp (.data d ps) φ (.con d c qs args rs)) T →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.con d c qs args rs))
      (.con d c (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T
  transpHcomp : ∀ {Ψ Φ Γ d D ps φ qs ψ u a T}, S'[d]? = some (.data D) → D.params ≠ [] → D.isHIT = true →
    HasTy0 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .zero)) ψ u a) (.data d (ps.dinst .zero)) →
    HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) T →
    HasTy0 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .one)) ψ
        (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a)) T →
    Valid2 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .zero)) ψ u a) (.hcomp (.data d (ps.dinst .zero)) ψ u a)
      (.data d (ps.dinst .zero)) →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a))
      (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) T →
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a))
      (.hcomp (.data d (ps.dinst .one)) ψ
        (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a)) T

end

end Model.Whnf
