import Model.Univ

/-!
# Semantic judgments

The interpretation `⟦t⟧_S` of a raw term in a signature `S` (constants are interpreted by their
bodies, `cstFn`), and the semantic counterparts of the spec's judgments:

* a *point* of a context `Ψ; Φ; Γ` at stage `m` is an interval environment `ρ` in which `Φ` holds
  and a term environment `γ` whose entries have the types of `Γ`;
* `SemTy S Ψ Φ Γ t A`: at every point, `⟦t⟧` is an element of the code `⟦A⟧`, `⟦A⟧` is a
  well-formed code of some level `≤ maxLevel`, and both are natural (commute with restriction);
* `SemEq`: both sides are `SemTy` and denote the same value at every point.

Constants: the syntactic side condition `ConstsLt` (all constants of a term are in the
signature) makes interpretations stable under extending the signature.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Good codes: well-formed codes of some level `≤ maxLevel`, and universes. -/
def TyCode (m : ℕ) (c : V) : Prop := ∃ l ≤ maxLevel, (WF l m c ∧ c ∈ Vt l) ∨ c = univC m l

/-! ### The signature -/

/-! ### Inductive types -/

/-- The first `np` components of a list value (nested pairs). -/
def plist (v : V) (np : ℕ) : List V := (List.range np).map (vnth v)

/-- The term environment of the context of a constructor argument: the earlier arguments and the
parameters, most recent first. -/
def argEnv (ps pre : List V) : ℕ → V := fun x => (pre.reverse ++ ps.reverse).getD x ∅

/-- The type of argument `j` of constructor `c`, at the parameters `psv` (a list value) and the
earlier arguments `pre`, at stage `n`, as interpreted in `σ`. -/
def argTyRaw (σ : SigV) (D : DataDecl) (d c j n : ℕ) (psv : V) (pre : List V) : V :=
  interp σ univC TyCode ((D.ctors.getD c default).argTy d D.params.length j) n (fun _ => DM.zero n)
    (argEnv (plist psv D.params.length) (pre.take j))

/-- The earlier point arguments in `pre` (before `j`) have their types. -/
def argPreValid (σ : SigV) (D : DataDecl) (d c j n : ℕ) (psv : V) (pre : List V) : Prop :=
  j ≤ pre.length ∧ ∀ i (hi : i < j) (hip : i < pre.length), (D.ctors.getD c default).isRec i = false →
    pre[i] ∈ El (argTyRaw σ D d c i n psv pre) (Hom.id n)

/-- The argument types of the semantic inductive type: junk (empty) unless at a point argument
with valid earlier arguments. -/
def argTySem (σ : SigV) (D : DataDecl) (d c j n : ℕ) (psv : V) (pre : List V) : V :=
  if j < (D.ctors.getD c default).args.length ∧ (D.ctors.getD c default).isRec j = false ∧
      argPreValid σ D d c j n psv pre
  then argTyRaw σ D d c j n psv pre else emptyC n

/-- `v` is a list value (nested pairs) of length `n`. -/
def ListLen : V → ℕ → Prop
  | v, 0 => v = ∅
  | v, n + 1 => (∃ a b, v = ZFSet.pair a b) ∧ ListLen (π2 v) n

/-- Parameter values (given at all restrictions, as list values) of the declaration `D`: lists of
the right length whose components have their types (at the earlier parameters, interpreted in
`σ`) and are natural. -/
def ParamsOK (σ : SigV) (D : DataDecl) (m : ℕ) (ps : RV m) : Prop :=
  ∀ n (g : Hom n m), ListLen (ps n g) D.params.length ∧
    (∀ i (hi : i < D.params.length), IsKV n (vnth (ps n g) i) ∧
      vnth (ps n g) i ∈ El (interp σ univC TyCode (D.params[i]) n (fun _ => DM.zero n)
        (argEnv [] (plist (ps n g) i))) (Hom.id n)) ∧
    ∀ n' (h : Hom n' n), ∀ i < D.params.length, vnth (ps n' (g.comp h)) i = res h (vnth (ps n g) i)

/-- The semantic inductive type at the parameters `ps` (given at all restrictions). -/
def dataSD (σ : SigV) (D : DataDecl) (d m : ℕ) (ps : RV m) : SData m where
  ctors := D.ctors
  params := !D.params.isEmpty
  ty c j n g pre := argTySem σ D d c j n (ps n g) pre

/-- A constructor term denotes a constructor value only at valid parameters and typed arguments
of the right number. -/
def ConGuard (σ : SigV) (D : DataDecl) (d m : ℕ) (ps : RV m) (c : ℕ) (args : RV m) (rs : List (DM m)) : Prop :=
  ∃ C, D.ctors[c]? = some C ∧ rs.length = C.dims ∧ ListLen (args m (Hom.id m)) C.args.length ∧
    ParamsOK σ D m ps ∧ (dataSD σ D d m ps).ArgsTyped c C m (Hom.id m) (plist (args m (Hom.id m)) C.args.length)

/-- The eliminator applies only at valid parameters, to an element, with branches satisfying the
boundary conditions, and where it is typed and natural on all elements. -/
def ElimGuard (σ : SigV) (D : DataDecl) (d m : ℕ) (ps : RV m) (P : (n : ℕ) → Hom n m → V → V) (bs t : RV m) : Prop :=
  ParamsOK σ D m ps ∧ DElem (dataSD σ D d m ps) m (Hom.id m) (t m (Hom.id m)) ∧ BranchesOK (dataSD σ D d m ps) P bs ∧
    ∀ n (g : Hom n m) v, DElem (dataSD σ D d m ps) n g v →
      elimD (dataSD σ D d m ps) P bs n g v ∈ El (P n g v) (Hom.id n) ∧
      ∀ n' (h : Hom n' n), res h (elimD (dataSD σ D d m ps) P bs n g v) = elimD (dataSD σ D d m ps) P bs n' (g.comp h) (res h v)

/-- The semantics of the inductive type `d` with declaration `D`, given the semantics `σ` of the
entries before it: the type former (the data code at valid parameters, junk otherwise, so that
a well-typed type former has valid parameters), the constructors (values of the arguments at
the stage itself; parameters are not recorded) and the eliminator. -/
def dataSem (σ : SigV) (D : DataDecl) (d : ℕ) : SigV where
  cst _ _ := ∅
  dat m _ ps := if ParamsOK σ D m ps then dataC (dataSD σ D d m ps) else ∅
  con m _ c ps args rs := if ConGuard σ D d m ps c args rs then
    conV D.ctors m c (plist (args m (Hom.id m)) (D.ctors.getD c default).args.length) rs else ∅
  elim m _ ps P bs t := if ElimGuard σ D d m ps P bs t then
    elimD (dataSD σ D d m ps) P bs m (Hom.id m) (t m (Hom.id m)) else ∅

/-- `σ` with the entry `k` taken from `τ`. -/
def SigV.set (σ τ : SigV) (k : ℕ) : SigV where
  cst m j := if j = k then τ.cst m j else σ.cst m j
  dat m j ps := if j = k then τ.dat m j ps else σ.dat m j ps
  con m j c ps args rs := if j = k then τ.con m j c ps args rs else σ.con m j c ps args rs
  elim m j ps P bs t := if j = k then τ.elim m j ps P bs t else σ.elim m j ps P bs t

/-- The semantics of entry `k`, given the semantics of the entries before it. -/
def entrySem (σ : SigV) (k : ℕ) : Option Entry → SigV
  | some (.defn t _) =>
    { SigV.empty with cst := fun m _ => interp σ univC TyCode t m (fun _ => DM.zero m) (fun _ => emptyC m) }
  | some (.data D) => dataSem σ D k
  | none => SigV.empty

/-- The semantics of the entries before `k`. -/
def sigUpTo (S : Sig) : ℕ → SigV
  | 0 => SigV.empty
  | k + 1 => (sigUpTo S k).set (entrySem (sigUpTo S k) k S[k]?) k

/-- The semantics of the signature. -/
def sigV (S : Sig) : SigV := sigUpTo S S.length

/-- The value of constant `k` at stage `m`. -/
abbrev cstFn (S : Sig) (m : ℕ) (k : ℕ) : V := (sigV S).cst m k

/-- The interpretation of raw terms in the signature `S`. -/
abbrev sem (S : Sig) (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : V := interp (sigV S) univC TyCode t m ρ γ

/-- All constants of a term are below `n`. -/
def _root_.KubusCore.Tm.ConstsLt (n : ℕ) : Tm → Prop
  | .var _ | .univ _ | .abort => True
  | .const k => k < n
  | .pi A B | .sigma A B | .lam A B | .app A B | .pair A B => A.ConstsLt n ∧ B.ConstsLt n
  | .fst p | .snd p | .plam p | .ipi p | .papp p _ => p.ConstsLt n
  | .unglue _ e g => e.ConstsLt n ∧ g.ConstsLt n
  | .path A a b => A.ConstsLt n ∧ a.ConstsLt n ∧ b.ConstsLt n
  | .split _ t _ u => t.ConstsLt n ∧ u.ConstsLt n
  | .transp A _ a => A.ConstsLt n ∧ a.ConstsLt n
  | .hcomp A _ u a => A.ConstsLt n ∧ u.ConstsLt n ∧ a.ConstsLt n
  | .glue A _ T e => A.ConstsLt n ∧ T.ConstsLt n ∧ e.ConstsLt n
  | .glueEl _ e t a => e.ConstsLt n ∧ t.ConstsLt n ∧ a.ConstsLt n
  | .tnil => True
  | .tcons t ts => t.ConstsLt n ∧ ts.ConstsLt n
  | .data d ps => d < n ∧ ps.ConstsLt n
  | .con d _ ps args _ => d < n ∧ ps.ConstsLt n ∧ args.ConstsLt n
  | .elim d ps P bs t => d < n ∧ ps.ConstsLt n ∧ P.ConstsLt n ∧ bs.ConstsLt n ∧ t.ConstsLt n

/-! ### Points, naturality, well-formed types -/

variable {S : Sig} {k m n : ℕ}

/-- A point of the context `Ψ; Φ; Γ` at stage `m`. -/
structure IsPoint (S : Sig) (Φ : I) (Γ : Ctx) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop where
  cof : (ival ρ Φ).holds
  typ : ∀ x A, Γ.lookup x = some A → γ x ∈ El (sem S A m ρ γ) (Hom.id m)
  kv : ∀ x, IsKV m (γ x)

/-- `t` commutes with restriction at the point `(ρ, γ)`. -/
def Natural (S : Sig) (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop :=
  ∀ k (f : Hom k m), sem S t k (ρ.restr f) (TEnv.restr γ f) = res f (sem S t m ρ γ)

/-- `A` denotes a well-formed code of some level `≤ maxLevel`, or a universe, at the point
`(ρ, γ)`. (The top universe `U_maxLevel` is a type but not an element of a universe.) -/
def TyOK (S : Sig) (A : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop := TyCode m (sem S A m ρ γ)

/-- Semantic well-formedness of a context. (Scoping of the face is not needed semantically; the
first component is a placeholder.) -/
def SemWf (S : Sig) (_Ψ : ℕ) (Φ : I) (Γ : Ctx) : Prop :=
  True ∧ (∀ x A, Γ.lookup x = some A → A.ConstsLt S.length) ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → ∀ x A, Γ.lookup x = some A →
    TyOK S A m ρ γ ∧ Natural S A m ρ γ

/-- Semantic typing. -/
def SemTy (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t A : Tm) : Prop :=
  SemWf S Ψ Φ Γ ∧ t.ConstsLt S.length ∧ A.ConstsLt S.length ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
    sem S t m ρ γ ∈ El (sem S A m ρ γ) (Hom.id m) ∧ Natural S t m ρ γ ∧
      TyOK S A m ρ γ ∧ Natural S A m ρ γ

/-- Semantic equality. -/
def SemEq (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t u A : Tm) : Prop :=
  SemTy S Ψ Φ Γ t A ∧ SemTy S Ψ Φ Γ u A ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S t m ρ γ = sem S u m ρ γ

/-- Semantic telescope typing: `as : Δ`, the telescope's types instantiated by `prev`. -/
def SemTele (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) : Tm → List Tm → List Tm → Prop
  | .tnil, [], _ => SemWf S Ψ Φ Γ
  | .tcons a as, A :: Δ, prev => SemTy S Ψ Φ Γ a (A.substList prev) ∧ SemTele S Ψ Φ Γ as Δ (a :: prev)
  | _, _, _ => False

/-- Semantic equality of telescopes. -/
def SemEqTele (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) : Tm → Tm → List Tm → List Tm → Prop
  | .tnil, .tnil, [], _ => SemWf S Ψ Φ Γ
  | .tcons a as, .tcons a' as', A :: Δ, prev =>
    SemEq S Ψ Φ Γ a a' (A.substList prev) ∧ SemEqTele S Ψ Φ Γ as as' Δ (a :: prev)
  | _, _, _, _ => False

/-- The syntactic facts about a declaration used by the model (from `DataDecl.Wf`). -/
def DataSyn (d : ℕ) (D : DataDecl) : Prop :=
  D.level + 1 ≤ maxLevel ∧
  (∀ (j : ℕ) (A : Tm), D.params[j]? = some A → A.closedB j 0 = true ∧ A.ConstsLt d) ∧
  (∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ (k : ℕ) (A : Tm), C.args[k]? = some (.point A) →
    A.closedB (D.params.length + k) 0 = true ∧ A.ConstsLt (d + 1) ∧ A.mentionsData d = false ∧
      C.noRecDeps k A = true) ∧
  (∀ (c : ℕ) (C : Ctor), D.ctors[c]? = some C → ∀ (ψ : I) (b : Tm), (ψ, b) ∈ C.bnd →
    ψ.Scoped C.dims ∧ b.closedB (D.params.length + C.args.length) C.dims = true ∧
      Ctor.simpleB D.ctors d D.params.length c C.args.length C b = true)

/-- The inductive type `d` with declaration `D` is semantically valid: at valid parameters, its
semantic data is well-formed and its argument types are well-formed codes of the declared level. -/
def DataOK (S : Sig) (d : ℕ) (D : DataDecl) : Prop :=
  DataSyn d D ∧ ∀ m (ps : RV m), ParamsOK (sigUpTo S d) D m ps →
    (dataSD (sigUpTo S d) D d m ps).Good ∧
    ∀ c j n (g : Hom n m) pre, (dataSD (sigUpTo S d) D d m ps).ty c j n g pre ∈ Vt D.level ∧
      ((dataSD (sigUpTo S d) D d m ps).PtValid c n g pre → WF D.level n ((dataSD (sigUpTo S d) D d m ps).ty c j n g pre))

/-- The signature is semantically valid: every definition is well-typed in the model, and every
inductive type is valid. -/
def SigOK (S : Sig) : Prop :=
  (∀ k t A, S[k]? = some (.defn t A) → t.closedB 0 0 ∧ A.closedB 0 0 ∧ SemTy (S.take k) 0 .one [] t A) ∧
  ∀ k D, S[k]? = some (.data D) → DataOK S k D

end

end Model
