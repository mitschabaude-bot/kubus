import Model.Whnf.Step
import Model.Canon.Comp

/-!
# The binary computability relation (a PER with judgmental equality)

Related closed types and elements at a stage, indexed by the model's code (as `Model.Canon.Comp`)
and Kripke by construction. Every relation includes the judgmental equality of the two sides. The
types of every former, and the elements of inductive types, are observed through their weak-head
normal forms (`RedW`), which are unique: this makes the relations transitive without any
injectivity of type formers or constructors. Elements of `Π`, `Σ` and path types are observed
through their eliminations. Elements of Glue types are observed through their weak-head normal
forms `glueEl ψ e t a`, whose annotations agree with those of the type's normal form (so that
`unglue` computes soundly), and their bases `a`; where the face holds, through `T`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Model.Whnf

open KubusCore ZFSet Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k k' k'' m n : ℕ}

variable (S : Sig)

/-- Related types (`ty A A'`) and related elements of a type (`el A t t'`). -/
structure Pack2 where
  ty : Tm → Tm → Prop
  el : Tm → Tm → Tm → Prop

def Pack2.bot : Pack2 := ⟨fun _ _ => False, fun _ _ _ => False⟩

/-- A binary element relation at all interval substitutions out of stage `k`. -/
abbrev ElR2 (k : ℕ) := (k' : ℕ) → ISub k' k → Tm → Tm → Tm → Prop

/-- Two elements of a closed type, judgmentally equal. -/
def EB (k : ℕ) (A t t' : Tm) : Prop :=
  HasTy S k .one [] t A ∧ HasTy S k .one [] t' A ∧ EqTm S k .one [] t t' A

/-- A type and its weak-head normal form, judgmentally equal. -/
def RedT (k : ℕ) (A W : Tm) : Prop := RedW S A W ∧ TyEq S k A W

/-- An element and its weak-head normal form, judgmentally equal at its type. -/
def RedE (k : ℕ) (A t w : Tm) : Prop := RedW S t w ∧ EqTm S k .one [] t w A

/-! ### Element relations of the type formers -/

def piE2 (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ A1 B1, RedT S k'' (A.isub σ') (.pi A1 B1) ∧
    ∀ a a', dom k'' (σ.comp σ') A1 a a' →
      cod k'' (σ.comp σ') a k'' (ISub.id k'') (B1.inst a) (.app (t.isub σ') a) (.app (t'.isub σ') a')

def sigmaE2 (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ A1 B1, RedT S k'' (A.isub σ') (.sigma A1 B1) ∧
    dom k'' (σ.comp σ') A1 (.fst (t.isub σ')) (.fst (t'.isub σ')) ∧
    cod k'' (σ.comp σ') (.fst (t.isub σ')) k'' (ISub.id k'') (B1.inst (.fst (t.isub σ')))
      (.snd (t.isub σ')) (.snd (t'.isub σ'))

def pathE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1 b0 b1, RedT S k'' (A.isub σ') (.path L1 b0 b1) ∧
    ∀ (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r)

def ipiE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1, RedT S k'' (A.isub σ') (.ipi L1) ∧
    ∀ (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r)

/-! ### Relations of families of types -/

section families
variable {k : ℕ}

/-- The element relation of a `Π` family. -/
def piEl (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (A t t' : Tm) : Prop :=
  piE2 S (fun k' σ => (D k' σ).el) (fun k' σ a k'' σ' => (C k' σ a k'' σ').el) k (ISub.id k) A t t'

/-- The type relation of a `Π` family. -/
def piT (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1', RedT S k' (A.isub σ) (.pi A1 B1) ∧ RedT S k' (A'.isub σ) (.pi A1' B1') ∧
    (D k' σ).ty A1 A1' ∧ ∀ a a', (D k' σ).el A1 a a' → (C k' σ a k' (ISub.id k')).ty (B1.inst a) (B1'.inst a')

/-- The element relation of a `Σ` family. -/
def sigEl (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (A t t' : Tm) : Prop :=
  sigmaE2 S (fun k' σ => (D k' σ).el) (fun k' σ a k'' σ' => (C k' σ a k'' σ').el) k (ISub.id k) A t t'

/-- The type relation of a `Σ` family. -/
def sigT (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1', RedT S k' (A.isub σ) (.sigma A1 B1) ∧ RedT S k' (A'.isub σ) (.sigma A1' B1') ∧
    (D k' σ).ty A1 A1' ∧ ∀ a a', (D k' σ).el A1 a a' → (C k' σ a k' (ISub.id k')).ty (B1.inst a) (B1'.inst a')

/-- The element relation of path types over a family of lines. -/
def pathEl (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) (A t t' : Tm) : Prop :=
  pathE2 S (fun k' σ => (Lp k' σ).el) k (ISub.id k) A t t'

/-- The type relation of path types over a family of lines. -/
def pathT (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
    RedT S k' (A.isub σ) (.path L1 b0 b1) ∧ RedT S k' (A'.isub σ) (.path L1' b0' b1') ∧
    (Lp (k' + 1) σ.up).ty L1 L1' ∧
    (Lp k' (ISub.cons .zero trivial σ)).el (L1.dinst .zero) b0 b0' ∧
    (Lp k' (ISub.cons .one trivial σ)).el (L1.dinst .one) b1 b1'

/-- The pack of a `Π` family. -/
def piPack (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2) :
    Pack2 := ⟨fun A A' => (IsTyK S k A ∧ IsTyK S k A' ∧ TyEq S k A A') ∧ piT S D C A A', piEl S D C⟩

/-- The pack of a `Σ` family. -/
def sigPack (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2) :
    Pack2 := ⟨fun A A' => (IsTyK S k A ∧ IsTyK S k A' ∧ TyEq S k A A') ∧ sigT S D C A A', sigEl S D C⟩

/-- The pack of path types over a family of lines. -/
def pathPack (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) : Pack2 :=
  ⟨fun A A' => (IsTyK S k A ∧ IsTyK S k A' ∧ TyEq S k A A') ∧ pathT S Lp A A', pathEl S Lp⟩

end families

section fam
variable {n : ℕ}

/-- Path types over a constant family of lines. -/
def pathF (AP : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 := fun k' σ =>
  pathPack S (k := k') (fun k3 (σ3 : ISub k3 (k' + 1)) => AP k3 (σ.comp σ3.tail))

/-- `Σ` types over families of relations (the codomain relation does not depend on the argument). -/
def sigF (D Cf : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 := fun k' σ =>
  sigPack S (k := k') (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 _ k4 σ4 => Cf k4 ((σ.comp σ3).comp σ4))

/-- `Π` types over families of relations (the codomain relation does not depend on the argument). -/
def piF (D Cf : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 := fun k' σ =>
  piPack S (k := k') (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 _ k4 σ4 => Cf k4 ((σ.comp σ3).comp σ4))

/-- `fiber f y = Σ (x : T), Path A (f x) y`. -/
def fiberF (TP AP : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 :=
  sigF S TP (pathF S AP)
/-- `isContr X = Σ (c : X), (x : X) → Path X c x`. -/
def isContrF (X : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 :=
  sigF S X (piF S X (pathF S X))
/-- `isEquiv f = (y : A) → isContr (fiber f y)`. -/
def isEquivF (TP AP : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 :=
  piF S AP (isContrF S (fiberF S TP AP))
/-- `Equiv T A = Σ (f : T → A), isEquiv f`. -/
def equivF (TP AP : (k' : ℕ) → ISub k' n → Pack2) : (k' : ℕ) → ISub k' n → Pack2 :=
  sigF S (piF S TP AP) (isEquivF S TP AP)

end fam

/-! ### Inductive types -/

mutual
/-- Related elements of an inductive type: related at every restriction (`DR2At`). -/
inductive DR2 {m : ℕ} (d : ℕ) (D : DataDecl) (Mem : (k : ℕ) → Hom k m → Tm → Prop)
    (P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Tm → Prop) :
    (k : ℕ) → Hom k m → Tm → Tm → Tm → Prop
  | intro {k : ℕ} {f : Hom k m} {A t t' : Tm} : EqTm S k .one [] t t' A →
      (∀ k' (σ : ISub k' k), DR2At d D Mem P k' (f.comp σ.hom) (A.isub σ) (t.isub σ) (t'.isub σ)) →
      DR2 d D Mem P k f A t t'

/-- Related elements of an inductive type at a stage: weak-head normal forms which are the same
constructor with related arguments (point arguments by `P`, given the values of the earlier
arguments of the left side), or, in a HIT, formal compositions with equivalent faces that do not
hold, related bases and tubes related where the face holds. -/
inductive DR2At {m : ℕ} (d : ℕ) (D : DataDecl) (Mem : (k : ℕ) → Hom k m → Tm → Prop)
    (P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Tm → Prop) :
    (k : ℕ) → Hom k m → Tm → Tm → Tm → Prop
  | con {k : ℕ} {f : Hom k m} {A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
      {rs rs' : List I} :
      Mem k f t → Mem k f t' → EqTm S k .one [] t t' A → D.ctors[c]? = some C → RedT S k A (.data d ps) → ps = Tm.ofList ps.toList →
      RedE S k A t (.con d c qs (Tm.ofList args) rs) → RedE S k A t' (.con d c qs' (Tm.ofList args') rs') →
      rs.length = C.dims → rs'.length = C.dims →
      (∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r') →
      (∀ r ∈ rs, r.Scoped k) → (∀ r ∈ rs', r.Scoped k) →
      args.length = C.args.length → args'.length = C.args.length →
      (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
        DR2 d D Mem P k f (.data d ps) args[j] args'[j]) →
      (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
        P k f c j ((args.take j).map (semK S k))
          ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) args[j] args'[j]) →
      DR2At d D Mem P k f A t t'
  | hcomp {k : ℕ} {f : Hom k m} {A t t' ps qs qs' u u' a a' : Tm} {φ φ' : I} :
      Mem k f t → Mem k f t' → EqTm S k .one [] t t' A → D.isHIT = true → RedT S k A (.data d ps) → ps = Tm.ofList ps.toList →
      RedE S k A t (.hcomp (.data d qs) φ u a) → RedE S k A t' (.hcomp (.data d qs') φ' u' a') →
      φ.Scoped k → φ'.Scoped k → I.Entails φ φ' → I.Entails φ' φ →
      DR2 d D Mem P k f (.data d ps) a a' →
      (∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
        DR2 d D Mem P k' (f.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)) →
      DR2At d D Mem P k f A t t'
end

/-! ### The relations -/

/-- One step of the definition: the relations of the type whose data at the restrictions of stage
`k` are `Dt` and which is the code `self`, given the relations `rec` of the codes of rank below
`ρ`. -/
def core2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2) : Pack2 :=
  let sh := π1 (Dt k (Hom.id k))
  have hsh : rank sh < ρ := (rank_π1_le _).trans_lt (hD k (Hom.id k))
  have h2 : rank (π2 sh) < ρ := (rank_π2_le _).trans_lt hsh
  have h12 : rank (π1 (π2 sh)) < ρ := (rank_π1_le _).trans_lt h2
  have h22 : rank (π2 (π2 sh)) < ρ := (rank_π2_le _).trans_lt h2
  have h122 : rank (π1 (π2 (π2 sh))) < ρ := (rank_π1_le _).trans_lt h22
  have h222 : rank (π2 (π2 (π2 sh))) < ρ := (rank_π2_le _).trans_lt h22
  have h1222 : rank (π1 (π2 (π2 (π2 sh)))) < ρ := (rank_π1_le _).trans_lt h222
  if π1 sh = natZ tPi ∨ π1 sh = natZ tSigma then
    let Y := π1 (π2 sh)
    let B := π2 (π2 sh)
    let RY : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => rec Y h12 k k' σ.hom
    let RB : (k' : ℕ) → ISub k' k → Tm → Pack2 := fun k' σ a =>
      rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k' (Hom.id k')
    let cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k' := fun k' σ a k'' σ' =>
      (rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k'' σ'.hom).el
    let isPi := π1 sh = natZ tPi
    -- the normal forms at a restriction and at a further restriction are related
    let coh : Tm → Prop := fun A => ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') A1 B1 A2 B2,
      RedT S k' (A.isub σ) (if isPi then .pi A1 B1 else .sigma A1 B1) →
      RedT S k'' (A.isub (σ.comp σ')) (if isPi then .pi A2 B2 else .sigma A2 B2) →
      (RY k'' (σ.comp σ')).ty (A1.isub σ') A2 ∧
      ∀ a a', (RY k'' (σ.comp σ')).el (A1.isub σ') a a' →
        (RB k'' (σ.comp σ') a).ty ((B1.isub σ').inst a) (B2.inst a')
    { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
          RedT S k' (A.isub σ) (if isPi then .pi A1 B1 else .sigma A1 B1) ∧
          RedT S k' (A'.isub σ) (if isPi then .pi A1' B1' else .sigma A1' B1') ∧
          (RY k' σ).ty A1 A1' ∧ ∀ a a', (RY k' σ).el A1 a a' → (RB k' σ a).ty (B1.inst a) (B1'.inst a')) ∧
          coh A ∧ coh A'
      el := if isPi then piE2 S (fun k' σ => (RY k' σ).el) cod k (ISub.id k)
        else sigmaE2 S (fun k' σ => (RY k' σ).el) cod k (ISub.id k) }
  else if π1 sh = natZ tPath ∨ π1 sh = natZ tIPi then
    let L := π1 (π2 sh)
    let RL : (k' : ℕ) → ISub k' (k + 1) → Pack2 := fun k' σ => rec L h12 (k + 1) k' σ.hom
    if π1 sh = natZ tPath then
      let coh : Tm → Prop := fun A => ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') L1 b0 b1 L2 c0 c1,
        RedT S k' (A.isub σ) (.path L1 b0 b1) → RedT S k'' (A.isub (σ.comp σ')) (.path L2 c0 c1) →
        (RL (k'' + 1) (σ.comp σ').up).ty (L1.isub σ'.up) L2
      { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
            RedT S k' (A.isub σ) (.path L1 b0 b1) ∧ RedT S k' (A'.isub σ) (.path L1' b0' b1') ∧
            (RL (k' + 1) σ.up).ty L1 L1' ∧
            (RL k' (ISub.cons .zero trivial σ)).el (L1.dinst .zero) b0 b0' ∧
            (RL k' (ISub.cons .one trivial σ)).el (L1.dinst .one) b1 b1') ∧ coh A ∧ coh A'
        el := pathE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
    else
      let coh : Tm → Prop := fun A => ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') L1 L2,
        RedT S k' (A.isub σ) (.ipi L1) → RedT S k'' (A.isub (σ.comp σ')) (.ipi L2) →
        (RL (k'' + 1) (σ.comp σ').up).ty (L1.isub σ'.up) L2
      { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ L1 L1',
            RedT S k' (A.isub σ) (.ipi L1) ∧ RedT S k' (A'.isub σ) (.ipi L1') ∧ (RL (k' + 1) σ.up).ty L1 L1') ∧
            coh A ∧ coh A'
        el := ipiE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
  else if π1 sh = natZ tUniv then
    { ty := fun A A' => ∀ k' (σ : ISub k' k),
          RedT S k' (A.isub σ) (.univ (natOf (π2 sh))) ∧ RedT S k' (A'.isub σ) (.univ (natOf (π2 sh)))
      el := fun A T T' => ∃ h : semK S k T ∈ π1 (π2 (Dt k (Hom.id k))),
        (rec (semK S k T) (lt_trans (rank_lt_of_mem h) ((rank_π1_le _).trans_lt ((rank_π2_le _).trans_lt
          (hD k (Hom.id k))))) k k (Hom.id k)).ty T T' }
  else if π1 sh = natZ tEmpty then
    { ty := fun _ _ => True
      el := fun _ _ _ => False }
  else if π1 sh = natZ tGlue then
    let A0 := π1 (π2 sh)
    let φ := cofOf k (π1 (π2 (π2 sh)))
    let Tp := π1 (π2 (π2 (π2 sh)))
    let RA : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => rec A0 h12 k k' σ.hom
    let RT : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ =>
      rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k' (Hom.id k')
    let ET : (k' : ℕ) → ISub k' k → (k'' : ℕ) → ISub k'' k' → Pack2 := fun k' σ k'' σ' =>
      rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k'' σ'.hom
    { ty := fun A A' => ∀ k' (σ : ISub k' k),
          if (φ.restr σ.hom).holds then (RT k' σ).ty (A.isub σ) (A'.isub σ)
          else ∃ A1 φ1 T1 e1 A1' φ1' T1' e1',
            RedT S k' (A.isub σ) (.glue A1 φ1 T1 e1) ∧ RedT S k' (A'.isub σ) (.glue A1' φ1' T1' e1') ∧
            φ1.Scoped k' ∧ φ1'.Scoped k' ∧
            (ival (idEnv k') φ1).face = φ.restr σ.hom ∧ (ival (idEnv k') φ1').face = φ.restr σ.hom ∧
            (RA k' σ).ty A1 A1' ∧
            ∀ k'' (σ' : ISub k'' k'), (φ.restr (σ.comp σ').hom).holds →
              (RT k'' (σ.comp σ')).ty (T1.isub σ') (T1'.isub σ') ∧
              (equivF S (ET k'' (σ.comp σ')) (fun k3 σ3 => RA k3 ((σ.comp σ').comp σ3)) k'' (ISub.id k'')).el
                (Tm.equiv (T1.isub σ') (A1.isub σ')) (e1.isub σ') (e1'.isub σ')
      el := fun A g g' => EB S k A g g' ∧ ∀ k' (σ : ISub k' k),
          if (φ.restr σ.hom).holds then (RT k' σ).el (A.isub σ) (g.isub σ) (g'.isub σ)
          else ∃ A1 φ1 T1 e1 ψ e0 t0 a0 ψ' e0' t0' a0', RedT S k' (A.isub σ) (.glue A1 φ1 T1 e1) ∧
            RedE S k' (A.isub σ) (g.isub σ) (.glueEl ψ e0 t0 a0) ∧ RedE S k' (A.isub σ) (g'.isub σ) (.glueEl ψ' e0' t0' a0') ∧
            I.Entails ψ φ1 ∧ I.Entails φ1 ψ ∧ I.Entails ψ' φ1 ∧ I.Entails φ1 ψ' ∧
            EqTm S k' (cof .one φ1) [] e0 e1 (Tm.equiv T1 A1) ∧ EqTm S k' (cof .one φ1) [] e0' e1 (Tm.equiv T1 A1) ∧
            (RA k' σ).el A1 a0 a0' }
  else if π1 sh = natZ tData then
    let d := natOf (π1 (π2 sh))
    let D : DataDecl := dataD S d
    let Mem : (k' : ℕ) → Hom k' k → Tm → Prop := fun k' g t => semK S k' t ∈ π1 (π2 (Dt k' g))
    let P : (k' : ℕ) → Hom k' k → ℕ → ℕ → List V → Tm → Tm → Tm → Prop := fun k' g c j pre A t t' =>
      (rec (tyLook (π2 (π2 (π2 (π1 (Dt k' g))))) c j pre) (tyLook_rank_lt (hD k' g)) k' k' (Hom.id k')).el A t t'
    -- the argument types at related arguments, from the parameters `ps` (the arguments are related
    -- at `ps`) to the parameters `ps'`
    let argCl : (k' : ℕ) → ISub k' k → Tm → Tm → Prop := fun k' σ ps ps' =>
      ∀ k'' (σ' : ISub k'' k') (c : ℕ) (C : Ctor) (args args' : List Tm), D.ctors[c]? = some C →
        args.length < C.args.length → args'.length = args.length → C.isRec args.length = false →
        (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
          DR2 S d D Mem P k'' (σ.comp σ').hom (.data d (ps.isub σ')) args[j] args'[j]) →
        (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
          P k'' (σ.comp σ').hom c j ((args.take j).map (semK S k''))
            ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ (ps.isub σ').toList.reverse))
            args[j] args'[j]) →
        (rec (tyLook (π2 (π2 (π2 (π1 (Dt k'' (σ.comp σ').hom))))) c args.length (args.map (semK S k'')))
          (tyLook_rank_lt (hD k'' (σ.comp σ').hom)) k'' k'' (Hom.id k'')).ty
          ((C.argTy d D.params.length args.length).substList (args.reverse ++ (ps.isub σ').toList.reverse))
          ((C.argTy d D.params.length args.length).substList (args'.reverse ++ (ps'.isub σ').toList.reverse))
    { ty := fun A A' => ∀ k' (σ : ISub k' k), ∃ ps ps',
          RedT S k' (A.isub σ) (.data d ps) ∧ RedT S k' (A'.isub σ) (.data d ps') ∧
          ps = Tm.ofList ps.toList ∧ ps' = Tm.ofList ps'.toList ∧ argCl k' σ ps ps' ∧ argCl k' σ ps' ps ∧
          argCl k' σ ps ps ∧ argCl k' σ ps' ps'
      el := fun A t t' => EB S k A t t' ∧ DR2 S d D Mem P k (Hom.id k) A t t' }
  else Pack2.bot

/-- The relations, with the types typed, equal and of the code, and the elements typed, equal, and in the
code's element set. -/
def body2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2) : Pack2 :=
  ⟨fun A A' => (IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = self ∧ semK S k A' = self ∧ TyEq S k A A') ∧
    (core2 S k Dt self ρ hD rec).ty A A', fun A t t' => EB S k A t t' ∧ semK S k t ∈ El self (Hom.id k) ∧
    (core2 S k Dt self ρ hD rec).el A t t'⟩

def compF2 (X : V) (rec : (Y : V) → rank Y < rank X → (m k : ℕ) → Hom k m → Pack2) (m k : ℕ) (f : Hom k m) :
    Pack2 :=
  if h : X ≠ ∅ then body2 S k (fun k' g => dat X k' (f.comp g)) (res f X) (rank X)
    (fun k' g => rank_dat_lt h _) rec
  else Pack2.bot

/-- The binary relations for the code `X` (at stage `m`) restricted along `f : Hom k m`. -/
def Comp2 (X : V) : (m k : ℕ) → Hom k m → Pack2 :=
  rank_wf.fix (C := fun _ => (m k : ℕ) → Hom k m → Pack2) (fun X rec => compF2 S X rec) X

theorem Comp2_eq (X : V) : Comp2 S X = compF2 S X (fun Y _ => Comp2 S Y) :=
  rank_wf.fix_eq _ X

/-- Related types at a stage. -/
def RT2 (k : ℕ) (A A' : Tm) : Prop := (Comp2 S (semK S k A) k k (Hom.id k)).ty A A'

/-- Related elements of a type at a stage. -/
def RE2 (k : ℕ) (A t t' : Tm) : Prop := (Comp2 S (semK S k A) k k (Hom.id k)).el A t t'

end

end Model.Whnf
