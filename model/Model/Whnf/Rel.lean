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
`unglue` computes soundly), and their bases `a`; where the face holds, through `T`. Related elements of a
universe are related types whose code is Kan (`KanPG`): composition and transport in all types related at
its restrictions relate related inputs.
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

/-- Elements of path types: related at equal interval terms, and the left side at the endpoints
is related to the type's endpoints. -/
def pathE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1 b0 b1, RedT S k'' (A.isub σ') (.path L1 b0 b1) ∧
    (∀ (r r' : I) (hr : r.Scoped k'') (hr' : r'.Scoped k''), I.Eq r r' →
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r')) ∧
    line k'' (ISub.cons .zero trivial (σ.comp σ')) (L1.dinst .zero) (.papp (t.isub σ') .zero) b0 ∧
    line k'' (ISub.cons .one trivial (σ.comp σ')) (L1.dinst .one) (.papp (t.isub σ') .one) b1

def ipiE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1, RedT S k'' (A.isub σ') (.ipi L1) ∧
    ∀ (r r' : I) (hr : r.Scoped k'') (hr' : r'.Scoped k''), I.Eq r r' →
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r')

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
    (∀ (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
      (Lp k' (ISub.cons r hr σ)).ty (L1.dinst r) (L1'.dinst r')) ∧
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

/-! ### The Kan property, for the relations of a code -/

/-- Composition relates related tubes and bases, with the element relations `E k' σ` at the restrictions
`A.isub σ` of `A` (at `KanH2`, those of `RE2`; in the universe, those of the code of `A`). -/
def KanHG (k : ℕ) (A A' : Tm) (E : (k' : ℕ) → ISub k' k → Tm → Tm → Tm → Prop) : Prop :=
  ∀ (φ φ' : I) (u u' a a' : Tm), HasTy S k .one [] (.hcomp A φ u a) A → HasTy S k .one [] (.hcomp A' φ' u' a') A →
    EqTm S k .one [] (.hcomp A φ u a) (.hcomp A' φ' u' a') A →
    EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift →
    I.Entails φ φ' → I.Entails φ' φ →
    (∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      (ival (idEnv k') (φ.subst σ.τ)).holds → E k' σ (A.isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r')) →
    E k (ISub.id k) A a a' →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      E k' σ (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      E k' σ (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) →
    E k (ISub.id k) A (.hcomp A φ u a) (.hcomp A' φ' u' a')

/-- Transport along related lines (at stage `k + 1`) relates related elements, with the type and element
relations `Rt k' ρ`, `Re k' ρ` at the restrictions `A.isub ρ` of the line `A`. -/
def KanTG (k : ℕ) (A A' : Tm) (Rt : (k' : ℕ) → ISub k' (k + 1) → Tm → Tm → Prop)
    (Re : (k' : ℕ) → ISub k' (k + 1) → Tm → Tm → Tm → Prop) : Prop :=
  (∀ k' (τ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
    Rt k' (ISub.cons r hr τ) (A.isub (ISub.cons r hr τ)) (A'.isub (ISub.cons r' hr' τ))) →
  ∀ (φ φ' : I) (a a' : Tm),
    (∀ k' (σ : ISub k' k) (r : I) (hr : r.Scoped k'), (ival (idEnv k') (φ.subst σ.τ)).holds →
      Rt k' (ISub.cons r hr σ) (A.isub (ISub.cons r hr σ)) (A.isub (ISub.cons .zero trivial σ))) →
    HasTy S k .one [] (.transp A φ a) (A.dinst .one) →
    HasTy S k .one [] (.transp A' φ' a') (A.dinst .one) →
    EqTm S k .one [] (.transp A φ a) (.transp A' φ' a') (A.dinst .one) → I.Entails φ φ' → I.Entails φ' φ →
    Re k (ISub.cons .zero trivial (ISub.id k)) (A.dinst .zero) a a' →
    Re k (ISub.cons .one trivial (ISub.id k)) (A.dinst .one) (.transp A φ a) (.transp A' φ' a')

/-- The Kan property of a code given by its relations `R` at the restrictions of stage `m`: composition
and transport in all pairs of related types. -/
def KanPG (m : ℕ) (R : (k : ℕ) → Hom k m → Pack2) : Prop :=
  (∀ k (f : Hom k m) (A A' : Tm), (R k f).ty A A' → KanHG S k A A' (fun k' σ => (R k' (f.comp σ.hom)).el)) ∧
  (∀ k (f : Hom (k + 1) m) (A A' : Tm), (R (k + 1) f).ty A A' →
    KanTG S k A A' (fun k' ρ => (R k' (f.comp ρ.hom)).ty) (fun k' ρ => (R k' (f.comp ρ.hom)).el))

/-! ### Inductive types -/

mutual
/-- Related elements of an inductive type: related at every restriction (`DR2At`), and coherent: the
weak-head normal form of each side at a restriction, restricted further, is related to that side at the
further restriction. -/
inductive DR2 {m : ℕ} (d : ℕ) (D : DataDecl) (Mem : (k : ℕ) → Hom k m → Tm → Prop)
    (P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Tm → Prop) :
    (k : ℕ) → Hom k m → Tm → Tm → Tm → Prop
  | intro {k : ℕ} {f : Hom k m} {A t t' : Tm} : EqTm S k .one [] t t' A →
      (∀ k' (σ : ISub k' k), DR2At d D Mem P k' (f.comp σ.hom) (A.isub σ) (t.isub σ) (t'.isub σ)) →
      (∀ k' (σ : ISub k' k) w, RedW S (t.isub σ) w → ∀ k'' (ρ : ISub k'' k'),
        DR2At d D Mem P k'' (f.comp (σ.comp ρ).hom) (A.isub (σ.comp ρ)) (w.isub ρ) (t.isub (σ.comp ρ))) →
      (∀ k' (σ : ISub k' k) w, RedW S (t'.isub σ) w → ∀ k'' (ρ : ISub k'' k'),
        DR2At d D Mem P k'' (f.comp (σ.comp ρ).hom) (A.isub (σ.comp ρ)) (w.isub ρ) (t'.isub (σ.comp ρ))) →
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

theorem rank_vnth_le : ∀ (v : V) (j : ℕ), rank (vnth v j) ≤ rank v
  | v, 0 => rank_π1_le v
  | v, j + 1 => (rank_vnth_le (π2 v) j).trans (rank_π2_le v)

/-! ### The relations -/

/-- One step of the definition: the relations of the type whose data at the restrictions of stage
`k` are `Dt` and which is the code `self`, given the relations `rec` of the codes of rank below
`ρ`. -/
def core2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2)
    (recK : (Y : V) → rank Y < ρ → ℕ → Prop) : Pack2 :=
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
        (RL (k'' + 1) (σ.comp σ').up).ty (L1.isub σ'.up) L2 ∧
        (RL k'' (ISub.cons .zero trivial (σ.comp σ'))).el (L2.dinst .zero) (b0.isub σ') c0 ∧
        (RL k'' (ISub.cons .one trivial (σ.comp σ'))).el (L2.dinst .one) (b1.isub σ') c1
      { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
            RedT S k' (A.isub σ) (.path L1 b0 b1) ∧ RedT S k' (A'.isub σ) (.path L1' b0' b1') ∧
            (RL (k' + 1) σ.up).ty L1 L1' ∧
            (∀ (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
              (RL k' (ISub.cons r hr σ)).ty (L1.dinst r) (L1'.dinst r')) ∧
            (RL k' (ISub.cons .zero trivial σ)).el (L1.dinst .zero) b0 b0' ∧
            (RL k' (ISub.cons .one trivial σ)).el (L1.dinst .one) b1 b1') ∧ coh A ∧ coh A'
        el := pathE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
    else
      let coh : Tm → Prop := fun A => ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') L1 L2,
        RedT S k' (A.isub σ) (.ipi L1) → RedT S k'' (A.isub (σ.comp σ')) (.ipi L2) →
        (RL (k'' + 1) (σ.comp σ').up).ty (L1.isub σ'.up) L2
      { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ L1 L1',
            RedT S k' (A.isub σ) (.ipi L1) ∧ RedT S k' (A'.isub σ) (.ipi L1') ∧ (RL (k' + 1) σ.up).ty L1 L1' ∧
            ∀ (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
              (RL k' (ISub.cons r hr σ)).ty (L1.dinst r) (L1'.dinst r')) ∧
            coh A ∧ coh A'
        el := ipiE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
  else if π1 sh = natZ tUniv then
    { ty := fun A A' => ∀ k' (σ : ISub k' k),
          RedT S k' (A.isub σ) (.univ (natOf (π2 sh))) ∧ RedT S k' (A'.isub σ) (.univ (natOf (π2 sh)))
      el := fun A T T' => ∃ h : semK S k T ∈ π1 (π2 (Dt k (Hom.id k))),
        (rec (semK S k T) (lt_trans (rank_lt_of_mem h) ((rank_π1_le _).trans_lt ((rank_π2_le _).trans_lt
          (hD k (Hom.id k))))) k k (Hom.id k)).ty T T' ∧
        recK (semK S k T) (lt_trans (rank_lt_of_mem h) ((rank_π1_le _).trans_lt ((rank_π2_le _).trans_lt
          (hD k (Hom.id k))))) k }
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
    -- the relations at one stage, of types and of elements
    let locT : (k' : ℕ) → ISub k' k → Tm → Tm → Prop := fun k' σ Y Z =>
      if (φ.restr σ.hom).holds then (RT k' σ).ty Y Z
      else ∃ A1 φ1 T1 e1 A1' φ1' T1' e1',
        RedT S k' Y (.glue A1 φ1 T1 e1) ∧ RedT S k' Z (.glue A1' φ1' T1' e1') ∧
        φ1.Scoped k' ∧ φ1'.Scoped k' ∧
        (ival (idEnv k') φ1).face = φ.restr σ.hom ∧ (ival (idEnv k') φ1').face = φ.restr σ.hom ∧
        (RA k' σ).ty A1 A1' ∧
        ∀ k'' (σ' : ISub k'' k'), (φ.restr (σ.comp σ').hom).holds →
          (RT k'' (σ.comp σ')).ty (T1.isub σ') (T1'.isub σ') ∧
          (equivF S (ET k'' (σ.comp σ')) (fun k3 σ3 => RA k3 ((σ.comp σ').comp σ3)) k'' (ISub.id k'')).el
            (Tm.equiv (T1.isub σ') (A1.isub σ')) (e1.isub σ') (e1'.isub σ')
    let locE : (k' : ℕ) → ISub k' k → Tm → Tm → Tm → Prop := fun k' σ X g g' =>
      if (φ.restr σ.hom).holds then (RT k' σ).el X g g'
      else ∃ A1 φ1 T1 e1 ψ e0 t0 a0 ψ' e0' t0' a0', RedT S k' X (.glue A1 φ1 T1 e1) ∧
        RedE S k' X g (.glueEl ψ e0 t0 a0) ∧ RedE S k' X g' (.glueEl ψ' e0' t0' a0') ∧
        I.Entails ψ φ1 ∧ I.Entails φ1 ψ ∧ I.Entails ψ' φ1 ∧ I.Entails φ1 ψ' ∧
        EqTm S k' (cof .one φ1) [] e0 e1 (Tm.equiv T1 A1) ∧ EqTm S k' (cof .one φ1) [] e0' e1 (Tm.equiv T1 A1) ∧
        (RA k' σ).el A1 a0 a0' ∧
        -- where the face holds, the fibers are related, and the bases agree with the fibers through `e1`
        ∀ k'' (σ' : ISub k'' k'), (φ.restr (σ.comp σ').hom).holds →
          (RT k'' (σ.comp σ')).el (T1.isub σ') (t0.isub σ') (t0'.isub σ') ∧
          (RA k'' (σ.comp σ')).el (A1.isub σ') (a0.isub σ') (.app (.fst (e1.isub σ')) (t0.isub σ')) ∧
          (RA k'' (σ.comp σ')).el (A1.isub σ') (a0'.isub σ') (.app (.fst (e1.isub σ')) (t0'.isub σ'))
    -- coherence: where the face does not hold, the normal form at a restriction, restricted further, is
    -- related to the further restriction
    let cohT : Tm → Prop := fun A => ∀ k' (σ : ISub k' k), ¬ (φ.restr σ.hom).holds → ∀ W, RedW S (A.isub σ) W →
      ∀ k'' (ρ : ISub k'' k'), locT k'' (σ.comp ρ) (W.isub ρ) (A.isub (σ.comp ρ))
    let cohE : Tm → Tm → Prop := fun A g => ∀ k' (σ : ISub k' k), ¬ (φ.restr σ.hom).holds → ∀ w,
      RedW S (g.isub σ) w → ∀ k'' (ρ : ISub k'' k'),
        ((φ.restr (σ.comp ρ).hom).holds → ∀ ψ e0 t0 a0, w = .glueEl ψ e0 t0 a0 →
          (RT k'' (σ.comp ρ)).el (A.isub (σ.comp ρ)) (t0.isub ρ) (g.isub (σ.comp ρ))) ∧
        (¬ (φ.restr (σ.comp ρ).hom).holds →
          locE k'' (σ.comp ρ) (A.isub (σ.comp ρ)) (w.isub ρ) (g.isub (σ.comp ρ)))
    { ty := fun A A' => (∀ k' (σ : ISub k' k), locT k' σ (A.isub σ) (A'.isub σ)) ∧ cohT A ∧ cohT A'
      el := fun A g g' => EB S k A g g' ∧ (∀ k' (σ : ISub k' k), locE k' σ (A.isub σ) (g.isub σ) (g'.isub σ)) ∧
        cohE A g ∧ cohE A g' }
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
    -- the parameters: a parameter of a universe type is related as a type at its value's code, the
    -- others at the code of their type
    let pe : (k' : ℕ) → Hom k' k → ℕ → V := fun k' g j => vnth (π2 (π1 (π2 (π2 (π1 (Dt k' g)))))) j
    have hpe : ∀ k' (g : Hom k' k) j, rank (π2 (pe k' g j)) < ρ := fun k' g j =>
      lt_of_le_of_lt ((rank_π2_le _).trans ((rank_vnth_le _ _).trans ((rank_π2_le _).trans ((rank_π1_le _).trans
        ((rank_π2_le _).trans ((rank_π2_le _).trans (rank_π1_le _))))))) (hD k' g)
    let parCl : (k' : ℕ) → ISub k' k → Tm → Tm → Prop := fun k' σ ps ps' =>
      ∀ j (p p' : Tm), ps.toList[j]? = some p → ps'.toList[j]? = some p' →
        (π1 (pe k' σ.hom j) = natZ 1 → (rec (π2 (pe k' σ.hom j)) (hpe k' σ.hom j) k' k' (Hom.id k')).ty p p') ∧
        (π1 (pe k' σ.hom j) = natZ 0 → ∀ Aj, D.params[j]? = some Aj →
          (rec (π2 (pe k' σ.hom j)) (hpe k' σ.hom j) k' k' (Hom.id k')).ty
            (Aj.substList (ps.toList.take j).reverse) (Aj.substList (ps'.toList.take j).reverse) ∧
          (rec (π2 (pe k' σ.hom j)) (hpe k' σ.hom j) k' k' (Hom.id k')).el
            (Aj.substList (ps.toList.take j).reverse) p p')
    -- coherence: the parameters of the normal form at a restriction, restricted further, are related
    -- to those of the normal form at the further restriction
    let coh : Tm → Prop := fun A => ∀ k' (σ : ISub k' k) k'' (σ' : ISub k'' k') ps1 ps2,
      RedT S k' (A.isub σ) (.data d ps1) → RedT S k'' (A.isub (σ.comp σ')) (.data d ps2) →
      argCl k'' (σ.comp σ') (ps1.isub σ') ps2 ∧ argCl k'' (σ.comp σ') ps2 (ps1.isub σ') ∧
      parCl k'' (σ.comp σ') (ps1.isub σ') ps2
    { ty := fun A A' => (∀ k' (σ : ISub k' k), ∃ ps ps',
          RedT S k' (A.isub σ) (.data d ps) ∧ RedT S k' (A'.isub σ) (.data d ps') ∧
          ps = Tm.ofList ps.toList ∧ ps' = Tm.ofList ps'.toList ∧ argCl k' σ ps ps' ∧ argCl k' σ ps' ps ∧
          argCl k' σ ps ps ∧ argCl k' σ ps' ps' ∧ parCl k' σ ps ps') ∧ coh A ∧ coh A'
      el := fun A t t' => EB S k A t t' ∧ DR2 S d D Mem P k (Hom.id k) A t t' }
  else Pack2.bot

/-- The relations, with the types typed, equal and of the code, and the elements typed, equal, and in the
code's element set. -/
def body2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2)
    (recK : (Y : V) → rank Y < ρ → ℕ → Prop) : Pack2 :=
  ⟨fun A A' => (IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = self ∧ semK S k A' = self ∧ TyEq S k A A') ∧
    (core2 S k Dt self ρ hD rec recK).ty A A', fun A t t' => EB S k A t t' ∧ semK S k t ∈ El self (Hom.id k) ∧
    (core2 S k Dt self ρ hD rec recK).el A t t'⟩

def compF2 (X : V) (rec : (Y : V) → rank Y < rank X → (m k : ℕ) → Hom k m → Pack2)
    (recK : (Y : V) → rank Y < rank X → ℕ → Prop) (m k : ℕ) (f : Hom k m) : Pack2 :=
  if h : X ≠ ∅ then body2 S k (fun k' g => dat X k' (f.comp g)) (res f X) (rank X)
    (fun k' g => rank_dat_lt h _) rec recK
  else Pack2.bot

/-- Hereditary Kan of the components of a datum. Dependent fibres are required only at related
arguments. Universe elements carry their own hereditary Kan in the element relation. -/
def kanParts2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2)
    (recK : (Y : V) → rank Y < ρ → ℕ → Prop) : Prop :=
  let sh := π1 (Dt k (Hom.id k))
  have hsh : rank sh < ρ := (rank_π1_le _).trans_lt (hD k (Hom.id k))
  have h2 : rank (π2 sh) < ρ := (rank_π2_le _).trans_lt hsh
  have h12 : rank (π1 (π2 sh)) < ρ := (rank_π1_le _).trans_lt h2
  have h22 : rank (π2 (π2 sh)) < ρ := (rank_π2_le _).trans_lt h2
  have h1222 : rank (π1 (π2 (π2 (π2 sh)))) < ρ := (rank_π1_le _).trans_lt
    ((rank_π2_le _).trans_lt h22)
  if π1 sh = natZ tPi ∨ π1 sh = natZ tSigma then
    let Y := π1 (π2 sh)
    let B := π2 (π2 sh)
    recK Y h12 k ∧ ∀ A a a', (rec Y h12 k k (Hom.id k)).el A a a' →
      recK (appV k B (semK S k a)) ((rank_apZ_le _ _).trans_lt ((rank_dat_le _ _).trans_lt h22)) k
  else if π1 sh = natZ tPath ∨ π1 sh = natZ tIPi then
    recK (π1 (π2 sh)) h12 (k + 1)
  else if π1 sh = natZ tGlue then
    let φ := cofOf k (π1 (π2 (π2 sh)))
    let Tp := π1 (π2 (π2 (π2 sh)))
    recK (π1 (π2 sh)) h12 k ∧ ∀ k' (g : Hom k' k), (φ.restr g).holds →
      recK (dat Tp k' g) ((rank_dat_le _ _).trans_lt h1222) k'
  else if π1 sh = natZ tData then
    let pe := fun j => vnth (π2 (π1 (π2 (π2 sh)))) j
    have hpe : ∀ j, rank (π2 (pe j)) < ρ := fun j =>
      ((rank_π2_le _).trans ((rank_vnth_le _ _).trans ((rank_π2_le _).trans
        ((rank_π1_le _).trans ((rank_π2_le _).trans (rank_π2_le _)))))).trans_lt hsh
    ∀ j, π1 (pe j) = natZ 0 ∨ π1 (pe j) = natZ 1 → recK (π2 (pe j)) (hpe j) k
  else True

/-- The relations and hereditary Kan predicate of a code, defined together by rank recursion. -/
structure Code2 where
  rel : (m k : ℕ) → Hom k m → Pack2
  kan : ℕ → Prop

def codeF2 (X : V) (rec : (Y : V) → rank Y < rank X → Code2) : Code2 :=
  let R := compF2 S X (fun Y h => (rec Y h).rel) (fun Y h => (rec Y h).kan)
  ⟨R, fun m => KanPG S m (R m) ∧ ∀ k (f : Hom k m),
    if h : X ≠ ∅ then kanParts2 S k (fun k' g => dat X k' (f.comp g)) (rank X)
      (fun k' g => rank_dat_lt h _) (fun Y h => (rec Y h).rel) (fun Y h => (rec Y h).kan)
    else True⟩

def code2 (X : V) : Code2 := rank_wf.fix (fun X rec => codeF2 S X rec) X

theorem code2_eq (X : V) : code2 S X = codeF2 S X (fun Y _ => code2 S Y) := rank_wf.fix_eq _ X

attribute [irreducible] code2

/-- The binary relations for the code `X` (at stage `m`) restricted along `f : Hom k m`. -/
def Comp2 (X : V) : (m k : ℕ) → Hom k m → Pack2 := (code2 S X).rel

/-- A code is Kan, hereditarily in its components at every restriction. -/
def HerKan2 (m : ℕ) (X : V) : Prop := (code2 S X).kan m

theorem Comp2_eq (X : V) : Comp2 S X = compF2 S X (fun Y _ => Comp2 S Y) (fun Y _ m => HerKan2 S m Y) := by
  unfold Comp2; rw [code2_eq]; rfl

theorem HerKan2_eq (X : V) (m : ℕ) : HerKan2 S m X ↔ KanPG S m (Comp2 S X m) ∧ ∀ k (f : Hom k m),
    if h : X ≠ ∅ then kanParts2 S k (fun k' g => dat X k' (f.comp g)) (rank X)
      (fun k' g => rank_dat_lt h _) (fun Y _ => Comp2 S Y) (fun Y _ m => HerKan2 S m Y)
    else True := by
  unfold HerKan2; rw [code2_eq]; rw [Comp2_eq]; rfl

/-- Related types at a stage. -/
def RT2 (k : ℕ) (A A' : Tm) : Prop := (Comp2 S (semK S k A) k k (Hom.id k)).ty A A'

/-- Related elements of a type at a stage. -/
def RE2 (k : ℕ) (A t t' : Tm) : Prop := (Comp2 S (semK S k A) k k (Hom.id k)).el A t t'

/-! ### The Kan property -/

/-- Related tubes: related where the face holds, at all restrictions and `I.Eq`-equal points. -/
def Tube2 (k : ℕ) (A : Tm) (φ : I) (u u' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
    (ival (idEnv k') (φ.subst σ.τ)).holds → RE2 S k' (A.isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r')

/-- Composition in related types relates related tubes and bases. -/
def KanH2 (k : ℕ) (A A' : Tm) : Prop :=
  ∀ (φ φ' : I) (u u' a a' : Tm), HasTy S k .one [] (.hcomp A φ u a) A → HasTy S k .one [] (.hcomp A' φ' u' a') A →
    EqTm S k .one [] (.hcomp A φ u a) (.hcomp A' φ' u' a') A →
    EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift →
    I.Entails φ φ' → I.Entails φ' φ → Tube2 S k A φ u u' → RE2 S k A a a' →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) →
    RE2 S k A (.hcomp A φ u a) (.hcomp A' φ' u' a')

/-- Lines (at stage `k + 1`) related at `I.Eq`-equal points of every restriction. -/
def LineRob (k : ℕ) (A A' : Tm) : Prop :=
  ∀ k' (τ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
    RT2 S k' (A.isub (ISub.cons r hr τ)) (A'.isub (ISub.cons r' hr' τ))

/-- A line (at stage `k + 1`) is constant where the face `φ` holds. -/
def LineConst (k : ℕ) (A : Tm) (φ : I) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I) (hr : r.Scoped k'), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RT2 S k' (A.isub (ISub.cons r hr σ)) (A.isub (ISub.cons .zero trivial σ))

/-- Transport along related lines (at stage `k + 1`) relates related elements. -/
def KanT2 (k : ℕ) (A A' : Tm) : Prop :=
  LineRob S k A A' →
  ∀ (φ φ' : I) (a a' : Tm), LineConst S k A φ → HasTy S k .one [] (.transp A φ a) (A.dinst .one) →
    HasTy S k .one [] (.transp A' φ' a') (A.dinst .one) →
    EqTm S k .one [] (.transp A φ a) (.transp A' φ' a') (A.dinst .one) → I.Entails φ φ' → I.Entails φ' φ →
    RE2 S k (A.dinst .zero) a a' → RE2 S k (A.dinst .one) (.transp A φ a) (.transp A' φ' a')

/-- The Kan properties of all pairs of types related at a restriction of the code `X`. -/
def KanP2 (m : ℕ) (X : V) : Prop :=
  (∀ k (f : Hom k m) (A A' : Tm), (Comp2 S X m k f).ty A A' → KanH2 S k A A') ∧
  (∀ k (f : Hom (k + 1) m) (A A' : Tm), (Comp2 S X m (k + 1) f).ty A A' → KanT2 S k A A')


end

end Model.Whnf
