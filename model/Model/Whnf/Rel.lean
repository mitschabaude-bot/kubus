import Model.Whnf.Step
import Model.Canon.Comp

/-!
# The binary computability relation (a PER with judgmental equality)

Related closed types and elements at a stage, indexed by the model's code (as `Model.Canon.Comp`)
and Kripke by construction. Every relation includes the judgmental equality of the two sides. The
types of every former, and the elements of inductive types, are observed through their weak-head
normal forms (`RedW`), which are unique: this makes the relations transitive without any
injectivity of type formers or constructors. Elements of `Π`, `Σ`, path types and Glue types are
observed through their eliminations.
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

/-! ### Element relations of the type formers -/

def piE2 (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ A1 B1, RedW S (A.isub σ') (.pi A1 B1) ∧
    ∀ a a', dom k'' (σ.comp σ') A1 a a' →
      cod k'' (σ.comp σ') a k'' (ISub.id k'') (B1.inst a) (.app (t.isub σ') a) (.app (t'.isub σ') a')

def sigmaE2 (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ A1 B1, RedW S (A.isub σ') (.sigma A1 B1) ∧
    dom k'' (σ.comp σ') A1 (.fst (t.isub σ')) (.fst (t'.isub σ')) ∧
    cod k'' (σ.comp σ') (.fst (t.isub σ')) k'' (ISub.id k'') (B1.inst (.fst (t.isub σ')))
      (.snd (t.isub σ')) (.snd (t'.isub σ'))

def pathE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1 b0 b1, RedW S (A.isub σ') (.path L1 b0 b1) ∧
    ∀ (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r)

def ipiE2 (line : ElR2 (k + 1)) : ElR2 k := fun k' σ A t t' =>
  EB S k' A t t' ∧ ∀ k'' (σ' : ISub k'' k'), ∃ L1, RedW S (A.isub σ') (.ipi L1) ∧
    ∀ (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) (L1.dinst r) (.papp (t.isub σ') r) (.papp (t'.isub σ') r)

def constLine2 (R : ElR2 k) : ElR2 (k + 1) := fun k' σ => R k' σ.tail

def isContrE2 (X : ElR2 k) : ElR2 k :=
  sigmaE2 S X fun k' σ _ => piE2 S (fun k'' σ' => X k'' (σ.comp σ'))
    fun k'' σ' _ => pathE2 S (constLine2 (fun k3 σ3 => X k3 (σ.comp (σ'.comp σ3))))

def fiberE2 (T A : ElR2 k) : ElR2 k :=
  sigmaE2 S T fun k' σ _ => pathE2 S (constLine2 (fun k'' σ' => A k'' (σ.comp σ')))

def equivE2 (T A : ElR2 k) : ElR2 k :=
  sigmaE2 S (piE2 S T fun k' σ _ k'' σ' => A k'' (σ.comp σ'))
    fun k' σ _ => piE2 S (fun k'' σ' => A k'' (σ.comp σ'))
      fun k'' σ' _ => isContrE2 S (fiberE2 S (fun k3 σ3 => T k3 ((σ.comp σ').comp σ3))
        (fun k3 σ3 => A k3 ((σ.comp σ').comp σ3)))

/-! ### Inductive types -/

/-- Related elements of an inductive type: weak-head normal forms which are the same constructor
with related arguments (point arguments by `P`, given the values of the earlier arguments of the
left side), or, in a HIT, formal compositions with equivalent faces that do not hold, related
bases and tubes related where the face holds. -/
inductive DR2 {m : ℕ} (d : ℕ) (D : DataDecl) (Mem : (k : ℕ) → Hom k m → Tm → Prop)
    (P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Tm → Prop) :
    (k : ℕ) → Hom k m → Tm → Tm → Tm → Prop
  | con {k : ℕ} {f : Hom k m} {A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
      {rs rs' : List I} :
      Mem k f t → Mem k f t' → D.ctors[c]? = some C → RedW S A (.data d ps) → ps = Tm.ofList ps.toList →
      RedW S t (.con d c qs (Tm.ofList args) rs) → RedW S t' (.con d c qs' (Tm.ofList args') rs') →
      rs.length = C.dims → rs'.length = C.dims → (∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r') →
      (∀ r ∈ rs, r.Scoped k) → (∀ r ∈ rs', r.Scoped k) →
      args.length = C.args.length → args'.length = C.args.length →
      (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
        DR2 d D Mem P k f (.data d ps) args[j] args'[j]) →
      (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
        P k f c j ((args.take j).map (semK S k))
          ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) args[j] args'[j]) →
      DR2 d D Mem P k f A t t'
  | hcomp {k : ℕ} {f : Hom k m} {A t t' ps qs qs' u u' a a' : Tm} {φ φ' : I} :
      Mem k f t → Mem k f t' → D.isHIT = true → RedW S A (.data d ps) → ps = Tm.ofList ps.toList →
      RedW S t (.hcomp (.data d qs) φ u a) → RedW S t' (.hcomp (.data d qs') φ' u' a') →
      φ.Scoped k → φ'.Scoped k → I.Entails φ φ' → I.Entails φ' φ →
      DR2 d D Mem P k f (.data d ps) a a' →
      (∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
        DR2 d D Mem P k' (f.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)) →
      DR2 d D Mem P k f A t t'

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
  let base : Tm → Tm → Prop := fun A A' =>
    IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = self ∧ semK S k A' = self ∧ TyEq S k A A'
  if π1 sh = natZ tPi ∨ π1 sh = natZ tSigma then
    let Y := π1 (π2 sh)
    let B := π2 (π2 sh)
    let RY : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => rec Y h12 k k' σ.hom
    let RB : (k' : ℕ) → ISub k' k → Tm → Pack2 := fun k' σ a =>
      rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k' (Hom.id k')
    let cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k' := fun k' σ a k'' σ' =>
      (rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k'' σ'.hom).el
    let isPi := π1 sh = natZ tPi
    { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
          RedW S (A.isub σ) (if isPi then .pi A1 B1 else .sigma A1 B1) ∧
          RedW S (A'.isub σ) (if isPi then .pi A1' B1' else .sigma A1' B1') ∧
          (RY k' σ).ty A1 A1' ∧ ∀ a a', (RY k' σ).el A1 a a' → (RB k' σ a).ty (B1.inst a) (B1'.inst a')
      el := if isPi then piE2 S (fun k' σ => (RY k' σ).el) cod k (ISub.id k)
        else sigmaE2 S (fun k' σ => (RY k' σ).el) cod k (ISub.id k) }
  else if π1 sh = natZ tPath ∨ π1 sh = natZ tIPi then
    let L := π1 (π2 sh)
    let RL : (k' : ℕ) → ISub k' (k + 1) → Pack2 := fun k' σ => rec L h12 (k + 1) k' σ.hom
    if π1 sh = natZ tPath then
      { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
            RedW S (A.isub σ) (.path L1 b0 b1) ∧ RedW S (A'.isub σ) (.path L1' b0' b1') ∧
            (RL (k' + 1) σ.up).ty L1 L1' ∧
            (RL k' (ISub.cons .zero trivial σ)).el (L1.dinst .zero) b0 b0' ∧
            (RL k' (ISub.cons .one trivial σ)).el (L1.dinst .one) b1 b1'
        el := pathE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
    else
      { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k), ∃ L1 L1',
            RedW S (A.isub σ) (.ipi L1) ∧ RedW S (A'.isub σ) (.ipi L1') ∧ (RL (k' + 1) σ.up).ty L1 L1'
        el := ipiE2 S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
  else if π1 sh = natZ tUniv then
    { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k),
          RedW S (A.isub σ) (.univ (natOf (π2 sh))) ∧ RedW S (A'.isub σ) (.univ (natOf (π2 sh)))
      el := fun A T T' => ∃ h : semK S k T ∈ π1 (π2 (Dt k (Hom.id k))),
        (rec (semK S k T) (lt_trans (rank_lt_of_mem h) ((rank_π1_le _).trans_lt ((rank_π2_le _).trans_lt
          (hD k (Hom.id k))))) k k (Hom.id k)).ty T T' }
  else if π1 sh = natZ tEmpty then
    { ty := base
      el := fun _ _ _ => False }
  else if π1 sh = natZ tGlue then
    let A0 := π1 (π2 sh)
    let φ := cofOf k (π1 (π2 (π2 sh)))
    let Tp := π1 (π2 (π2 (π2 sh)))
    let RA : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => rec A0 h12 k k' σ.hom
    let RT : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ =>
      rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k' (Hom.id k')
    let ET : (k' : ℕ) → ISub k' k → ElR2 k' := fun k' σ k'' σ' =>
      (rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k'' σ'.hom).el
    { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k),
          if (φ.restr σ.hom).holds then (RT k' σ).ty (A.isub σ) (A'.isub σ)
          else ∃ A1 φ1 T1 e1 A1' φ1' T1' e1',
            RedW S (A.isub σ) (.glue A1 φ1 T1 e1) ∧ RedW S (A'.isub σ) (.glue A1' φ1' T1' e1') ∧
            φ1.Scoped k' ∧ φ1'.Scoped k' ∧
            (ival (idEnv k') φ1).face = φ.restr σ.hom ∧ (ival (idEnv k') φ1').face = φ.restr σ.hom ∧
            (RA k' σ).ty A1 A1' ∧
            ∀ k'' (σ' : ISub k'' k'), (φ.restr (σ.comp σ').hom).holds →
              (RT k'' (σ.comp σ')).ty (T1.isub σ') (T1'.isub σ') ∧
              equivE2 S (ET k'' (σ.comp σ')) (fun k3 σ3 => (RA k3 ((σ.comp σ').comp σ3)).el) k'' (ISub.id k'')
                (Tm.equiv (T1.isub σ') (A1.isub σ')) (e1.isub σ') (e1'.isub σ')
      el := fun A g g' => EB S k A g g' ∧ ∀ k' (σ : ISub k' k),
          if (φ.restr σ.hom).holds then (RT k' σ).el (A.isub σ) (g.isub σ) (g'.isub σ)
          else ∃ A1 φ1 T1 e1, RedW S (A.isub σ) (.glue A1 φ1 T1 e1) ∧
            (RA k' σ).el A1 (.unglue φ1 e1 (g.isub σ)) (.unglue φ1 e1 (g'.isub σ)) }
  else if π1 sh = natZ tData then
    let d := natOf (π1 (π2 sh))
    let D : DataDecl := dataD S d
    let Mem : (k' : ℕ) → Hom k' k → Tm → Prop := fun k' g t => semK S k' t ∈ π1 (π2 (Dt k' g))
    let P : (k' : ℕ) → Hom k' k → ℕ → ℕ → List V → Tm → Tm → Tm → Prop := fun k' g c j pre A t t' =>
      (rec (tyLook (π2 (π2 (π2 (π1 (Dt k' g))))) c j pre) (tyLook_rank_lt (hD k' g)) k' k' (Hom.id k')).el A t t'
    { ty := fun A A' => base A A' ∧ ∀ k' (σ : ISub k' k), ∃ ps ps',
          RedW S (A.isub σ) (.data d ps) ∧ RedW S (A'.isub σ) (.data d ps') ∧
          ps = Tm.ofList ps.toList ∧ ps' = Tm.ofList ps'.toList ∧
          ∀ (c : ℕ) (C : Ctor) (args args' : List Tm), D.ctors[c]? = some C →
            args.length < C.args.length → args'.length = args.length → C.isRec args.length = false →
            (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
              DR2 S d D Mem P k' σ.hom (.data d ps) args[j] args'[j]) →
            (∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = false →
              P k' σ.hom c j ((args.take j).map (semK S k'))
                ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse))
                args[j] args'[j]) →
            (rec (tyLook (π2 (π2 (π2 (π1 (Dt k' σ.hom))))) c args.length (args.map (semK S k')))
              (tyLook_rank_lt (hD k' σ.hom)) k' k' (Hom.id k')).ty
              ((C.argTy d D.params.length args.length).substList (args.reverse ++ ps.toList.reverse))
              ((C.argTy d D.params.length args.length).substList (args'.reverse ++ ps'.toList.reverse))
      el := fun A t t' => EB S k A t t' ∧ DR2 S d D Mem P k (Hom.id k) A t t' }
  else Pack2.bot

/-- The relations, with the elements typed, equal, and in the code's element set. -/
def body2 (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack2) : Pack2 :=
  ⟨(core2 S k Dt self ρ hD rec).ty, fun A t t' => EB S k A t t' ∧ semK S k t ∈ El self (Hom.id k) ∧
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
