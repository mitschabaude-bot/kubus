import Model.Canon.Rank

/-!
# Canonicity: computability

Computability of closed types and elements at a stage, indexed by the model's code of the type
and defined by well-founded recursion on codes (`Below`). The relations are given for the code
`X` (at stage `m`) restricted along `f : Hom k m`, and are Kripke by construction: every clause
quantifies over the further interval substitutions `σ : ISub k' k`.

Each clause records the syntactic canonical form of the type (`A ≡ Π A₁ B₁`, …), so that types are
canonical as well as elements.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k k' k'' m n : ℕ}

/-! ### Interval substitutions between stages -/

theorem I.scoped_subst {r : I} {n n' : ℕ} (hr : r.Scoped n) {τ : ℕ → I} (hτ : ∀ i < n, (τ i).Scoped n') :
    (r.subst τ).Scoped n' := by
  induction r <;> simp_all [I.subst, I.Scoped]

theorem I.scoped_shift {r : I} {n : ℕ} (hr : r.Scoped n) : r.shift.Scoped (n + 1) := by
  induction r <;> simp_all [I.shift, I.ren, I.subst, I.Scoped]

/-- An interval substitution from stage `k` to stage `k'`. -/
structure ISub (k' k : ℕ) where
  τ : ℕ → I
  sc : ∀ i < k, (τ i).Scoped k'
  hi : ∀ i, k ≤ i → τ i = .zero

namespace ISub

def id (k : ℕ) : ISub k k := ⟨fun i => if i < k then .var i else .zero,
  fun i hi => by simp [hi, I.Scoped], fun i hi => by simp [show ¬ i < k by omega]⟩

def comp (σ : ISub k' k) (σ' : ISub k'' k') : ISub k'' k :=
  ⟨fun i => (σ.τ i).subst σ'.τ, fun i hi => I.scoped_subst (σ.sc i hi) σ'.sc,
    fun i hi => by show (σ.τ i).subst σ'.τ = _; rw [σ.hi i hi]; rfl⟩

def up (σ : ISub k' k) : ISub (k' + 1) (k + 1) :=
  ⟨I.up σ.τ, fun i hi => by
    cases i with
    | zero => simp [I.up, I.Scoped]
    | succ i => exact I.scoped_shift (σ.sc i (by omega)),
   fun i hi => by
    cases i with
    | zero => omega
    | succ i => simp only [I.up]; rw [σ.hi i (by omega)]; rfl⟩

/-- Extend by an interval term for the variable `0`. -/
def cons (r : I) (hr : r.Scoped k') (σ : ISub k' k) : ISub k' (k + 1) :=
  ⟨fun | 0 => r | i + 1 => σ.τ i, fun i hi => by
    cases i with
    | zero => exact hr
    | succ i => exact σ.sc i (by omega),
   fun i hi => by
    cases i with
    | zero => omega
    | succ i => exact σ.hi i (by omega)⟩

def tail (σ : ISub k' (k + 1)) : ISub k' k :=
  ⟨fun i => σ.τ (i + 1), fun i hi => σ.sc (i + 1) (by omega), fun i hi => σ.hi (i + 1) (by omega)⟩

/-- The cube map of an interval substitution. -/
def hom (σ : ISub k' k) : Hom k' k := fun j => ival (idEnv k') (σ.τ (k - 1 - j))

end ISub

/-- Interval substitution of a term. -/
def _root_.KubusCore.Tm.isub (t : Tm) (σ : ISub k' k) : Tm := t.subst .var σ.τ

/-! ### Judgments at a stage -/

variable (S : Sig)

/-- A closed type at stage `k`. -/
def IsTyK (k : ℕ) (A : Tm) : Prop := ∃ l, HasTy S k .one [] A (.univ l) ∨ A = .univ l

/-- Equality of closed types at stage `k`. -/
def TyEq (k : ℕ) (A B : Tm) : Prop := A = B ∨ ∃ l, EqTm S k .one [] A B (.univ l)

/-- Computability of types (`ty`) and of their elements (`el`, given the type), at a stage. -/
structure Pack where
  ty : Tm → Prop
  el : Tm → Tm → Prop

def Pack.bot : Pack := ⟨fun _ => False, fun _ _ => False⟩

/-- An element relation at all interval substitutions out of stage `k`. -/
abbrev ElR (k : ℕ) := (k' : ℕ) → ISub k' k → Tm → Tm → Prop

/-! ### Element relations of the type formers -/

/-- Elements of `Π`: application to computable arguments is computable. -/
def piE (dom : ElR k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR k') : ElR k := fun k' σ A t =>
  HasTy S k' .one [] t A ∧ ∃ A1 B1, TyEq S k' A (.pi A1 B1) ∧
    ∀ k'' (σ' : ISub k'' k') a, dom k'' (σ.comp σ') (A1.isub σ') a →
      cod k'' (σ.comp σ') a k'' (ISub.id k'') ((B1.isub σ').inst a) (.app (t.isub σ') a)

/-- Elements of `Σ`: computable projections. -/
def sigmaE (dom : ElR k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR k') : ElR k := fun k' σ A t =>
  HasTy S k' .one [] t A ∧ ∃ A1 B1, TyEq S k' A (.sigma A1 B1) ∧
    ∀ k'' (σ' : ISub k'' k'), dom k'' (σ.comp σ') (A1.isub σ') (.fst (t.isub σ')) ∧
      cod k'' (σ.comp σ') (.fst (t.isub σ')) k'' (ISub.id k'') ((B1.isub σ').inst (.fst (t.isub σ')))
        (.snd (t.isub σ'))

/-- Elements of path types: computable at every interval term. `line` is the relation of the line
(a code at stage `k + 1`, the line variable is index `0`). -/
def pathE (line : ElR (k + 1)) : ElR k := fun k' σ A t =>
  HasTy S k' .one [] t A ∧ ∃ L1 b0 b1, TyEq S k' A (.path L1 b0 b1) ∧
    ∀ k'' (σ' : ISub k'' k') (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) ((L1.isub σ'.up).dinst r) (.papp (t.isub σ') r)

/-- Elements of `(i : I) → A`. -/
def ipiE (line : ElR (k + 1)) : ElR k := fun k' σ A t =>
  HasTy S k' .one [] t A ∧ ∃ L1, TyEq S k' A (.ipi L1) ∧
    ∀ k'' (σ' : ISub k'' k') (r : I) (hr : r.Scoped k''),
      line k'' (ISub.cons r hr (σ.comp σ')) ((L1.isub σ'.up).dinst r) (.papp (t.isub σ') r)

/-- A relation constant along the new line variable. -/
def constLine (R : ElR k) : ElR (k + 1) := fun k' σ => R k' σ.tail

/-- `isContr X = Σ (c : X), (x : X) → Path X c x`. -/
def isContrE (X : ElR k) : ElR k :=
  sigmaE S X fun k' σ _ => piE S (fun k'' σ' => X k'' (σ.comp σ'))
    fun k'' σ' _ => pathE S (constLine (fun k3 σ3 => X k3 (σ.comp (σ'.comp σ3))))

/-- `fiber f y = Σ (x : T), Path A (f x) y`. -/
def fiberE (T A : ElR k) : ElR k :=
  sigmaE S T fun k' σ _ => pathE S (constLine (fun k'' σ' => A k'' (σ.comp σ')))

/-- `Equiv T A = Σ (f : T → A), (y : A) → isContr (fiber f y)`. -/
def equivE (T A : ElR k) : ElR k :=
  sigmaE S (piE S T fun k' σ _ k'' σ' => A k'' (σ.comp σ'))
    fun k' σ _ => piE S (fun k'' σ' => A k'' (σ.comp σ'))
      fun k'' σ' _ => isContrE S (fiberE S (fun k3 σ3 => T k3 ((σ.comp σ').comp σ3))
        (fun k3 σ3 => A k3 ((σ.comp σ').comp σ3)))

/-! ### Inductive types -/

/-- Computable elements of an inductive type (`d`, declaration `D`) at the restriction `f` of its
code: canonical constructors with computable arguments (`P` for point arguments, given the code's
argument types: the constructor, the position and the values of the earlier arguments), and in
a HIT formal compositions whose face does not hold. -/
inductive DR {m : ℕ} (d : ℕ) (D : DataDecl)
    (P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Prop) : (k : ℕ) → Hom k m → Tm → Tm → Prop
  | con {k : ℕ} {f : Hom k m} {A t ps : Tm} {c : ℕ} {C : Ctor} {args : List Tm} {rs : List I} :
      D.ctors[c]? = some C → rs.length = C.dims → (∀ r ∈ rs, r.Scoped k) →
      bndAtMap C (rs.map (ival (idEnv k))) (Hom.id k) = none →
      TyEq S k A (.data d ps) →
      EqTm S k .one [] t (.con d c ps (Tm.ofList args) rs) A →
      args.length = C.args.length →
      (∀ j (hj : j < args.length), C.isRec j = true → DR d D P k f A args[j]) →
      (∀ j (hj : j < args.length), C.isRec j = false →
        P k f c j ((args.take j).map (semK S k))
          ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ ps.toList.reverse)) args[j]) →
      DR d D P k f A t
  | hcomp {k : ℕ} {f : Hom k m} {A t ps u a : Tm} {φ : I} :
      D.isHIT = true → φ.Scoped k → ¬ (ival (idEnv k) φ).holds →
      TyEq S k A (.data d ps) →
      EqTm S k .one [] t (.hcomp (.data d ps) φ u a) A →
      DR d D P k f A a →
      (∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
        DR d D P k' (f.comp σ.hom) (A.isub σ) ((u.isub σ.up).dinst r)) →
      DR d D P k f A t

/-! ### Decoding codes -/

/-- The declaration of the inductive type `d`. -/
def dataD (d : ℕ) : DataDecl := match S[d]? with | some (.data D) => D | _ => default

/-- The natural number encoded by `v`. -/
def natOf (v : V) : ℕ := if h : ∃ n, natZ n = v then Classical.choose h else 0

/-- The face encoded by `v`. -/
def cofOf (k : ℕ) (v : V) : Cof k := if h : ∃ φ : Cof k, enc φ = v then Classical.choose h else Cof.bot k

/-- The argument type, in the table of argument types of an inductive type's shape. -/
def tyLook (tbl : V) (c j : ℕ) (pre : List V) : V :=
  if h : ∃ T, ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist pre) T)) ∈ tbl then Classical.choose h
  else ∅

/-! ### Computability -/

theorem tyLook_rank_lt {X : V} {ρ : Ordinal} (h : rank X < ρ) {c j : ℕ} {pre : List V} :
    rank (tyLook (π2 (π2 (π2 (π1 X)))) c j pre) < ρ := by
  have hb : rank (π2 (π2 (π2 (π1 X)))) < ρ :=
    (rank_π2_le _).trans_lt ((rank_π2_le _).trans_lt ((rank_π2_le _).trans_lt ((rank_π1_le _).trans_lt h)))
  unfold tyLook; split
  · rename_i hT
    exact ((rank_pair_right _ _).trans ((rank_pair_right _ _).trans ((rank_pair_right _ _).trans
      (rank_lt_of_mem hT.choose_spec)))).trans hb
  · rw [rank_empty]; exact (bot_le).trans_lt hb

/-- The rank order on values is well founded. -/
theorem rank_wf : WellFounded (fun Y X : V => rank Y < rank X) := InvImage.wf _ wellFounded_lt

theorem rank_appV_res_le (B : V) (g : Hom k' k) (a : V) : rank (appV k' (res g B) a) ≤ rank B := by
  unfold appV here
  refine (rank_apZ_le _ _).trans ?_
  rw [dat_res]; exact rank_dat_le _ _

/-- One step of the definition (without the typing of elements): the relations of the type whose data at the restrictions of
stage `k` are `Dt` and which is the code `self`, given the relations `rec` of the codes of rank
below `ρ`. -/
def core (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack) : Pack :=
  let sh := π1 (Dt k (Hom.id k))
  have hsh : rank sh < ρ := (rank_π1_le _).trans_lt (hD k (Hom.id k))
  have h2 : rank (π2 sh) < ρ := (rank_π2_le _).trans_lt hsh
  have h12 : rank (π1 (π2 sh)) < ρ := (rank_π1_le _).trans_lt h2
  have h22 : rank (π2 (π2 sh)) < ρ := (rank_π2_le _).trans_lt h2
  have h122 : rank (π1 (π2 (π2 sh))) < ρ := (rank_π1_le _).trans_lt h22
  have h222 : rank (π2 (π2 (π2 sh))) < ρ := (rank_π2_le _).trans_lt h22
  have h1222 : rank (π1 (π2 (π2 (π2 sh)))) < ρ := (rank_π1_le _).trans_lt h222
  let base : Tm → Prop := fun A => IsTyK S k A ∧ semK S k A = self
  if π1 sh = natZ tPi ∨ π1 sh = natZ tSigma then
    let Y := π1 (π2 sh)
    let B := π2 (π2 sh)
    let RY : (k' : ℕ) → ISub k' k → Pack := fun k' σ => rec Y h12 k k' σ.hom
    let RB : (k' : ℕ) → ISub k' k → Tm → Pack := fun k' σ a =>
      rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k' (Hom.id k')
    let cod : (k' : ℕ) → ISub k' k → Tm → ElR k' := fun k' σ a k'' σ' =>
      (rec (appV k' (res σ.hom B) (semK S k' a)) ((rank_appV_res_le _ _ _).trans_lt h22) k' k'' σ'.hom).el
    let isPi := π1 sh = natZ tPi
    { ty := fun A => base A ∧ ∃ A1 B1, TyEq S k A (if isPi then .pi A1 B1 else .sigma A1 B1) ∧
          ∀ k' (σ : ISub k' k), (RY k' σ).ty (A1.isub σ) ∧
            ∀ a, (RY k' σ).el (A1.isub σ) a → (RB k' σ a).ty ((B1.isub σ).inst a)
      el := if isPi then piE S (fun k' σ => (RY k' σ).el) cod k (ISub.id k)
        else sigmaE S (fun k' σ => (RY k' σ).el) cod k (ISub.id k) }
  else if π1 sh = natZ tPath ∨ π1 sh = natZ tIPi then
    let L := π1 (π2 sh)
    let RL : (k' : ℕ) → ISub k' (k + 1) → Pack := fun k' σ => rec L h12 (k + 1) k' σ.hom
    if π1 sh = natZ tPath then
      { ty := fun A => base A ∧ ∃ L1 b0 b1, TyEq S k A (.path L1 b0 b1) ∧ ∀ k' (σ : ISub k' k),
            (RL (k' + 1) σ.up).ty (L1.isub σ.up) ∧
            (RL k' (ISub.cons .zero trivial σ)).el ((L1.isub σ.up).dinst .zero) (b0.isub σ) ∧
            (RL k' (ISub.cons .one trivial σ)).el ((L1.isub σ.up).dinst .one) (b1.isub σ)
        el := pathE S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
    else
      { ty := fun A => base A ∧ ∃ L1, TyEq S k A (.ipi L1) ∧ ∀ k' (σ : ISub k' k),
            (RL (k' + 1) σ.up).ty (L1.isub σ.up)
        el := ipiE S (fun k' σ => (RL k' σ).el) k (ISub.id k) }
  else if π1 sh = natZ tUniv then
    { ty := fun A => base A ∧ TyEq S k A (.univ (natOf (π2 sh)))
      el := fun A T => TyEq S k A (.univ (natOf (π2 sh))) ∧ ∃ h : semK S k T ∈ π1 (π2 (Dt k (Hom.id k))),
        (rec (semK S k T) (lt_trans (rank_lt_of_mem h) ((rank_π1_le _).trans_lt ((rank_π2_le _).trans_lt
          (hD k (Hom.id k))))) k k (Hom.id k)).ty T }
  else if π1 sh = natZ tEmpty then
    { ty := base
      el := fun _ _ => False }
  else if π1 sh = natZ tGlue then
    let A0 := π1 (π2 sh)
    let φ := cofOf k (π1 (π2 (π2 sh)))
    let Tp := π1 (π2 (π2 (π2 sh)))
    let RA : (k' : ℕ) → ISub k' k → Pack := fun k' σ => rec A0 h12 k k' σ.hom
    let RT : (k' : ℕ) → ISub k' k → Pack := fun k' σ =>
      rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k' (Hom.id k')
    let ET : (k' : ℕ) → ISub k' k → ElR k' := fun k' σ k'' σ' =>
      (rec (dat Tp k' σ.hom) ((rank_dat_le _ _).trans_lt h1222) k' k'' σ'.hom).el
    { ty := fun A => base A ∧ ∃ A1 φ1 T1 e1, TyEq S k A (.glue A1 φ1 T1 e1) ∧ φ1.Scoped k ∧
          (ival (idEnv k) φ1).face = φ ∧
          (∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1)) ∧
          (∀ k' (σ : ISub k' k), (RA k' σ).ty (A1.isub σ)) ∧
          ∀ k' (σ : ISub k' k), (φ.restr σ.hom).holds →
            (RT k' σ).ty (T1.isub σ) ∧
            equivE S (ET k' σ) (fun k'' σ' => (RA k'' (σ.comp σ')).el) k' (ISub.id k')
              (Tm.equiv (T1.isub σ) (A1.isub σ)) (e1.isub σ)
      el := fun A g => HasTy S k .one [] g A ∧ ∃ A1 φ1 T1 e1, TyEq S k A (.glue A1 φ1 T1 e1) ∧ φ1.Scoped k ∧
          (ival (idEnv k) φ1).face = φ ∧
          (∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1)) ∧
          (∀ k' (σ : ISub k' k), (RA k' σ).el (A1.isub σ) (.unglue (φ1.subst σ.τ) (e1.isub σ) (g.isub σ))) ∧
          ∀ k' (σ : ISub k' k), (φ.restr σ.hom).holds → (RT k' σ).el (T1.isub σ) (g.isub σ) }
  else if π1 sh = natZ tData then
    let d := natOf (π1 (π2 sh))
    let D : DataDecl := dataD S d
    let P : (k' : ℕ) → Hom k' k → ℕ → ℕ → List V → Tm → Tm → Prop := fun k' g c j pre A t =>
      (rec (tyLook (π2 (π2 (π2 (π1 (Dt k' g))))) c j pre) (tyLook_rank_lt (hD k' g)) k' k' (Hom.id k')).el A t
    { ty := fun A => base A ∧ ∃ ps, TyEq S k A (.data d ps) ∧ ps = Tm.ofList ps.toList ∧
          ∀ k' (σ : ISub k' k) (c : ℕ) (C : Ctor) (args : List Tm), D.ctors[c]? = some C →
            args.length < C.args.length → C.isRec args.length = false →
            (∀ j (hj : j < args.length), C.isRec j = true → DR S d D P k' σ.hom (A.isub σ) args[j]) →
            (∀ j (hj : j < args.length), C.isRec j = false →
              P k' σ.hom c j ((args.take j).map (semK S k'))
                ((C.argTy d D.params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse))
                args[j]) →
            (rec (tyLook (π2 (π2 (π2 (π1 (Dt k' σ.hom))))) c args.length (args.map (semK S k')))
              (tyLook_rank_lt (hD k' σ.hom)) k' k' (Hom.id k')).ty
              ((C.argTy d D.params.length args.length).substList (args.reverse ++ (ps.isub σ).toList.reverse))
      el := fun A t => HasTy S k .one [] t A ∧ DR S d D P k (Hom.id k) A t }
  else Pack.bot

/-- The relations, with the elements typed and in the code's element set. -/
def body (k : ℕ) (Dt : (k' : ℕ) → Hom k' k → V) (self : V) (ρ : Ordinal)
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ)
    (rec : (Y : V) → rank Y < ρ → (m k : ℕ) → Hom k m → Pack) : Pack :=
  ⟨(core S k Dt self ρ hD rec).ty, fun A t => HasTy S k .one [] t A ∧ semK S k t ∈ El self (Hom.id k) ∧
    (core S k Dt self ρ hD rec).el A t⟩

/-- The recursion step: the relations of `X` restricted along `f`. -/
def compF (X : V) (rec : (Y : V) → rank Y < rank X → (m k : ℕ) → Hom k m → Pack) (m k : ℕ) (f : Hom k m) : Pack :=
  if h : X ≠ ∅ then body S k (fun k' g => dat X k' (f.comp g)) (res f X) (rank X)
    (fun k' g => rank_dat_lt h _) rec
  else Pack.bot

/-- Computability for the code `X` (at stage `m`) restricted along `f : Hom k m`. -/
def Comp (X : V) : (m k : ℕ) → Hom k m → Pack :=
  rank_wf.fix (C := fun _ => (m k : ℕ) → Hom k m → Pack) (fun X rec => compF S X rec) X

theorem Comp_eq (X : V) : Comp S X = compF S X (fun Y _ => Comp S Y) :=
  rank_wf.fix_eq _ X

end

end Model.Canon
