import Model.Interval

/-!
# The De Morgan cube category

Objects are natural numbers `m` (the number of interval variables). An interval value at
stage `m` is a function `M4^m → M4` definable by an interval term in `m` variables (`DM m`);
equality is equality of functions, i.e. `M4`-equality, i.e. equality in the free De Morgan
algebra. A cube map `Hom k m` is an `m`-tuple of such values at stage `k`; it acts on points
`M4^k → M4^m`, and composition is composition of these actions (substitution), so the category
laws hold definitionally on the actions.

Presheaves are contravariant: a value at stage `m` restricts along `f : Hom k m` to stage `k`.

A face (cofibration) at stage `m` *holds* if the corresponding interval value is `1`, which is
the case iff it is `1` at the all-`a` point (`DM.holds_iff`). Faces are compared by their
Kleene reading `DM.face` (the `K3`-points where they are `1`), which is the spec's face lattice.
-/

set_option autoImplicit false

namespace Model

open KubusCore
open KubusCore.I.M4 (zero a b one)

/-- Points of the `m`-cube with coordinates in `M4`. -/
abbrev Pt (m : ℕ) := Fin m → M4

/-- Extend a point by zeros, to evaluate interval terms. -/
def Pt.ext {m : ℕ} (p : Pt m) : ℕ → M4 := fun n => if h : n < m then p ⟨n, h⟩ else zero

/-- The all-`a` point. -/
def Pt.allA (m : ℕ) : Pt m := fun _ => a

def Pt.IsK3 {m : ℕ} (p : Pt m) : Prop := ∀ i, M4.IsK3 (p i)

theorem Pt.allA_isK3 (m : ℕ) : (Pt.allA m).IsK3 := fun _ => by simp [Pt.allA, M4.IsK3]

theorem Pt.ext_isK3 {m : ℕ} {p : Pt m} (hp : p.IsK3) (n : ℕ) : M4.IsK3 (p.ext n) := by
  unfold Pt.ext; split
  · exact hp _
  · simp [M4.IsK3]

theorem eval_isK3 {ρ : ℕ → M4} (hρ : ∀ n, M4.IsK3 (ρ n)) (r : I) : M4.IsK3 (r.eval ρ) := by
  induction r with
  | zero | one => simp [I.eval, M4.IsK3]
  | var i => exact hρ i
  | neg r ih => exact ih.neg
  | and r s ihr ihs => exact ihr.meet ihs
  | or r s ihr ihs => exact ihr.join ihs

theorem scoped_subst_all {σ : ℕ → I} {k : ℕ} (hσ : ∀ n, (σ n).Scoped k) (r : I) :
    (r.subst σ).Scoped k := by
  induction r <;> simp_all [I.subst, I.Scoped]

/-- `fn` is definable by an interval term in `m` variables. -/
def Definable (m : ℕ) (fn : Pt m → M4) : Prop :=
  ∃ r : I, r.Scoped m ∧ ∀ p, fn p = r.eval p.ext

/-- Definable functions are closed under composition with definable tuples. -/
theorem Definable.comp {m k : ℕ} {g : Pt m → M4} (hg : Definable m g) {F : Pt k → Pt m}
    (hF : ∀ j, Definable k (fun q => F q j)) : Definable k (fun q => g (F q)) := by
  obtain ⟨r, hr, hgr⟩ := hg
  choose s hs hsF using hF
  let σ : ℕ → I := fun n => if h : n < m then s ⟨n, h⟩ else .zero
  refine ⟨r.subst σ, scoped_subst_all (fun n => ?_) r, fun q => ?_⟩
  · simp only [σ]; split
    · exact hs _
    · trivial
  · show g (F q) = _
    rw [hgr, Cof.eval_subst]
    apply Cof.eval_congr hr
    intro n hn
    simp [σ, Pt.ext, hn, hsF]

theorem Definable.isK3 {m : ℕ} {g : Pt m → M4} (hg : Definable m g) {p : Pt m} (hp : p.IsK3) :
    M4.IsK3 (g p) := by
  obtain ⟨r, -, h⟩ := hg; rw [h]; exact eval_isK3 (Pt.ext_isK3 hp) r

/-- Interval values at stage `m`: the free De Morgan algebra on `m` generators. -/
@[ext]
structure DM (m : ℕ) where
  fn : Pt m → M4
  defn : Definable m fn

/-- Cube maps: `Hom k m` is an `m`-tuple of interval values at stage `k`. -/
abbrev Hom (k m : ℕ) := Fin m → DM k

namespace Hom

variable {k m n : ℕ}

/-- The action of a cube map on points. -/
def app (f : Hom k m) (p : Pt k) : Pt m := fun j => (f j).fn p

theorem app_isK3 (f : Hom k m) {p : Pt k} (hp : p.IsK3) : (f.app p).IsK3 :=
  fun j => (f j).defn.isK3 hp

end Hom

namespace DM

variable {k m n : ℕ}

def ofTerm (r : I) (hr : r.Scoped m) : DM m := ⟨fun p => r.eval p.ext, r, hr, fun _ => rfl⟩

def zero (m : ℕ) : DM m := ofTerm .zero trivial
def one (m : ℕ) : DM m := ofTerm .one trivial
def var (j : Fin m) : DM m := ofTerm (.var j) j.isLt

@[simp] theorem zero_fn (p : Pt m) : (zero m).fn p = I.M4.zero := rfl
@[simp] theorem one_fn (p : Pt m) : (one m).fn p = I.M4.one := rfl
@[simp] theorem var_fn (j : Fin m) (p : Pt m) : (var j).fn p = p j := by
  simp [var, ofTerm, I.eval, Pt.ext]

/-- Restriction along a cube map: substitution. -/
def restr (g : DM m) (f : Hom k m) : DM k :=
  ⟨fun q => g.fn (f.app q), g.defn.comp fun j => (f j).defn⟩

@[simp] theorem restr_fn (g : DM m) (f : Hom k m) (q : Pt k) : (g.restr f).fn q = g.fn (f.app q) :=
  rfl

/-- A face holds iff it is `1` at the all-`a` point. -/
def holds (g : DM m) : Prop := g.fn (Pt.allA m) = I.M4.one

theorem holds_iff (g : DM m) : g.holds ↔ ∀ p, g.fn p = I.M4.one := by
  refine ⟨fun h p => ?_, fun h => h _⟩
  obtain ⟨r, hr, hg⟩ := g.defn
  rw [holds, hg] at h
  rw [hg]
  have h' : r.eval (fun _ => a) = I.M4.one := by
    rw [← h]; apply Cof.eval_congr hr; intro n hn; simp [Pt.ext, hn, Pt.allA]
  exact Cof.eval_allA_eq_one h' _

theorem holds.restr {g : DM m} (h : g.holds) (f : Hom k m) : (g.restr f).holds :=
  (holds_iff _).2 fun _ => (holds_iff g).1 h _

/-- The Kleene reading of a face: the `K3`-points where it is `1`. -/
def face (g : DM m) : Set (Pt m) := {p | p.IsK3 ∧ g.fn p = I.M4.one}

theorem holds_iff_face (g : DM m) : g.holds ↔ Pt.allA m ∈ g.face :=
  ⟨fun h => ⟨Pt.allA_isK3 m, h⟩, fun h => h.2⟩

theorem holds_restr_iff_face (g : DM m) (f : Hom k m) :
    (g.restr f).holds ↔ f.app (Pt.allA k) ∈ g.face :=
  ⟨fun h => ⟨f.app_isK3 (Pt.allA_isK3 k), h⟩, fun h => h.2⟩

/-- Restriction depends only on the face. -/
theorem holds_restr_congr {g h : DM m} (e : g.face = h.face) (f : Hom k m) :
    (g.restr f).holds ↔ (h.restr f).holds := by
  rw [holds_restr_iff_face, holds_restr_iff_face, e]

end DM

namespace Hom

variable {k m n l : ℕ}

def id (m : ℕ) : Hom m m := fun j => DM.var j

/-- `f.comp g` is "first `g`, then `f`" on points: `(f.comp g).app = f.app ∘ g.app`. -/
def comp (f : Hom k m) (g : Hom n k) : Hom n m := fun j => (f j).restr g

@[simp] theorem app_id (p : Pt m) : (id m).app p = p := by funext j; simp [app, id]
@[simp] theorem app_comp (f : Hom k m) (g : Hom n k) (p : Pt n) :
    (f.comp g).app p = f.app (g.app p) := rfl

theorem ext_app {f g : Hom k m} (h : ∀ p, f.app p = g.app p) : f = g := by
  funext j; ext p; exact congrFun (h p) j

@[simp] theorem comp_id (f : Hom k m) : f.comp (id k) = f := ext_app fun p => by simp
@[simp] theorem id_comp (f : Hom k m) : (id m).comp f = f := ext_app fun p => by simp
theorem comp_assoc (f : Hom k m) (g : Hom n k) (h : Hom l n) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

end Hom

@[simp] theorem DM.restr_id {m : ℕ} (g : DM m) : g.restr (Hom.id m) = g := by ext p; simp
theorem DM.restr_restr {k m n : ℕ} (g : DM m) (f : Hom k m) (h : Hom n k) :
    (g.restr f).restr h = g.restr (f.comp h) := rfl

/-! ### Interval environments -/

/-- An interval environment at stage `m`: values for all interval variables. -/
abbrev IEnv (m : ℕ) := ℕ → DM m

namespace IEnv

variable {k m n : ℕ}

def restr (ρ : IEnv m) (f : Hom k m) : IEnv k := fun i => (ρ i).restr f

@[simp] theorem restr_id (ρ : IEnv m) : ρ.restr (Hom.id m) = ρ := by funext i; simp [restr]
theorem restr_restr (ρ : IEnv m) (f : Hom k m) (h : Hom n k) :
    (ρ.restr f).restr h = ρ.restr (f.comp h) := rfl

end IEnv

/-- Interpretation of an interval term. -/
def ival {m : ℕ} (ρ : IEnv m) (r : I) : DM m :=
  ⟨fun p => r.eval (fun n => (ρ n).fn p), by
    choose s hs hsρ using fun n => (ρ n).defn
    refine ⟨r.subst s, scoped_subst_all hs r, fun p => ?_⟩
    rw [Cof.eval_subst]; show I.eval (fun n => (ρ n).fn p) r = _
    congr 1; funext n; exact hsρ n p⟩

namespace ival

variable {k m : ℕ}

@[simp] theorem fn (ρ : IEnv m) (r : I) (p : Pt m) :
    (ival ρ r).fn p = r.eval (fun n => (ρ n).fn p) := rfl

theorem restr (ρ : IEnv m) (r : I) (f : Hom k m) : ival (ρ.restr f) r = (ival ρ r).restr f := rfl

theorem subst (ρ : IEnv m) (σ : ℕ → I) (r : I) :
    ival ρ (r.subst σ) = ival (fun n => ival ρ (σ n)) r := by
  ext p; simp [Cof.eval_subst]

theorem congr_eq {r s : I} (h : I.Eq r s) (ρ : IEnv m) : ival ρ r = ival ρ s := by
  ext p; exact h _

@[simp] theorem var (ρ : IEnv m) (i : ℕ) : ival ρ (.var i) = ρ i := rfl

end ival

/-! ### Cofibrations at a stage -/

theorem ival_isK3 {m : ℕ} (ρ : IEnv m) (r : I) {p : Pt m} (hp : p.IsK3) :
    M4.IsK3 ((ival ρ r).fn p) :=
  (ival ρ r).defn.isK3 hp

/-- The spec's entailment is sound at every stage. -/
theorem entails_holds {φ ψ : I} (h : I.Entails φ ψ) {m : ℕ} {ρ : IEnv m}
    (hφ : (ival ρ φ).holds) : (ival ρ ψ).holds :=
  Cof.entails_sound h (fun n => (ρ n).defn.isK3 (Pt.allA_isK3 m)) hφ

/-- Faces that entail each other have the same Kleene reading. -/
theorem entails_face {φ ψ : I} (h : I.Entails φ ψ) {m : ℕ} (ρ : IEnv m) :
    (ival ρ φ).face ⊆ (ival ρ ψ).face :=
  fun _ ⟨hp, hφ⟩ => ⟨hp, Cof.entails_sound h (fun n => (ρ n).defn.isK3 hp) hφ⟩

theorem face_eq_of_entails {φ ψ : I} (h₁ : I.Entails φ ψ) (h₂ : I.Entails ψ φ) {m : ℕ}
    (ρ : IEnv m) : (ival ρ φ).face = (ival ρ ψ).face :=
  Set.Subset.antisymm (entails_face h₁ ρ) (entails_face h₂ ρ)

/-- The true face is join-prime: this is what makes local character trivial. -/
theorem holds_or {m : ℕ} {ρ : IEnv m} {φ ψ : I} (h : (ival ρ (.or φ ψ)).holds) :
    (ival ρ φ).holds ∨ (ival ρ ψ).holds := by
  simp only [DM.holds, ival.fn, I.eval] at h ⊢
  exact (M4.join_eq_one_K3 (ival_isK3 ρ φ (Pt.allA_isK3 m))
    (ival_isK3 ρ ψ (Pt.allA_isK3 m))).1 h

theorem holds_and {m : ℕ} {ρ : IEnv m} {φ ψ : I} :
    (ival ρ (.and φ ψ)).holds ↔ (ival ρ φ).holds ∧ (ival ρ ψ).holds := by
  simp only [DM.holds, ival.fn, I.eval]; exact M4.meet_eq_one

theorem not_holds_zero {m : ℕ} {ρ : IEnv m} : ¬ (ival ρ .zero).holds := by
  simp [DM.holds, I.eval]

/-- If `Φ ⊨ (i = d)` then the interval environment sends `i` to the endpoint `d`. -/
theorem holds_lit {m : ℕ} {ρ : IEnv m} {i : ℕ} {d : Bool} (h : (ival ρ (I.lit i d)).holds) :
    ρ i = ival ρ (I.ofDir d) := by
  rw [DM.holds_iff] at h
  ext p; have hp := h p
  cases d <;> simp only [I.lit, I.ofDir, ival.fn, I.eval] at hp ⊢ <;>
    revert hp <;> cases (ρ i).fn p <;> decide

end Model

/-! ### Structural cube maps -/

namespace Model

namespace Hom

variable {k m n : ℕ}

/-- Weakening: forget the last variable. -/
def wk (m : ℕ) : Hom (m + 1) m := fun j => DM.var j.castSucc

/-- Extend a cube map by one more component. -/
def snoc (f : Hom k m) (r : DM k) : Hom k (m + 1) := Fin.snoc (α := fun _ => DM k) f r

/-- Lift a cube map under a fresh last variable. -/
def lift (f : Hom k m) : Hom (k + 1) (m + 1) := snoc (f.comp (wk k)) (DM.var (Fin.last k))

/-- Substitute `r` for the last variable. -/
def endpt (m : ℕ) (r : DM m) : Hom m (m + 1) := snoc (id m) r

@[simp] theorem app_wk (p : Pt (m + 1)) : (wk m).app p = Fin.init p := by
  funext j; simp [app, wk, Fin.init]

@[simp] theorem app_snoc (f : Hom k m) (r : DM k) (p : Pt k) :
    (snoc f r).app p = Fin.snoc (α := fun _ => M4) (f.app p) (r.fn p) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [app, snoc]

theorem wk_comp_snoc (f : Hom k m) (r : DM k) : (wk m).comp (snoc f r) = f :=
  ext_app fun p => by simp

theorem snoc_comp (f : Hom k m) (r : DM k) (g : Hom n k) :
    (snoc f r).comp g = snoc (f.comp g) (r.restr g) :=
  ext_app fun p => by simp

theorem wk_comp_lift (f : Hom k m) : (wk m).comp (lift f) = f.comp (wk k) := by
  simp [lift, wk_comp_snoc]

theorem lift_comp (f : Hom k m) (g : Hom n k) : (lift f).comp (lift g) = lift (f.comp g) :=
  ext_app fun p => by simp [lift]

@[simp] theorem lift_id : lift (id m) = id (m + 1) :=
  ext_app fun p => by funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [lift, Fin.init]

theorem lift_comp_endpt (f : Hom k m) (r : DM k) :
    (lift f).comp (endpt k r) = snoc f r :=
  ext_app fun p => by simp [lift, endpt, Fin.init]

theorem endpt_comp (r : DM m) (f : Hom k m) :
    (endpt m r).comp f = (lift f).comp (endpt k (r.restr f)) := by
  rw [lift_comp_endpt]; exact ext_app fun p => by simp [endpt]

@[simp] theorem wk_comp_endpt (r : DM m) : (wk m).comp (endpt m r) = id m := wk_comp_snoc _ _

end Hom

namespace IEnv

variable {k m : ℕ}

/-- Extend an interval environment by a fresh variable (de Bruijn index 0), at stage `m + 1`. -/
def ext (ρ : IEnv m) : IEnv (m + 1) := fun
  | 0 => DM.var (Fin.last m)
  | n + 1 => (ρ n).restr (Hom.wk m)

/-- Extend an interval environment by a value (de Bruijn index 0). -/
def cons (ρ : IEnv m) (r : DM m) : IEnv m := fun
  | 0 => r
  | n + 1 => ρ n

theorem ext_restr_lift (ρ : IEnv m) (f : Hom k m) : ρ.ext.restr (Hom.lift f) = (ρ.restr f).ext := by
  funext n; cases n with
  | zero => ext p; simp [ext, restr, Hom.lift, Hom.app, Hom.snoc]
  | succ n => simp only [ext, restr, DM.restr_restr, Hom.wk_comp_lift]

theorem ext_restr_endpt (ρ : IEnv m) (r : DM m) : ρ.ext.restr (Hom.endpt m r) = ρ.cons r := by
  funext n; cases n with
  | zero => ext p; simp [ext, restr, cons, Hom.endpt, Hom.app, Hom.snoc]
  | succ n => simp [ext, restr, cons, DM.restr_restr]

theorem cons_restr (ρ : IEnv m) (r : DM m) (f : Hom k m) :
    (ρ.cons r).restr f = (ρ.restr f).cons (r.restr f) := by
  funext n; cases n <;> rfl

end IEnv

end Model
