import Model.Cube

/-!
# Computing with cube maps

Simp lemmas for the action of structural cube maps on points, used to prove identities between
cube maps (`Hom.ext_app`) and interval values (`DM.ext`).
-/

set_option autoImplicit false

namespace Model

open KubusCore

namespace Hom

variable {k m n : ℕ}

@[simp] theorem app_lift (f : Hom k m) (p : Pt (k + 1)) :
    (lift f).app p = Fin.snoc (α := fun _ => M4) (f.app (Fin.init p)) (p (Fin.last k)) := by
  simp [lift]

@[simp] theorem app_endpt (r : DM m) (p : Pt m) :
    (endpt m r).app p = Fin.snoc (α := fun _ => M4) p (r.fn p) := by
  simp [endpt]

theorem ext_snoc {f g : Hom k (m + 1)}
    (h1 : ∀ p, Fin.init (f.app p) = Fin.init (g.app p))
    (h2 : ∀ p, f.app p (Fin.last m) = g.app p (Fin.last m)) : f = g :=
  ext_app fun p => by
    funext j; refine Fin.lastCases (h2 p) (fun j => ?_) j
    exact congrFun (h1 p) j

@[simp] theorem init_apply' {α : Type} {m : ℕ} (p : Fin (m + 1) → α) (i : Fin m) :
    Fin.init (α := fun _ => α) p i = p i.castSucc := rfl

@[simp] theorem init_snoc' {α : Type} {m : ℕ} (p : Fin m → α) (x : α) :
    Fin.init (Fin.snoc (α := fun _ => α) p x) = p := Fin.init_snoc _ _

end Hom

end Model

namespace Model

namespace Hom

variable {k m n n' n'' : ℕ}

theorem lift_comp_endpt' (g : Hom n' n) (r : DM n') : (lift g).comp (endpt n' r) = snoc g r :=
  lift_comp_endpt g r

theorem snoc_comp_snoc_wk (g : Hom n' n) (x : DM (n' + 1)) (h : Hom n'' (n' + 1)) (r : DM n'') :
    (snoc (g.comp (wk n')) x).comp h = snoc (g.comp ((wk n').comp h)) (x.restr h) := by
  rw [snoc_comp]; rfl

end Hom

namespace DM

variable {m : ℕ}

theorem eq_one_of_holds {r : DM m} (h : r.holds) : r = one m := by
  ext p; exact (holds_iff r).1 h p

@[simp] theorem max_one_left (r : DM m) : max (one m) r = one m := by ext p; simp
@[simp] theorem max_one_right (r : DM m) : max r (one m) = one m := by ext p; simp
@[simp] theorem max_zero_left (r : DM m) : max (zero m) r = r := by ext p; simp
@[simp] theorem max_zero_right (r : DM m) : max r (zero m) = r := by ext p; simp
@[simp] theorem neg_zero' : neg (zero m) = one m := by ext p; simp
@[simp] theorem neg_one' : neg (one m) = zero m := by ext p; simp
@[simp] theorem neg_neg' (r : DM m) : neg (neg r) = r := by ext p; simp

end DM

namespace Cof

variable {m : ℕ}

@[simp] theorem eq1_zero : eq1 (DM.zero m) = bot m := by
  ext p; simp [eq1, bot, DM.face]

@[simp] theorem eq1_one : eq1 (DM.one m) = top m := by
  ext p; simp [eq1, top, DM.face]

theorem or_bot (φ : Cof m) : Cof.or φ (bot m) = φ := by ext p; simp [Cof.or, bot]

end Cof

end Model
