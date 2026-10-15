import KubusCore.Syntax

/-!
# Simple boundary normal forms

Normalize a boundary after substituting the endpoints of one consistent DNF face. Constructor arguments are normalized before a constructor's first holding boundary is evaluated; the boundary schema only calls earlier constructors. Normalized arguments are values of this evaluator, so substituting a recursive argument does not restart normalization at a larger constructor index.
-/

namespace KubusCore.Boundary

/-- The substitution determined by a conjunction of endpoint literals. -/
def faceSub : I.Face → Nat → I
  | [], i => .var i
  | (j, e) :: α, i => if i = j then I.ofDir e else faceSub α i

mutual
/-- Evaluate a simple boundary in an algebra of constructors. Parameters are fixed by the algebra. -/
def eval (conF : Nat → List Tm → List I → Tm) (σ : Nat → Tm) (τ : Nat → I) : Tm → Tm
  | .var j => σ j
  | .con _ c _ as rs => conF c (evalArgs conF σ τ as) (rs.map (·.subst τ))
  | _ => .abort
def evalArgs (conF : Nat → List Tm → List I → Tm) (σ : Nat → Tm) (τ : Nat → I) : Tm → List Tm
  | .tcons a as => eval conF σ τ a :: evalArgs conF σ τ as
  | _ => []
end

/-- Normalize a constructor applied to already normalized arguments. Only earlier constructors occur in its boundary schemas. -/
def conNF (ctors : List Ctor) (d : Nat) (ps : Tm) (c : Nat) (as : List Tm) (rs : List I) : Tm :=
  let C := ctors.getD c default
  match C.bnd.find? (fun p => I.entails .one (p.1.subst fun i => rs.reverse.getD i .zero)) with
  | none => .con d c ps (Tm.ofList as) rs
  | some (_, b) => eval
      (fun c' xs ss => if _ : c' < c then conNF ctors d ps c' xs ss else .abort)
      (fun j => as.reverse.getD j .abort)
      (fun i => rs.reverse.getD i .zero) b
termination_by c
decreasing_by assumption

/-- The boundary normal form on a single face, in the original constructor's argument context. -/
def nf (ctors : List Ctor) (d np n c : Nat) (α : I.Face) (b : Tm) : Tm :=
  eval (fun c' xs ss => if c' < c then conNF ctors d (Ctor.paramVars np n) c' xs ss else .abort)
    Tm.var (faceSub α) b

/-- Equality of constructor trees up to equality of interval arguments in the free De Morgan algebra. -/
def INear : List I → List I → Prop
  | [], [] => True
  | r :: rs, s :: ss => I.Eq r s ∧ INear rs ss
  | _, _ => False

def Near : Tm → Tm → Prop
  | .var x, .var y => x = y
  | .tnil, .tnil => True
  | .tcons a as, .tcons b bs => Near a b ∧ Near as bs
  | .con d c ps as rs, .con d' c' ps' bs ss =>
      d = d' ∧ c = c' ∧ ps = ps' ∧ Near as bs ∧ INear rs ss
  | _, _ => False

/-- Boundary agreement is checked on each consistent DNF face of the overlap separately. -/
def Agree (ctors : List Ctor) (d np n c : Nat) (φ : I) (b b' : Tm) : Prop :=
  ∀ α ∈ φ.faces, Near (nf ctors d np n c α b) (nf ctors d np n c α b')

end KubusCore.Boundary
