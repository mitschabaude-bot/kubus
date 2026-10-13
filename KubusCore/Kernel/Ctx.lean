import KubusCore.Kernel.Lemmas

/-!
# Kernel contexts

A kernel context for `Ψ; Φ; Γ` carries the universe level of every variable's type and of
every constant's type, with derivations that these types are well-formed, so that types
obtained from variables and constants can be decomposed by the inversion rules.
-/

namespace KubusCore

/-- Levels of the types of the signature's constants, with closedness and typing in the
empty context. -/
structure SigInfo (S : Sig) where
  lv : List Nat
  closed : ∀ (k : Nat) (t A : Tm), S[k]? = some (.defn t A) → k < lv.length → A.closedB 0 0 = true
  ok : ∀ (k : Nat) (t A : Tm) (l : Nat), S[k]? = some (.defn t A) → lv[k]? = some l → HasTy S 0 .one [] A (.univ l)

namespace Kernel

/-! ## Canonical restrictions

Each kernel call first replaces the restriction `Φ` by its canonical form `Φ'` (the
disjunction of its maximal faces), checking `Φ ⊨ Φ'` and `Φ' ⊨ Φ`, and moves the results
back with the restriction rule. This keeps `Φ` small under nested systems. -/

/-- `d ⊆ c` as constraint sets: the face `c` lies in the face `d`. -/
def faceLe (d c : I.Face) : Bool := d.all (c.contains ·)

/-- The maximal faces of a list of faces. -/
def maxFaces (fs : List I.Face) : List I.Face :=
  (fs.foldl (fun acc c =>
    if acc.any (fun d => faceLe d c) then acc else c :: acc.filter (fun d => !faceLe c d)) []).reverse

def litLt (a b : Nat × Bool) : Bool := a.1 < b.1 || (a.1 == b.1 && !a.2 && b.2)

/-- A face with sorted, distinct literals. -/
def normFace (α : I.Face) : I.Face := (α.mergeSort fun a b => !litLt b a).eraseDups

/-- Proofs that `Φ'` is equivalent to `Φ`. -/
structure Equiv' (Ψ : Nat) (Φ Φ' : I) : Type where
  hs : Φ'.Scoped Ψ
  h1 : I.Entails Φ' Φ
  h2 : I.Entails Φ Φ'

/-- A literal `i` or `~i`, and its sort key. -/
def litKey : I → Option Nat
  | .var i => some (2 * i + 1)
  | .neg (.var i) => some (2 * i)
  | _ => none

/-- A conjunction of literals with strictly increasing keys, ending in `1`. -/
def faceShape (bound : Nat) : I → Bool
  | .one => true
  | .and l r => match litKey l with
    | some k => decide (bound ≤ k) && faceShape (k + 1) r
    | none => false
  | _ => false

/-- Already in the form produced by `canonPhi` (up to absorption): a disjunction of such
faces ending in `0`. Only a shortcut; the canonical form is not needed for soundness. -/
def canonShape : I → Bool
  | .zero => true
  | .or f r => faceShape 0 f && canonShape r
  | _ => false

theorem dnf_ofFace (α : I.Face) : I.dnf true (I.ofFace α) = [α] := by
  induction α with
  | nil => rfl
  | cons a α ih =>
    obtain ⟨i, b⟩ := a
    cases b <;> simp [I.ofFace, I.lit, I.dnf] at ih ⊢ <;> simp [ih]

theorem faces_ofFaces (cs : List I.Face) : (I.ofFaces cs).faces = cs.filter I.Face.consistent := by
  have : I.dnf true (I.ofFaces cs) = cs := by
    induction cs with
    | nil => rfl
    | cons α cs ih =>
      simp only [I.ofFaces, List.foldr_cons, I.dnf] at ih ⊢
      rw [dnf_ofFace, ih]; rfl
  simp only [I.faces, this]

/-- The canonical form of `Φ`, given its faces `fs`, if it differs from `Φ`. -/
def canonOf (Ψ : Nat) (Φ : I) (fs : List I.Face) (hfs : fs = Φ.faces) :
    Option ((Φ' : I) × Equiv' Ψ Φ Φ') :=
  if canonShape Φ then none else
  let gs := (maxFaces fs).map normFace
  let Φ' := I.ofFaces gs
  if Φ' = Φ then none else
  if hs : Φ'.Scoped Ψ then
    if h1 : ((gs.filter I.Face.consistent).all fun c => fs.any fun d => d.all (c.contains ·)) = true then
      if h2 : (fs.all fun c => (gs.filter I.Face.consistent).any fun d => d.all (c.contains ·)) = true then
        some ⟨Φ', hs, by
          show I.entails (I.ofFaces gs) Φ = true
          unfold I.entails; rw [faces_ofFaces, ← hfs]; exact h1, by
          show I.entails Φ (I.ofFaces gs) = true
          unfold I.entails; rw [faces_ofFaces, ← hfs]; exact h2⟩
      else none
    else none
  else none

end Kernel

structure KCtx (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) where
  sig : SigInfo S
  /-- the restriction is known to be in canonical form (a hint only: it lets the kernel skip
  canonicalizing it again) -/
  canon : Bool := false
  /-- the faces of the restriction, computed once -/
  fs : Thunk (List I.Face)
  hfs : fs.get = Φ.faces
  /-- the canonical form of the restriction, computed once (`none`: keep `Φ`) -/
  cn : Thunk (Option ((Φ' : I) × Kernel.Equiv' Ψ Φ Φ'))
  lv : List Nat
  wf : Wf S Ψ Φ Γ
  hsc : Φ.Scoped Ψ
  varOk : ∀ (x : Nat) (A : Tm) (l : Nat), Γ.lookup x = some A → lv[x]? = some l → HasTy S Ψ Φ Γ A (.univ l)
  constOk : ∀ (k : Nat) (t A : Tm) (l : Nat), S[k]? = some (.defn t A) → sig.lv[k]? = some l → HasTy S Ψ Φ Γ A (.univ l)

namespace KCtx

variable {S : Sig}

def root (sig : SigInfo S) : KCtx S 0 .one [] where
  sig := sig
  fs := Thunk.mk fun _ => I.faces .one
  hfs := rfl
  cn := Thunk.pure none
  lv := []
  wf := Wf.nil trivial
  hsc := trivial
  varOk := fun x A l h _ => by simp [Ctx.lookup] at h
  constOk := sig.ok

theorem lt_of_getElem? {l : List Nat} {k n : Nat} (h : l[k]? = some n) : k < l.length := by
  exact (List.getElem?_eq_some_iff.mp h).1

/-- Extend by a term variable of type `A`. -/
def ext {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) :
    KCtx S Ψ Φ (A :: Γ) where
  sig := E.sig
  canon := E.canon
  fs := E.fs
  hfs := E.hfs
  cn := E.cn
  lv := l :: E.lv
  wf := Wf.cons hA
  hsc := E.hsc
  varOk := by
    intro x B l' hx hl
    cases x with
    | zero =>
      simp [Ctx.lookup] at hx; simp at hl
      subst hx; subst hl
      exact HasTy.wk hA hA
    | succ x =>
      rw [Ctx.lookup_cons_succ] at hx
      simp only [List.getElem?_cons_succ] at hl
      cases h : Γ.lookup x with
      | none => rw [h] at hx; cases hx
      | some B' =>
        rw [h] at hx; simp at hx; subst hx
        exact HasTy.wk hA (E.varOk x B' l' h hl)
  constOk := by
    intro k t B l' hk hl
    have hc := E.sig.closed k t B hk (lt_of_getElem? hl)
    have := HasTy.wk hA (E.constOk k t B l' hk hl)
    rw [Tm.shift_closed hc] at this
    exact this

/-- Extend by an interval variable. -/
def dext {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : KCtx S (Ψ + 1) Φ.shift Γ.dshift :=
  let fs : Thunk (List I.Face) := Thunk.mk fun _ => Φ.shift.faces
  { sig := E.sig
    canon := E.canon
    fs := fs
    hfs := rfl
    cn := Thunk.mk fun _ => Kernel.canonOf (Ψ + 1) Φ.shift fs.get rfl
    lv := E.lv
    wf := E.wf.dwk E.hsc
    hsc := I.scoped_shift E.hsc
    varOk := by
      intro x B l hx hl
      rw [Ctx.lookup_dshift] at hx
      cases h : Γ.lookup x with
      | none => rw [h] at hx; cases hx
      | some B' =>
        rw [h] at hx; simp at hx; subst hx
        exact HasTy.dwk (E.varOk x B' l h hl)
    constOk := by
      intro k t B l hk hl
      have hc := E.sig.closed k t B hk (lt_of_getElem? hl)
      have := HasTy.dwk (E.constOk k t B l hk hl)
      rw [Tm.dshift_closed hc] at this
      exact this }

/-- Strengthen the restriction to `Φ'` with `Φ' ⊨ Φ`. -/
def restrict {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (Φ' : I) (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    KCtx S Ψ Φ' Γ :=
  let fs : Thunk (List I.Face) := Thunk.mk fun _ => Φ'.faces
  { sig := E.sig
    fs := fs
    hfs := rfl
    cn := Thunk.mk fun _ => Kernel.canonOf Ψ Φ' fs.get rfl
    lv := E.lv
    wf := E.wf.restrict hs he
    hsc := hs
    varOk := fun x A l hx hl => HasTy.restrict hs he (E.varOk x A l hx hl)
    constOk := fun k t A l hk hl => HasTy.restrict hs he (E.constOk k t A l hk hl) }

/-- `Φ ⊨ ψ`, decided with the cached faces of `Φ`. -/
def ent {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ψ : I) : Bool :=
  E.fs.get.all fun c => ψ.faces.any fun d => d.all (c.contains ·)

theorem ent_eq {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ψ : I) : E.ent ψ = I.entails Φ ψ := by
  simp only [ent, E.hfs]; rfl

theorem ent_sound {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) {ψ : I} (h : E.ent ψ = true) : I.Entails Φ ψ := by
  rw [ent_eq] at h; exact h

/-- `Φ ⊨ ψ`, decided with the cached faces. -/
def Ent {Ψ Φ Γ} (_E : KCtx S Ψ Φ Γ) (ψ : I) : Prop := I.Entails Φ ψ

instance {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ψ : I) : Decidable (E.Ent ψ) :=
  decidable_of_iff (E.ent ψ = true) ⟨E.ent_sound, fun h => by rw [ent_eq]; exact h⟩

end KCtx

end KubusCore
