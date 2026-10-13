import KubusCore.Kernel.Conv

/-!
# Kernel: entry points

`Kernel.rec S n` ties the knot of the mutually recursive kernel functions with fuel `n`
(the nesting depth of recursive calls). `checkSig S` checks a signature and returns a proof
of `WfSig S`; `CheckedSig.extend` checks one more definition against a checked signature.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-! ## Canonical restrictions

Each kernel call first replaces the restriction `Φ` by its canonical form `Φ'` (the
disjunction of its maximal faces), checking `Φ ⊨ Φ'` and `Φ' ⊨ Φ`, and moves the results
back with the restriction rule. This keeps `Φ` small under nested systems. -/

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

def canonical (Ψ : Nat) (Φ : I) : Option ((Φ' : I) × Equiv' Ψ Φ Φ') :=
  if canonShape Φ then none else
  let Φ' := canonPhi Φ
  if Φ' = Φ then none else
  if hs : Φ'.Scoped Ψ then
    if h1 : I.Entails Φ' Φ then
      if h2 : I.Entails Φ Φ' then some ⟨Φ', hs, h1, h2⟩ else none
    else none
  else none

variable {Ψ : Nat} {Φ : I} {Γ : Ctx}

def canonInfer (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) : K (Inf S Ψ Φ Γ t) :=
  match (if E.canon then none else canonical Ψ Φ) with
  | none => inferStep R { E with canon := true } t
  | some ⟨Φ', q⟩ => do
    let i ← inferStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t
    pure ⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩

def canonCheck (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (PLift (HasTy S Ψ Φ Γ t A)) :=
  match (if E.canon then none else canonical Ψ Φ) with
  | none => checkStep R { E with canon := true } t A l hA
  | some ⟨Φ', q⟩ => do
    let ⟨h⟩ ← checkStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t A l (HasTy.restrict q.hs q.h1 hA)
    pure ⟨HasTy.restrict E.hsc q.h2 h⟩

def canonWhnf (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K (Red S Ψ Φ Γ t A) :=
  match (if E.canon then none else canonical Ψ Φ) with
  | none => whnfMain R { E with canon := true } t A l hA ht
  | some ⟨Φ', q⟩ => do
    let r ← whnfMain R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t A l (HasTy.restrict q.hs q.h1 hA)
      (HasTy.restrict q.hs q.h1 ht)
    pure ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩

def canonWhnfI (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) :=
  match (if E.canon then none else canonical Ψ Φ) with
  | none => whnfIStep R { E with canon := true } t
  | some ⟨Φ', q⟩ => do
    let ⟨i, r⟩ ← whnfIStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩⟩

def canonConv (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm) (ht : HasTy S Ψ Φ Γ t A)
    (hu : HasTy S Ψ Φ Γ u A) : K (PLift (EqTm S Ψ Φ Γ t u A)) :=
  if h : t = u then pure ⟨h ▸ EqTm.refl ht⟩ else
  match (if E.canon then none else canonical Ψ Φ) with
  | none => convStep R { E with canon := true } A l hA t u ht hu
  | some ⟨Φ', q⟩ => do
    let ⟨e⟩ ← convStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) A l (HasTy.restrict q.hs q.h1 hA) t u
      (HasTy.restrict q.hs q.h1 ht) (HasTy.restrict q.hs q.h1 hu)
    pure ⟨EqTm.restrict E.hsc q.h2 e⟩

def canonConvNe (R : Rec S) (E : KCtx S Ψ Φ Γ) (t u : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty)) :=
  match (if E.canon then none else canonical Ψ Φ) with
  | none => convNeStep R { E with canon := true } t u
  | some ⟨Φ', q⟩ => do
    let ⟨i, ⟨e⟩⟩ ← convNeStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t u
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨EqTm.restrict E.hsc q.h2 e⟩⟩

/-- The kernel with `n` levels of nested recursive calls. Each level is built lazily. -/
def rec (S : Sig) : Nat → Rec S
  | 0 => Rec.bot S
  | n + 1 =>
    { infer := fun E t => canonInfer (rec S n) E t
      check := fun E t A l hA => canonCheck (rec S n) E t A l hA
      whnf := fun E t A l hA ht => canonWhnf (rec S n) E t A l hA ht
      whnfI := fun E t => canonWhnfI (rec S n) E t
      conv := fun E A l hA t u ht hu => canonConv (rec S n) E A l hA t u ht hu
      convNe := fun E t u => canonConvNe (rec S n) E t u }

/-- Default nesting depth. -/
def defaultFuel : Nat := 20000

/-! ## Signatures -/

/-- Add the level of the next constant's type to the signature information. -/
def SigInfo.next (R : Rec S) (si : SigInfo S) : K (Option (SigInfo S)) :=
  match h : S[si.lv.length]? with
  | none => pure none
  | some (.data _) =>
    -- inductive types are not supported by the kernel yet: a placeholder level, never used
    pure (some
      { lv := si.lv ++ [0]
        closed := by
          intro k t A' hk hlt
          simp only [List.length_append, List.length_singleton] at hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact si.closed k t A' hk hlt
          · subst heq; rw [h] at hk; cases hk
        ok := by
          intro k t A' l' hk hl
          have hlt := KCtx.lt_of_getElem? hl
          simp only [List.length_append, List.length_singleton] at hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · rw [List.getElem?_append_left hlt] at hl
            exact si.ok k t A' l' hk hl
          · subst heq; rw [h] at hk; cases hk })
  | some (.defn b A) =>
    if hc : A.closedB 0 0 = true then do
      let ⟨l, ⟨hA⟩⟩ ← inferType R (KCtx.root si) A
      pure (some
        { lv := si.lv ++ [l]
          closed := by
            intro k t A' hk hlt
            simp only [List.length_append, List.length_singleton] at hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
            · exact si.closed k t A' hk hlt
            · subst heq; rw [h] at hk; cases hk; exact hc
          ok := by
            intro k t A' l' hk hl
            have hlt := KCtx.lt_of_getElem? hl
            simp only [List.length_append, List.length_singleton] at hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
            · rw [List.getElem?_append_left hlt] at hl
              exact si.ok k t A' l' hk hl
            · subst heq; rw [h] at hk; cases hk
              rw [List.getElem?_append_right (Nat.le_refl _)] at hl
              simp at hl; subst hl; exact hA })
    else fail s!"kernel: the type of constant c{si.lv.length} is not closed"

def SigInfo.empty (S : Sig) : SigInfo S where
  lv := []
  closed := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  ok := fun _ _ _ _ _ h => by simp at h

/-- Levels of all constant types of `S`. -/
def SigInfo.build (R : Rec S) : Nat → SigInfo S → K (SigInfo S)
  | 0, si => pure si
  | n + 1, si => do
    match ← SigInfo.next R si with
    | none => pure si
    | some si' => SigInfo.build R n si'

/-- The kernel and the empty context for the signature `S`. -/
def setup (S : Sig) (fuel : Nat := defaultFuel) : K (Rec S × KCtx S 0 .one []) := do
  let R := rec S fuel
  let si ← SigInfo.build R S.length (SigInfo.empty S)
  pure (R, KCtx.root si)

/-- Check one definition `(t, A)` against the signature `S`. -/
def checkEntry (S : Sig) (t A : Tm) (fuel : Nat := defaultFuel) :
    K (PLift (t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A)) := do
  let (R, E) ← setup S fuel
  let ⟨l, ⟨hA⟩⟩ ← inferType R E A
  let ⟨ht⟩ ← R.check E t A l hA
  if hc : t.closedB 0 0 = true ∧ A.closedB 0 0 = true then
    pure ⟨hc.1, hc.2, ⟨l, hA⟩, ht⟩
  else fail "kernel: the definition is not closed"

theorem wfSig_append {S : Sig} {t A : Tm} (hS : WfSig S)
    (h : t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A) :
    WfSig (S ++ [.defn t A]) := by
  refine ⟨?_, ?_⟩
  · intro k t' A' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.1 k t' A' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      have hk0 : k - S.length = 0 := by
        cases h' : k - S.length with
        | zero => rfl
        | succ n => rw [h'] at hk; simp at hk
      have hkeq : k = S.length := by omega
      subst hkeq
      simp at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [List.take_left' rfl]
      exact h
  · intro k D hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.2 k D hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      cases h' : k - S.length with
      | zero => rw [h'] at hk; simp at hk
      | succ n => rw [h'] at hk; simp at hk

theorem wfSig_appendData {S : Sig} {D : DataDecl} (hS : WfSig S)
    (h : D.Wf S S.length) : WfSig (S ++ [.data D]) := by
  refine ⟨?_, ?_⟩
  · intro k t' A' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.1 k t' A' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      cases h' : k - S.length with
      | zero => rw [h'] at hk; simp at hk
      | succ n => rw [h'] at hk; simp at hk
  · intro k D' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.2 k D' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      have hk0 : k - S.length = 0 := by
        cases h' : k - S.length with
        | zero => rfl
        | succ n => rw [h'] at hk; simp at hk
      have hkeq : k = S.length := by omega
      subst hkeq
      simp at hk
      subst hk
      rw [List.take_left' rfl]
      exact h

/-! ## Data declarations -/

section
variable {S : Sig}

/-- The context of the parameters and the arguments before argument `k`. -/
def argCtxK (R : Rec S) (E0 : KCtx S 0 .one []) (D : DataDecl) (d : Nat) (C : Ctor) (k : Nat) :
    K (KCtx S 0 .one (D.argCtx d C k)) := do
  let E1 ← extTypes R E0 D.params
  let E2 ← extTypes R E1 ((List.range k).map (C.argTy d D.params.length))
  if h : ((List.range k).map (C.argTy d D.params.length)).reverse ++ (D.params.reverse ++ []) =
      D.argCtx d C k then pure (castCtx E2 rfl h)
  else fail "kernel: argument context mismatch"

/-- The same context at `Ψ = m` interval variables, restricted to `ψ`. -/
def bndCtxK (E : KCtx S 0 .one Γ) (m : Nat) (ψ : I) : K (KCtx S m ψ Γ) := do
  let E1 := E.dextN m
  if h : shiftIN m .one = .one ∧ dshiftN m Γ = Γ then
    let E2 : KCtx S (0 + m) .one Γ := castCtx E1 h.1 h.2
    let E3 : KCtx S m .one Γ := Nat.zero_add m ▸ E2
    let ⟨hψ⟩ ← ensureScoped ψ m
    pure (E3.restrict ψ hψ (I.entails_one ψ))
  else fail "kernel: boundary context mismatch"

/-! ### Typing of boundary arguments -/

mutual
def checkBndTyped (R : Rec S) {m ψ Γ} (E : KCtx S m ψ Γ) (lvl : Nat) (ctors : List Ctor) (d np : Nat) :
    (t : Tm) → K (PLift (Ctor.bndTyped S m ψ Γ lvl ctors d np t))
  | .con d' c' ps as rs =>
    match getIdx' ctors c' with
    | .inl ⟨C', ⟨h⟩⟩ => do
      let ⟨p⟩ ← checkBndTypedArgs R E lvl ctors d np C' ps 0 [] as
      pure ⟨by simp only [Ctor.bndTyped, h]; exact p⟩
    | .inr ⟨h⟩ => pure ⟨by simp only [Ctor.bndTyped, h]⟩
  | .var .. | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .tcons .. | .data .. | .elim .. =>
    pure ⟨by simp [Ctor.bndTyped]⟩
def checkBndTypedArgs (R : Rec S) {m ψ Γ} (E : KCtx S m ψ Γ) (lvl : Nat) (ctors : List Ctor) (d np : Nat)
    (C' : Ctor) (ps : Tm) (k : Nat) (prev : List Tm) :
    (t : Tm) → K (PLift (Ctor.bndTypedArgs S m ψ Γ lvl ctors d np C' ps k prev t))
  | .tcons a as => do
    let ⟨h1⟩ ← checkBndVar R E lvl d np C' ps k prev a
    let ⟨h2⟩ ← if hr : C'.isRec k = true then do
        let ⟨h⟩ ← checkBndTyped R E lvl ctors d np a
        pure (PLift.up (fun _ => h))
      else pure (PLift.up (fun h => absurd h hr))
    let ⟨h3⟩ ← checkBndTypedArgs R E lvl ctors d np C' ps (k + 1) (a :: prev) as
    pure ⟨by simp only [Ctor.bndTypedArgs]; exact ⟨h1, h2, h3⟩⟩
  | .var .. | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .con .. | .data .. | .elim .. =>
    pure ⟨by simp [Ctor.bndTypedArgs]⟩
/-- A point argument variable of a nested constructor has the argument type. -/
def checkBndVar (R : Rec S) {m ψ Γ} (E : KCtx S m ψ Γ) (lvl d np : Nat) (C' : Ctor) (ps : Tm)
    (k : Nat) (prev : List Tm) (a : Tm) :
    K (PLift (∀ (j : Nat) (T : Tm), a = .var j → C'.isRec k = false → Γ.lookup j = some T →
      EqTm S m ψ Γ T ((C'.argTy d np k).substList (prev ++ ps.toList.reverse)) (.univ lvl))) :=
  match a with
  | .var j =>
    if hr : C'.isRec k = false then
      match hT : Γ.lookup j with
      | some T => do
        let A' := (C'.argTy d np k).substList (prev ++ ps.toList.reverse)
        let ⟨h1⟩ ← checkType R E T lvl
        let ⟨h2⟩ ← checkType R E A' lvl
        let ⟨hU⟩ ← univTyK E lvl
        let ⟨e⟩ ← R.conv E (.univ lvl) (lvl + 1) hU T A' h1 h2
        pure ⟨fun j' T' hj _ hT' => by cases hj; rw [hT] at hT'; cases hT'; exact e⟩
      | none => pure ⟨fun j' T' hj _ hT' => by cases hj; rw [hT] at hT'; cases hT'⟩
    else pure ⟨fun _ _ _ h => absurd h hr⟩
  | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .tcons .. | .con .. | .data .. | .elim .. =>
    pure ⟨fun _ _ h => by cases h⟩
end

/-- Check constructor `c` against the declaration truncated to the constructors before it. -/
def checkCtor (S : Sig) (d : Nat) (D : DataDecl) (c : Nat) (C : Ctor) :
    let Sc := S ++ [.data (D.truncate c)]
    K (PLift ((∀ (k : Nat) (A : Tm), C.args[k]? = some (.point A) → A.closedB (D.params.length + k) 0 = true ∧
        A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
        HasTy (S ++ [.data (D.truncate 0)]) 0 .one (D.argCtx d C k) A (.univ D.level)) ∧
      (∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) → ψ.Scoped C.dims ∧
        b.closedB (D.params.length + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d D.params.length c C.args.length C b = true ∧
        HasTy Sc C.dims ψ (D.argCtx d C C.args.length) b (.data d (Ctor.paramVars D.params.length C.args.length)) ∧
        Ctor.bndTyped Sc C.dims ψ (D.argCtx d C C.args.length) D.level D.ctors d D.params.length b) ∧
      (∀ (k k' : Nat) (ψ ψ' : I) (b b' : Tm), C.bnd[k]? = some (ψ, b) → C.bnd[k']? = some (ψ', b') →
        EqTm Sc C.dims (.and ψ ψ') (D.argCtx d C C.args.length) b b'
          (.data d (Ctor.paramVars D.params.length C.args.length))))) := do
  let Sc := S ++ [.data (D.truncate c)]
  let np := D.params.length
  let (R, E0) ← setup Sc
  let (R0, E00) ← setup (S ++ [.data (D.truncate 0)])

    let ⟨hargs⟩ ← forallElems C.args (fun k a => ∀ A, a = .point A → A.closedB (np + k) 0 = true ∧
        A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
        HasTy (S ++ [.data (D.truncate 0)]) 0 .one (D.argCtx d C k) A (.univ D.level)) fun k a _ =>
      match a with
      | .point A => do
        let Ek ← argCtxK R0 E00 D d C k
        let ⟨hA⟩ ← checkType R0 Ek A D.level
        if hc : A.closedB (np + k) 0 = true ∧ A.mentionsData d = false ∧ C.noRecDeps k A = true then
          pure ⟨fun A' hA' => by cases hA'; exact ⟨hc.1, hc.2.1, hc.2.2, hA⟩⟩
        else fail "kernel: argument type not closed, mentions the type or an earlier recursive argument"
      | .recur => pure ⟨fun _ h => by cases h⟩
    let En ← argCtxK R E0 D d C C.args.length
    let T : Tm := .data d (Ctor.paramVars np C.args.length)
    let ⟨hb⟩ ← forallElems C.bnd (fun _ pb => pb.1.Scoped C.dims ∧
        pb.2.closedB (np + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d np c C.args.length C pb.2 = true ∧
        HasTy Sc C.dims pb.1 (D.argCtx d C C.args.length) pb.2 T ∧
        Ctor.bndTyped Sc C.dims pb.1 (D.argCtx d C C.args.length) D.level D.ctors d np pb.2)
        fun _ pb _ => do
      let Eb ← bndCtxK En C.dims pb.1
      let ⟨hψ⟩ ← ensureScoped pb.1 C.dims
      let ⟨l, ⟨hT⟩⟩ ← inferType R Eb T
      let ⟨h⟩ ← R.check Eb pb.2 T l hT
      let ⟨hty⟩ ← checkBndTyped R Eb D.level D.ctors d np pb.2
      if hc : pb.2.closedB (np + C.args.length) C.dims = true ∧
          Ctor.simpleB D.ctors d np c C.args.length C pb.2 = true then pure ⟨hψ, hc.1, hc.2, h, hty⟩
      else fail "kernel: boundary not closed or not simple"
    let ⟨hagree⟩ ← forallElems C.bnd (fun k pb => ∀ (k' : Nat) (ψ' : I) (b' : Tm), C.bnd[k']? = some (ψ', b') →
        EqTm Sc C.dims (.and pb.1 ψ') (D.argCtx d C C.args.length) pb.2 b' T) fun k pb hk => do
      let ⟨h⟩ ← forallElems C.bnd (fun _ pb' => EqTm Sc C.dims (.and pb.1 pb'.1)
          (D.argCtx d C C.args.length) pb.2 pb'.2 T) fun k' pb' hk' => do
        let Eb ← bndCtxK En C.dims (.and pb.1 pb'.1)
        let ⟨l, ⟨hT⟩⟩ ← inferType R Eb T
        let ⟨h1⟩ ← R.check Eb pb.2 T l hT
        let ⟨h2⟩ ← R.check Eb pb'.2 T l hT
        R.conv Eb T l hT _ _ h1 h2
      pure ⟨fun k' ψ' b' hk' => h k' (ψ', b') hk'⟩
    pure ⟨fun k A hk => hargs k (.point A) hk A rfl,
      fun k ψ b hk => hb k (ψ, b) hk,
      fun k k' ψ ψ' b b' hk hk' => hagree k (ψ, b) hk k' ψ' b' hk'⟩


def checkData (S : Sig) (d : Nat) (D : DataDecl) : K (PLift (D.Wf S d)) := do
  let np := D.params.length
  let (R, E0) ← setup S
  let ⟨hl⟩ ← ensureLvl (D.level + 1)
  let ⟨hps⟩ ← forallElems D.params (fun j A => A.closedB j 0 = true ∧ A.mentionsData d = false ∧
      ∃ l, HasTy S 0 .one (D.paramCtx j) A (.univ l)) fun j A _ => do
    let E1 ← extTypes R E0 (D.params.take j)
    if h : (D.params.take j).reverse ++ [] = D.paramCtx j then
      let ⟨l, ⟨hA⟩⟩ ← inferType R (castCtx E1 rfl h) A
      if hc : A.closedB j 0 = true ∧ A.mentionsData d = false then pure ⟨hc.1, hc.2, l, hA⟩
      else fail "kernel: parameter type not closed or mentions the type"
    else fail "kernel: parameter context mismatch"
  let ⟨hcs⟩ ← forallElems D.ctors (fun c C =>
      let Sc := S ++ [.data (D.truncate c)]
      
      (∀ (k : Nat) (A : Tm), C.args[k]? = some (.point A) → A.closedB (np + k) 0 = true ∧
        A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
        HasTy (S ++ [.data (D.truncate 0)]) 0 .one (D.argCtx d C k) A (.univ D.level)) ∧
      (∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) → ψ.Scoped C.dims ∧
        b.closedB (np + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d np c C.args.length C b = true ∧
        HasTy Sc C.dims ψ (D.argCtx d C C.args.length) b (.data d (Ctor.paramVars np C.args.length)) ∧
        Ctor.bndTyped Sc C.dims ψ (D.argCtx d C C.args.length) D.level D.ctors d np b) ∧
      (∀ (k k' : Nat) (ψ ψ' : I) (b b' : Tm), C.bnd[k]? = some (ψ, b) → C.bnd[k']? = some (ψ', b') →
        EqTm Sc C.dims (.and ψ ψ') (D.argCtx d C C.args.length) b b'
          (.data d (Ctor.paramVars np C.args.length)))) fun c C _ => checkCtor S d D c C
  pure ⟨hl, hps, fun c C hC => hcs c C hC⟩

end

/-- A signature together with a proof that it is well-formed. -/
structure CheckedSig where
  sig : Sig
  wf : WfSig sig

def CheckedSig.empty : CheckedSig := ⟨[], fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩

/-- Check one more definition. -/
def CheckedSig.extend (C : CheckedSig) (t A : Tm) (fuel : Nat := defaultFuel) : K CheckedSig := do
  let ⟨h⟩ ← checkEntry C.sig t A fuel
  pure ⟨C.sig ++ [.defn t A], wfSig_append C.wf h⟩

/-- Check one more inductive type. -/
def CheckedSig.extendData (C : CheckedSig) (D : DataDecl) (fuel : Nat := defaultFuel) :
    K CheckedSig := do
  let S' := C.sig ++ [.data D]
  let ⟨h⟩ ← checkData C.sig C.sig.length D
  pure ⟨S', wfSig_appendData C.wf h⟩

def checkSigAux (pre : Sig) (hpre : WfSig pre) : (rest : Sig) → K (PLift (WfSig (pre ++ rest)))
  | [] => pure ⟨by simpa using hpre⟩
  | .defn t A :: rest => do
    let ⟨h⟩ ← checkEntry pre t A
    let ⟨h'⟩ ← checkSigAux (pre ++ [.defn t A]) (wfSig_append hpre h) rest
    pure ⟨by simpa using h'⟩
  | .data D :: rest => do
    let ⟨h⟩ ← checkData pre pre.length D
    let ⟨h'⟩ ← checkSigAux (pre ++ [.data D]) (wfSig_appendData hpre h) rest
    pure ⟨by simpa using h'⟩

/-- Check a whole signature. -/
def checkSig (S : Sig) : K (PLift (WfSig S)) := do
  let ⟨h⟩ ← checkSigAux [] ⟨fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩ S
  pure ⟨by simpa using h⟩

/-- Soundness of the kernel: by construction, `checkSig` only succeeds with a proof. -/
theorem checkSig_sound {S : Sig} {h : PLift (WfSig S)} (_ : checkSig S = .ok h) : WfSig S :=
  h.down

end KubusCore.Kernel
