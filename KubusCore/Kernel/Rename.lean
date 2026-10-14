import KubusCore.Kernel.Conv

/-!
# Kernel: judgments in the smallest context

A judgment about terms that mention only some of the variables of the context is derived in
the context of just those variables (term variables closed under the dependencies of their
types, and the interval variables they mention, with the restriction projected onto them),
and moved back along the renaming by the metatheory (`Meta.ren_ty`/`Meta.ren_eq`, through
the minimal judgments; this needs the signature to be well-formed). The cache keyed by the
small context then shares the result between all the contexts it occurs in: the contracta of
the Kan operations bind many interval variables around subterms that mention few of them.

The small context and the renaming are computed; the kernel checks the conditions of the
renaming theorem (injectivity and bounds of the interval renaming, entailment of the
restriction, the context lookups) and that renaming the small terms gives back the terms.
-/

namespace KubusCore.Kernel

open Meta (rS rI)

variable {S : Sig}

/-! ## Free variables -/

def _root_.KubusCore.I.collectVars (m : Nat) (r : I) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  r.vars.foldl (fun acc v => if v ≥ m then acc.insert (v - m) else acc) acc

/-- The free term variables (first) and interval variables (second) of `t`, where `k` term and
`m` interval variables are bound. -/
def _root_.KubusCore.Tm.collectVars (k m : Nat) : Tm → Std.HashSet Nat × Std.HashSet Nat →
    Std.HashSet Nat × Std.HashSet Nat
  | .var x, (xs, is) => (if x ≥ k then xs.insert (x - k) else xs, is)
  | .const _, acc | .univ _, acc | .abort, acc | .tnil, acc => acc
  | .pi A B, acc | .lam A B, acc | .sigma A B, acc => B.collectVars (k + 1) m (A.collectVars k m acc)
  | .app f a, acc | .pair f a, acc | .tcons f a, acc => a.collectVars k m (f.collectVars k m acc)
  | .fst p, acc | .snd p, acc | .data _ p, acc => p.collectVars k m acc
  | .path A a b, acc => b.collectVars k m (a.collectVars k m (A.collectVars k (m + 1) acc))
  | .plam t, acc | .ipi t, acc => t.collectVars k (m + 1) acc
  | .papp p r, (xs, is) => p.collectVars k m (xs, r.collectVars m is)
  | .split φ t ψ u, (xs, is) => u.collectVars k m (t.collectVars k m (xs, ψ.collectVars m (φ.collectVars m is)))
  | .transp A φ a, (xs, is) => a.collectVars k m (A.collectVars k (m + 1) (xs, φ.collectVars m is))
  | .hcomp A φ u a, (xs, is) =>
    a.collectVars k m (u.collectVars k (m + 1) (A.collectVars k m (xs, φ.collectVars m is)))
  | .glue A φ T e, (xs, is) => e.collectVars k m (T.collectVars k m (A.collectVars k m (xs, φ.collectVars m is)))
  | .glueEl φ e t a, (xs, is) => a.collectVars k m (t.collectVars k m (e.collectVars k m (xs, φ.collectVars m is)))
  | .unglue φ e g, (xs, is) => g.collectVars k m (e.collectVars k m (xs, φ.collectVars m is))
  | .con _ _ ps args rs, (xs, is) =>
    args.collectVars k m (ps.collectVars k m (xs, rs.foldl (fun is r => r.collectVars m is) is))
  | .elim _ ps P bs t, acc =>
    t.collectVars k m (bs.collectVars k m (P.collectVars (k + 1) m (ps.collectVars k m acc)))

/-! ## Renamings -/

/-- The interval renaming that sends `i` to the `i`-th kept variable (and the others above). -/
def dmap (vs : Array Nat) (Ψ : Nat) (i : Nat) : Nat := if h : i < vs.size then vs[i] else Ψ + i

/-- The term renaming that sends `j` to the `j`-th kept variable. -/
def rmap (ks : Array Nat) (n : Nat) (j : Nat) : Nat := if h : j < ks.size then ks[j] else n + j

/-- Strictly increasing and below `Ψ`. -/
def incrBelow (vs : Array Nat) (Ψ : Nat) : Bool :=
  (List.range vs.size).all fun i => if h : i < vs.size then
    vs[i] < Ψ && (if h' : i + 1 < vs.size then vs[i] < vs[i + 1] else true) else false

theorem incr_mono {vs : Array Nat} {Ψ : Nat} (h : incrBelow vs Ψ = true) :
    ∀ i j (hi : i < vs.size) (hj : j < vs.size), i < j → vs[i] < vs[j] := by
  intro i j hi hj hij
  induction j with
  | zero => omega
  | succ j ih =>
    have hjs : j < vs.size := by omega
    have hs := List.all_eq_true.1 h j (List.mem_range.2 hjs)
    simp only [hjs, ↓reduceDIte, hj, Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | h1
    · exact Nat.lt_trans (ih hjs h1) hs.2
    · subst h1; exact hs.2

theorem incr_below {vs : Array Nat} {Ψ : Nat} (h : incrBelow vs Ψ = true) :
    ∀ i (hi : i < vs.size), vs[i] < Ψ := by
  intro i hi
  have hs := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [hi, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

theorem dmap_inj {vs : Array Nat} {Ψ : Nat} (h : incrBelow vs Ψ = true) :
    ∀ i j, dmap vs Ψ i = dmap vs Ψ j → i = j := by
  intro i j e
  unfold dmap at e
  by_cases hi : i < vs.size <;> by_cases hj : j < vs.size <;> simp only [hi, hj, ↓reduceDIte] at e
  · rcases Nat.lt_trichotomy i j with h1 | h1 | h1
    · have := incr_mono h i j hi hj h1; omega
    · exact h1
    · have := incr_mono h j i hj hi h1; omega
  · have := incr_below h i hi; omega
  · have := incr_below h j hj; omega
  · omega

theorem dmap_bound {vs : Array Nat} {Ψ : Nat} (h : incrBelow vs Ψ = true) :
    ∀ i < vs.size, dmap vs Ψ i < Ψ := by
  intro i hi
  simp only [dmap, hi, ↓reduceDIte]
  exact incr_below h i hi

theorem lookup_lt : ∀ {Γ : Ctx} {x : Nat} {A : Tm}, Γ.lookup x = some A → x < Γ.length
  | [], _, _, h => by simp [Ctx.lookup] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: Γ, x + 1, A, h => by
    simp only [Ctx.lookup, Option.map_eq_some_iff] at h
    obtain ⟨B, hB, _⟩ := h
    have := lookup_lt hB
    simp; omega

/-- The context lookups commute with the renaming. -/
def lookOk (Δ Γ : Ctx) (ρ δ : Nat → Nat) : Bool :=
  (List.range Δ.length).all fun x =>
    match Δ.lookup x, Γ.lookup (ρ x) with
    | some A, some B => tmEq (A.subst (rS ρ) (rI δ)) B
    | _, _ => false

theorem lookOk_sound {Δ Γ : Ctx} {ρ δ : Nat → Nat} (h : lookOk Δ Γ ρ δ = true) :
    ∀ x A, Δ.lookup x = some A → Γ.lookup (ρ x) = some (A.subst (rS ρ) (rI δ)) := by
  intro x A hx
  have hb := List.all_eq_true.1 h x (List.mem_range.2 (lookup_lt hx))
  cases hB : Γ.lookup (ρ x) with
  | none => simp [hx, hB] at hb
  | some B =>
    simp only [hx, hB] at hb
    rw [tmEq_sound hb]

theorem wf0_of_wf (hS : WfSig S) {Ψ Φ Γ} : Wf S Ψ Φ Γ → Meta.Wf0 S Ψ Φ Γ
  | .nil h => .nil h
  | .cons h => .cons (Meta.spec_to_minimal hS h)

/-- A small context `Ψ'; Φ'; Δ` with a renaming into `Ψ; Φ; Γ` that satisfies the conditions of
the renaming theorem. -/
structure SmallCtx (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) where
  Ψ' : Nat
  Φ' : I
  Δ : Ctx
  E' : KCtx S Ψ' Φ' Δ
  ρ : Nat → Nat
  δ : Nat → Nat
  hS : WfSig S
  inj : ∀ i j, δ i = δ j → i = j
  bound : ∀ i < Ψ', δ i < Ψ
  ent : I.Entails Φ (Φ'.subst (rI δ))
  look : ∀ x A, Δ.lookup x = some A → Γ.lookup (ρ x) = some (A.subst (rS ρ) (rI δ))

theorem SmallCtx.tyRen (sc : SmallCtx S Ψ Φ Γ) (E : KCtx S Ψ Φ Γ) :
    Meta.TyRen S sc.Ψ' sc.Φ' sc.Δ Ψ Φ Γ sc.ρ sc.δ :=
  ⟨sc.inj, sc.bound, E.hsc, sc.ent, sc.look,
    Meta.wfAll_of_wf (Meta.sigClosed_of_wfSig sc.hS) (wf0_of_wf sc.hS E.wf)⟩

theorem SmallCtx.hasTy (sc : SmallCtx S Ψ Φ Γ) (E : KCtx S Ψ Φ Γ) {t A t0 A0 : Tm}
    (h : HasTy S sc.Ψ' sc.Φ' sc.Δ t A) (et : t.subst (rS sc.ρ) (rI sc.δ) = t0)
    (eA : A.subst (rS sc.ρ) (rI sc.δ) = A0) : HasTy S Ψ Φ Γ t0 A0 := by
  subst et; subst eA
  exact Meta.minimal_to_spec
    ((Meta.ren_ty (Meta.sigClosed_of_wfSig sc.hS) (Meta.spec_to_minimal sc.hS h)).2 (sc.tyRen E))

theorem SmallCtx.eqTm (sc : SmallCtx S Ψ Φ Γ) (E : KCtx S Ψ Φ Γ) {t u A t0 u0 A0 : Tm}
    (h : EqTm S sc.Ψ' sc.Φ' sc.Δ t u A) (et : t.subst (rS sc.ρ) (rI sc.δ) = t0)
    (eu : u.subst (rS sc.ρ) (rI sc.δ) = u0) (eA : A.subst (rS sc.ρ) (rI sc.δ) = A0) :
    EqTm S Ψ Φ Γ t0 u0 A0 := by
  subst et; subst eu; subst eA
  exact Meta.minimal_to_spec_eq
    ((Meta.ren_eq (Meta.sigClosed_of_wfSig sc.hS) (Meta.spec_to_minimal_eq sc.hS h)).2 (sc.tyRen E))

/-- The kept variables of a judgment about `ts`: the term variables they mention, closed under
the dependencies of their types, and the interval variables of all of these (sorted). -/
def keptVars (Γ : Ctx) (ts : List Tm) : Array Nat × Array Nat := Id.run do
  let (xs, is) := ts.foldl (fun acc t => t.collectVars 0 0 acc) ({}, {})
  let mut xs := xs
  let mut is := is
  let mut x := 0
  for A in Γ do
    if xs.contains x then
      -- the type of variable `x` lives in the context below it
      let (ys, js) := A.collectVars 0 0 ({}, is)
      is := js
      for y in ys do xs := xs.insert (x + 1 + y)
    x := x + 1
  let ks := xs.toArray.qsort (· < ·)
  let vs := is.toArray.qsort (· < ·)
  (ks, vs)

/-- Rename a term into the small context (`xmap`, `imap`: the positions of the kept variables). -/
def lowerTm (xmap imap : Std.HashMap Nat Nat) (base off : Nat) (t : Tm) : Tm :=
  t.subst (fun y => .var ((xmap.getD (base + y) 0) - off)) (fun i => .var (imap.getD i 0))

/-- The small context for a judgment about `ts`, if it is smaller. -/
def smallCtx? (R : Rec S) (E : KCtx S Ψ Φ Γ) (ts : List Tm) :
    K S (Option (SmallCtx S Ψ Φ Γ × List Tm)) := do
  let some ⟨hS⟩ := E.sig.wf | return none
  let (ks, vs) := keptVars Γ ts
  if ks.size == Γ.length && vs.size == Ψ then return none
  let xmap : Std.HashMap Nat Nat := (ks.toList.zipIdx).foldl (fun m (x, j) => m.insert x j) {}
  let imap : Std.HashMap Nat Nat := (vs.toList.zipIdx).foldl (fun m (i, j) => m.insert i j) {}
  let Ψ' := vs.size
  -- the restriction, projected onto the kept interval variables
  let fs := E.fs.get
  let Φ' := I.ofFaces (fs.map fun f => (f.filter fun (i, _) => imap.contains i).map
    fun (i, d) => (imap.getD i 0, d))
  -- the context: the type of the `j`-th kept variable `x` lives below it
  let Δ : Ctx := (ks.toList.zipIdx).map fun (x, j) =>
    match Γ[x]? with
    | some A => lowerTm xmap imap (x + 1) (j + 1) A
    | none => .abort
  let ρ := rmap ks Γ.length
  let δ := dmap vs Ψ
  if hinc : incrBelow vs Ψ = true then
    if hent : I.Entails Φ (Φ'.subst (rI δ)) then
      if hlook : lookOk Δ Γ ρ δ = true then
        if hs' : Φ'.Scoped Ψ' then
          let fs' := Φ'.faces
          let cached := ((← get).ctxs.find? Ψ' Φ' Δ [] fs' rfl hs' (fun _ _ _ => none)).filter
            fun E' => E'.sig.lv.length == E.sig.lv.length
          let E' ← match cached with
            | some E' => pure E'
            | none =>
              let E1 := (KCtx.root E.sig).dextN Ψ'
              let E0 ← if h : shiftIN Ψ' .one = .one ∧ dshiftN Ψ' [] = [] then
                  let E2 : KCtx S (0 + Ψ') .one [] := castCtx E1 h.1 h.2
                  let E3 : KCtx S Ψ' .one [] := Nat.zero_add Ψ' ▸ E2
                  pure (E3.restrict Φ' hs' (I.entails_one Φ'))
                else fail "kernel: small context"
              let E1 ← extTypes R E0 Δ.reverse
              if h : Δ.reverse.reverse ++ [] = Δ then
                let E' := castCtx E1 rfl h
                modify fun c => { c with ctxs := c.ctxs.insert Ψ' Φ' Δ [] fs' rfl E' }
                pure E'
              else fail "kernel: small context"
          let sc : SmallCtx S Ψ Φ Γ :=
            ⟨Ψ', Φ', Δ, E', ρ, δ, hS, dmap_inj hinc, dmap_bound hinc, hent, lookOk_sound hlook⟩
          return some (sc, ts.map (lowerTm xmap imap 0 0))
  return none

end KubusCore.Kernel
