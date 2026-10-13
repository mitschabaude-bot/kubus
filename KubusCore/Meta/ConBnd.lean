import KubusCore.Meta.PresupB

/-!
# Metatheory: the boundary of a constructor is typed

For a simple boundary element `b` of constructor `c` (`Ctor.simpleB`: a recursive argument, or a
constructor `c' < c` at the same parameters whose recursive arguments are simple and whose point
arguments are point arguments of `c`), `Ctor.bndAt b ps args rs` is typed at `data d ps` wherever
`con d c ps args rs` is typed by the `con` rule and the restriction entails the boundary's
cofibration. The point arguments' type equations (`Ctor.bndTyped`) are checked in the prefix
signature over the parameters and point arguments (`DataDecl.pointCtx`); `htr` carries them
from the spec's judgments over the prefix to the minimal judgments over `S`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## Free variables -/

theorem subst_freeIn_congr (t : Tm) : ∀ (σ σ' : Nat → Tm) (τ : Nat → I),
    (∀ x, t.freeIn x = true → σ x = σ' x) → t.subst σ τ = t.subst σ' τ := by
  have hup : ∀ {σ σ' : Nat → Tm} {P : Nat → Prop}, (∀ x, P x → σ x = σ' x) →
      ∀ x, (x = 0 ∨ ∃ y, x = y + 1 ∧ P y) → up σ x = up σ' x := by
    intro σ σ' P h x hx
    rcases hx with rfl | ⟨y, rfl, hy⟩
    · rfl
    · simp only [up]; rw [h y hy]
  induction t with
  | var x => intro σ σ' τ h; exact h x (by simp [freeIn])
  | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro σ σ' τ h
    simp only [subst]
    rw [ihA σ σ' τ (fun x hx => h x (by simp [freeIn, hx])),
      ihB _ _ τ (fun x hx => hup (P := fun y => B.freeIn (y + 1) = true) (fun y hy => h y (by simp [freeIn, hy])) x
        (by cases x with
            | zero => exact Or.inl rfl
            | succ y => exact Or.inr ⟨y, rfl, hx⟩))]
  | app f a ihf iha | pair f a ihf iha | tcons f a ihf iha =>
    intro σ σ' τ h
    simp only [subst]
    rw [ihf σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | fst p ih | snd p ih | data _ p ih =>
    intro σ σ' τ h; simp only [subst]; rw [ih σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | plam p ih | ipi p ih =>
    intro σ σ' τ h; simp only [subst]
    rw [ih _ _ _ (fun x hx => congrArg Tm.dshift (h x (by simp [freeIn, hx])))]
  | papp p r ih =>
    intro σ σ' τ h; simp only [subst]; rw [ih σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | path A a b ihA iha ihb =>
    intro σ σ' τ h; simp only [subst]
    rw [ihA _ _ _ (fun x hx => congrArg Tm.dshift (h x (by simp [freeIn, hx]))),
      iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), ihb σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | split φ a ψ b iha ihb =>
    intro σ σ' τ h; simp only [subst]
    rw [iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), ihb σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | unglue φ a b iha ihb =>
    intro σ σ' τ h; simp only [subst]
    rw [iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), ihb σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | transp A φ a ihA iha =>
    intro σ σ' τ h; simp only [subst]
    rw [ihA _ _ _ (fun x hx => congrArg Tm.dshift (h x (by simp [freeIn, hx]))),
      iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | hcomp A φ u a ihA ihu iha =>
    intro σ σ' τ h; simp only [subst]
    rw [ihA σ σ' τ (fun x hx => h x (by simp [freeIn, hx])),
      ihu _ _ _ (fun x hx => congrArg Tm.dshift (h x (by simp [freeIn, hx]))),
      iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | glue A φ T e ihA ihT ihe =>
    intro σ σ' τ h; simp only [subst]
    rw [ihA σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), ihT σ σ' τ (fun x hx => h x (by simp [freeIn, hx])),
      ihe σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | glueEl φ e t a ihe iht iha =>
    intro σ σ' τ h; simp only [subst]
    rw [ihe σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), iht σ σ' τ (fun x hx => h x (by simp [freeIn, hx])),
      iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | con d c ps args rs ihps iha =>
    intro σ σ' τ h; simp only [subst]
    rw [ihps σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), iha σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro σ σ' τ h; simp only [subst]
    rw [ihps σ σ' τ (fun x hx => h x (by simp [freeIn, hx])),
      ihP _ _ τ (fun x hx => hup (P := fun y => P.freeIn (y + 1) = true) (fun y hy => h y (by simp [freeIn, hy])) x
        (by cases x with
            | zero => exact Or.inl rfl
            | succ y => exact Or.inr ⟨y, rfl, hx⟩)),
      ihbs σ σ' τ (fun x hx => h x (by simp [freeIn, hx])), iht σ σ' τ (fun x hx => h x (by simp [freeIn, hx]))]

theorem freeIn_lt (t : Tm) : ∀ (n m x : Nat), t.closedB n m = true → t.freeIn x = true → x < n := by
  induction t with
  | var y => intro n m x h hx; simp [closedB, freeIn] at h hx; omega
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact ihA _ _ _ h.1 hx
    · have := ihB _ _ _ h.2 hx; omega
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact ihps _ _ _ h.1.1.1 hx
    · have := ihP _ _ _ h.1.1.2 hx; omega
    · exact ihbs _ _ _ h.1.2 hx
    · exact iht _ _ _ h.2 hx
  | const | univ | abort | tnil => intro n m x h hx; simp [freeIn] at hx
  | app f a ihf iha | pair f a ihf iha | tcons f a ihf iha =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact ihf _ _ _ h.1 hx
    · exact iha _ _ _ h.2 hx
  | fst p ih | snd p ih | data _ p ih | plam p ih | ipi p ih =>
    intro n m x h hx; simp only [closedB, freeIn] at h hx; exact ih _ _ _ h hx
  | papp p r ih =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true] at h hx; exact ih _ _ _ h.1 hx
  | path A a b ihA iha ihb =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with (hx | hx) | hx
    · exact ihA _ _ _ h.1.1 hx
    · exact iha _ _ _ h.1.2 hx
    · exact ihb _ _ _ h.2 hx
  | split φ a ψ b iha ihb =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact iha _ _ _ h.1.1.2 hx
    · exact ihb _ _ _ h.2 hx
  | unglue φ a b iha ihb =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact iha _ _ _ h.1.2 hx
    · exact ihb _ _ _ h.2 hx
  | transp A φ a ihA iha =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact ihA _ _ _ h.1.1 hx
    · exact iha _ _ _ h.2 hx
  | hcomp A φ u a ihA ihu iha | glue A φ u a ihA ihu iha =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with (hx | hx) | hx
    · exact ihA _ _ _ h.1.1.1 hx
    · exact ihu _ _ _ h.1.2 hx
    · exact iha _ _ _ h.2 hx
  | glueEl φ e t a ihe iht iha =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with (hx | hx) | hx
    · exact ihe _ _ _ h.1.1.2 hx
    · exact iht _ _ _ h.1.2 hx
    · exact iha _ _ _ h.2 hx
  | con d c ps args rs ihps iha =>
    intro n m x h hx; simp only [closedB, freeIn, Bool.and_eq_true, Bool.or_eq_true] at h hx
    rcases hx with hx | hx
    · exact ihps _ _ _ h.1.1 hx
    · exact iha _ _ _ h.1.2 hx

/-! ## Point arguments -/

/-- The substitution of the list `L` (most recent first), with the variables after it sent to
`var (y - L.length + c)`. -/
def lsub (L : List Tm) (c : Nat) (y : Nat) : Tm := L.getD y (.var (y - L.length + c))

theorem consT_lsub (a : Tm) (L : List Tm) (c : Nat) : consT a (lsub L c) = lsub (a :: L) c := by
  funext y; cases y with
  | zero => rfl
  | succ y =>
    simp only [consT, lsub, List.getD_cons_succ, List.length_cons]
    congr 2; omega

theorem substList_eq_lsub (L : List Tm) (t : Tm) : t.substList L = t.subst (lsub L 0) I.var := rfl

theorem lsub_lt {L : List Tm} {y : Nat} (h : y < L.length) (c : Nat) : lsub L c y = L[y] := by
  simp [lsub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The point arguments among the first `k` arguments `as` (most recent first), before `R`. -/
def ptL (C : Ctor) (as R : List Tm) : Nat → List Tm
  | 0 => R
  | k + 1 => if C.isRec k then ptL C as R k else as.getD k .abort :: ptL C as R k

def recCount (C : Ctor) (k : Nat) : Nat := ((List.range k).filter C.isRec).length

theorem recCount_succ (C : Ctor) (k : Nat) :
    recCount C (k + 1) = recCount C k + (if C.isRec k then 1 else 0) := by
  simp only [recCount, List.range_succ, List.filter_append, List.length_append]
  cases h : C.isRec k <;> simp [List.filter, h]

theorem recCount_le (C : Ctor) (k : Nat) : recCount C k ≤ k := by
  have := List.length_filter_le C.isRec (List.range k); simp only [List.length_range] at this
  exact this

theorem pointRen_zero_left (C : Ctor) (x : Nat) : C.pointRen 0 x = x := by
  simp [Ctor.pointRen]

theorem pointRen_ge (C : Ctor) {n x : Nat} (h : n ≤ x) : C.pointRen n x = x - recCount C n := by
  simp [Ctor.pointRen, recCount, Nat.not_lt.2 h]

theorem pointRen_succ_zero (C : Ctor) (k : Nat) : C.pointRen (k + 1) 0 = 0 := by
  simp [Ctor.pointRen]

theorem pointRen_succ_succ (C : Ctor) (k x : Nat) :
    C.pointRen (k + 1) (x + 1) = (if C.isRec k then 0 else 1) + C.pointRen k x := by
  by_cases hx : x < k
  · simp only [Ctor.pointRen, show x + 1 < k + 1 by omega, hx, if_true, List.range_succ_eq_map,
      List.filter_cons, List.filter_map]
    have e : ((fun y => !C.isRec (k + 1 - 1 - y)) ∘ Nat.succ) = fun y => !C.isRec (k - 1 - y) := by
      funext y; simp only [Function.comp]; congr 2; omega
    rw [e]
    cases h : C.isRec k <;> simp [h] <;> omega
  · rw [pointRen_ge C (show k + 1 ≤ x + 1 by omega), pointRen_ge C (show k ≤ x by omega), recCount_succ]
    have := recCount_le C k
    cases C.isRec k <;> simp <;> omega

theorem ptL_length (C : Ctor) (as R : List Tm) :
    ∀ k, (ptL C as R k).length + recCount C k = k + R.length
  | 0 => by simp [ptL, recCount]
  | k + 1 => by
    have := ptL_length C as R k
    rw [recCount_succ]
    cases h : C.isRec k <;> simp [ptL, h] <;> omega

theorem ptL_get (C : Ctor) (as R : List Tm) : ∀ k, k ≤ as.length → ∀ x, x < k + R.length →
    (x < k → C.isRec (k - 1 - x) = false) →
    (ptL C as R k)[C.pointRen k x]? = ((as.take k).reverse ++ R)[x]?
  | 0, _, x, _, _ => by simp [ptL, pointRen_zero_left]
  | k + 1, hk, x, hx, hc => by
    have htake : (as.take (k + 1)).reverse ++ R = as[k] :: ((as.take k).reverse ++ R) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append]
      rfl
    rw [htake]
    cases x with
    | zero =>
      have := hc (by omega); simp only [Nat.add_sub_cancel, Nat.sub_zero] at this
      simp [ptL, this, pointRen_succ_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < as.length by omega)]
      all_goals rfl
    | succ x =>
      have ih := ptL_get C as R k (by omega) x (by omega) (fun h => by
        have := hc (by omega); rw [← this]; congr 1; omega)
      rw [pointRen_succ_succ]
      cases h : C.isRec k
      · simp only [ptL, h, Bool.false_eq_true, if_false, Nat.add_comm 1, List.getElem?_cons_succ]; exact ih
      · simp only [ptL, h, if_true, Nat.zero_add, List.getElem?_cons_succ]; exact ih

theorem lsub_of_getElem? {L : List Tm} {y : Nat} {e : Tm} (h : L[y]? = some e) (c : Nat) :
    lsub L c y = e := by
  simp [lsub, List.getD_eq_getElem?_getD, h]

theorem getElem?_params {X ps : List Tm} {p : Nat} (hp : p < ps.length) :
    (X ++ ps.reverse)[X.length + ps.length - 1 - p]? = some ps[p] := by
  rw [List.getElem?_append_right (by omega), List.getElem?_reverse (by omega)]
  rw [show ps.length - 1 - (X.length + ps.length - 1 - p - X.length) = p by omega]
  exact List.getElem?_eq_getElem hp

theorem paramVars_subst {np k : Nat} {σ : Nat → Tm} {τ : Nat → I} {ps : List Tm}
    (hlen : ps.length = np) (h : ∀ (p : Nat) (hp : p < ps.length), σ (k + np - 1 - p) = ps[p]) :
    (Ctor.paramVars np k).subst σ τ = Tm.ofList ps := by
  simp only [Ctor.paramVars, ofList_subst, List.map_map]
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Function.comp, Tm.subst]
  exact h i h2

theorem paramVars_toList (np k : Nat) :
    (Ctor.paramVars np k).toList = (List.range np).map fun p => Tm.var (k + np - 1 - p) :=
  toList_ofList _

theorem paramVars_ren (np k e : Nat) :
    (Ctor.paramVars np k).ren (· + e) id = Ctor.paramVars np (k + e) := by
  simp only [Ctor.paramVars, ofList_ren, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [List.mem_range] at hp
  simp only [Function.comp, Tm.ren]
  congr 1; omega

theorem tele_get {S : Sig} {Ψ Φ Γ} : ∀ {ts Δ prev}, HasTele0 S Ψ Φ Γ ts Δ prev →
    ∀ (k : Nat) (a A : Tm), ts.toList[k]? = some a → Δ[k]? = some A →
    HasTy0 S Ψ Φ Γ a (A.substList ((ts.toList.take k).reverse ++ prev))
  | _, _, _, .nil _ => fun k a A h _ => by simp [Tm.toList] at h
  | _, _, _, .cons h0 h1 => fun k a A ha hA => by
    cases k with
    | zero =>
      simp only [Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at ha hA
      subst ha; subst hA; simpa using h0
    | succ k =>
      simp only [Tm.toList, List.getElem?_cons_succ] at ha hA
      have := tele_get h1 k a A ha hA
      simpa [Tm.toList, List.take_succ_cons] using this

theorem lookup_of_get : ∀ (Γ : Ctx) (x : Nat) (A : Tm), Γ[x]? = some A →
    Γ.lookup x = some (A.ren (· + (x + 1)) id)
  | [], _, _, h => by simp at h
  | B :: Γ, 0, A, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    rfl
  | B :: Γ, x + 1, A, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [Ctx.lookup, lookup_of_get Γ x A h, Option.map_some, Option.some.injEq, Tm.shift, ren_ren]
    congr 1

theorem paramCtx_succ (D : DataDecl) {j : Nat} (h : j < D.params.length) :
    D.paramCtx (j + 1) = D.params[j] :: D.paramCtx j := by
  simp only [DataDecl.paramCtx]
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp

theorem pointCtx_succ (D : DataDecl) (d : Nat) (C : Ctor) (k : Nat) :
    D.pointCtx d C (k + 1) = if C.isRec k then D.pointCtx d C k else
      (C.argTy d D.params.length k).ren (C.pointRen k) id :: D.pointCtx d C k := by
  simp only [DataDecl.pointCtx, List.range_succ, List.filter_append]
  cases h : C.isRec k <;> simp [h]

theorem argCtx_get (D : DataDecl) (d : Nat) (C : Ctor) {n j : Nat} (h : j < n) :
    (D.argCtx d C n)[j]? = some (C.argTy d D.params.length (n - 1 - j)) := by
  simp only [DataDecl.argCtx]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [h]

theorem pt_agree (C : Ctor) {as R : List Tm} {n x : Nat} (hlen : as.length = n)
    (hx : x < n → C.isRec (n - 1 - x) = false) :
    lsub (ptL C as R n) (n + R.length) (C.pointRen n x) = (as.reverse ++ R).getD x (.var x) := by
  by_cases hxl : x < n + R.length
  · have h1 := ptL_get C as R n (by omega) x hxl hx
    rw [List.take_of_length_le (by omega)] at h1
    have hxl' : x < (as.reverse ++ R).length := by simp; omega
    have h2 : (as.reverse ++ R)[x]? = some (as.reverse ++ R)[x] := List.getElem?_eq_getElem hxl'
    rw [h2] at h1
    rw [lsub_of_getElem? h1, List.getD_eq_getElem?_getD, h2]; rfl
  · have hl := ptL_length C as R n
    have hr := recCount_le C n
    rw [pointRen_ge C (by omega)]
    simp only [lsub, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]
    congr 1; omega


theorem isRec_true {C : Ctor} {k : Nat} (h : C.isRec k = true) : C.args[k]? = some .recur := by
  simpa [Ctor.isRec] using h

theorem argTy_rec {C : Ctor} {d np k : Nat} (h : C.isRec k = true) :
    C.argTy d np k = .data d (Ctor.paramVars np k) := by
  simp [Ctor.argTy, isRec_true h]

/-- The boundary, typed by recursion on its simple structure. -/
theorem bnd_rec (hS : SigClosed S) {d : Nat}
    (htr : ∀ {Ψ' Φ' Γ' t u A}, EqTm (S.take d) Ψ' Φ' Γ' t u A → EqTm0 S Ψ' Φ' Γ' t u A)
    {Ψ Φ Γ} {D : DataDecl} {c : Nat} {C : Ctor} {ps : Tm} {ψ : I} {σp σ : Nat → Tm} {τ : Nat → I}
    (hD : S[d]? = some (.data D)) (hps : ps = Tm.ofList ps.toList)
    (hdata : HasTy0 S Ψ Φ Γ (data d ps) (Tm.univ D.level)) (hpt : HasTele0 S Ψ Φ Γ ps D.params [])
    (hσ : TySub S C.dims ψ (D.pointCtx d C C.args.length) Ψ Φ Γ σp τ)
    (hag : ∀ X, C.mentionsRec C.args.length X = false →
      (X.ren (C.pointRen C.args.length) id).subst σp τ = X.subst σ τ)
    (hlook : ∀ j T, j < C.args.length → (D.argCtx d C C.args.length).lookup j = some T →
      HasTy0 S Ψ Φ Γ (σ j) (T.subst σ τ))
    (hpv : (Ctor.paramVars D.params.length C.args.length).subst σ τ = ps)
    (hτ : ∀ i < C.dims, (τ i).Scoped Ψ) (t : Tm) :
    (Ctor.simpleB D.ctors d D.params.length c C.args.length C t = true →
      Ctor.bndTyped (S.take d) C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length)
        D.level D.ctors d D.params.length t →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      HasTy0 S Ψ Φ Γ (t.subst σ τ) (data d ps)) ∧
    (∀ (c' : Nat) (C' : Ctor) (k : Nat) (prev : List Tm), D.ctors[c']? = some C' → prev.length = k →
      Ctor.simpleArgs D.ctors d D.params.length c C.args.length C C' k t = true →
      Ctor.bndTypedArgs (S.take d) C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length)
        D.level D.ctors d D.params.length C' (Ctor.paramVars D.params.length C.args.length) k prev t →
      t.closedB (D.params.length + C.args.length) C.dims = true →
      HasTele0 S Ψ Φ Γ (t.subst σ τ) ((List.range' k t.toList.length).map (C'.argTy d D.params.length))
        (prev.map (·.subst σ τ) ++ ps.toList.reverse)) := by
  have hpl : ps.toList.length = D.params.length := by have := tele_length hpt; simpa using this
  -- the parameters, instantiated by a list ending in `ps`
  have hpvL : ∀ (L : List Tm) (k : Nat), L.length = k →
      (Ctor.paramVars D.params.length k).substList (L ++ ps.toList.reverse) = ps := by
    intro L k hL
    rw [substList_eq_lsub, paramVars_subst hpl, ← hps]
    intro p hp
    apply lsub_of_getElem?
    have := getElem?_params (X := L) hp
    rwa [hL, hpl] at this
  -- the type of a variable for a recursive argument
  have hvar : ∀ j, j < C.args.length → C.isRec (C.args.length - 1 - j) = true →
      HasTy0 S Ψ Φ Γ (σ j) (data d ps) := by
    intro j hj hr
    have hl := lookup_of_get _ _ _ (argCtx_get D d C hj)
    have := hlook j _ hj hl
    rwa [argTy_rec hr, Tm.ren, paramVars_ren,
      show C.args.length - 1 - j + (j + 1) = C.args.length by omega, Tm.subst, hpv] at this
  induction t with
  | var j =>
    refine ⟨fun h _ _ => ?_, fun _ _ _ _ _ _ h => by simp [Ctor.simpleArgs] at h⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact hvar j h.1 h.2
  | con d' c' ps' as' rs' _ ihas =>
    refine ⟨fun h hb hcl => ?_, fun _ _ _ _ _ _ h => by simp [Ctor.simpleArgs] at h⟩
    simp only [Ctor.simpleB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, hc'c⟩, rfl⟩, h⟩ := h
    cases hc' : D.ctors[c']? with
    | none => simp [hc'] at h
    | some C' =>
      simp only [hc', Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hlen, hdims⟩, hsa⟩ := h
      simp only [Ctor.bndTyped, hc'] at hb
      simp only [closedB, Bool.and_eq_true, List.all_eq_true] at hcl
      have ht := ihas.2 c' C' 0 [] hc' rfl hsa hb hcl.1.2
      rw [hlen, ← List.range_eq_range'] at ht
      simp only [Tm.subst, hpv]
      exact HasTy0.con hD hc' hps hdata hpt ht (by simp [hdims])
        (fun r hr => by
          simp only [List.mem_map] at hr
          obtain ⟨r0, hr0, rfl⟩ := hr
          exact scoped_subst ((I.scopedB_iff _ _).1 (hcl.2 r0 hr0)) hτ)
  | tnil =>
    refine ⟨fun h => by simp [Ctor.simpleB] at h, fun _ _ _ _ _ _ _ _ _ => ?_⟩
    exact HasTele0.nil (wf_of_ty hdata)
  | tcons a as iha ihas =>
    refine ⟨fun h => by simp [Ctor.simpleB] at h, fun c' C' k prev hc' hprev h hb hcl => ?_⟩
    simp only [Ctor.simpleArgs, Bool.and_eq_true] at h
    simp only [Ctor.bndTypedArgs] at hb
    simp only [closedB, Bool.and_eq_true] at hcl
    have htl := ihas.2 c' C' (k + 1) (a :: prev) hc' (by simp [hprev]) h.2 hb.2.2 hcl.2
    show HasTele0 S Ψ Φ Γ (Tm.tcons (a.subst σ τ) (as.subst σ τ))
      (C'.argTy d D.params.length k :: (List.range' (k + 1) as.toList.length).map (C'.argTy d D.params.length))
      (prev.map (·.subst σ τ) ++ ps.toList.reverse)
    refine HasTele0.cons ?_ (by simpa using htl)
    cases hr : C'.isRec k
    · simp only [hr, Bool.false_eq_true, if_false] at h
      obtain ⟨hsa, -⟩ := h
      cases a with
      | var j =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hsa
        obtain ⟨hj, hjr⟩ := hsa
        have hl := lookup_of_get _ _ _ (argCtx_get D d C hj)
        obtain ⟨hmT, hmY, he⟩ := hb.1 j _ rfl hr hl
        have he0 := (sub_eq hS (htr he)).2 hσ
        rw [hag _ hmT, hag _ hmY] at he0
        have hx := HasTy0.conv (hlook j _ hj hl) he0
        have hcl' : (C'.argTy d D.params.length k).closedB
            ((prev ++ (Ctor.paramVars D.params.length C.args.length).toList.reverse).length) 0 = true := by
          have := argTy_closed hS hD hc' k
          simp only [List.length_append, List.length_reverse, paramVars_toList, List.length_map,
            List.length_range, hprev]
          rwa [Nat.add_comm]
        rw [substList_subst hcl', List.map_append, List.map_reverse] at hx
        have hpvl : (Ctor.paramVars D.params.length C.args.length).toList.map (·.subst σ τ) = ps.toList := by
          rw [← hpv, toList_subst (by unfold IsList; rw [Ctor.paramVars, toList_ofList])]
        rw [hpvl] at hx
        exact hx
      | _ => simp at hsa
    · simp only [hr, if_true] at h
      have := (iha.1 h.1 (hb.2.1 hr) hcl.1)
      rw [argTy_rec hr, substList_eq_lsub]
      simp only [Tm.subst]
      rw [← substList_eq_lsub, hpvL _ k (by simp [hprev])]
      exact this
  | _ =>
    exact ⟨fun h => by simp [Ctor.simpleB] at h, fun _ _ _ _ _ _ h => by simp [Ctor.simpleArgs] at h⟩


theorem rev_shift (as R : List Tm) (k y : Nat) :
    (as.reverse ++ R)[y + (as.length - k)]? = ((as.take k).reverse ++ R)[y]? := by
  have e : as.reverse = (as.drop k).reverse ++ (as.take k).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [e, List.append_assoc, List.getElem?_append_right (by simp only [List.length_reverse, List.length_drop]; omega)]
  simp only [List.length_reverse, List.length_drop]
  rw [show y + (as.length - k) - (as.length - k) = y by omega]

theorem argTys_get {C : Ctor} {d np k : Nat} (h : k < C.args.length) :
    (C.argTys d np)[k]? = some (C.argTy d np k) := by
  simp [Ctor.argTys, h]

theorem tySub_nil {Ψs Φs Ψ Φ Γ σ τ} (hb : ∀ i < Ψs, (τ i).Scoped Ψ) (he : I.Entails Φ (Φs.subst τ))
    (hw : Wf0 S Ψ Φ Γ) : TySub S Ψs Φs [] Ψ Φ Γ σ τ :=
  { bound := hb, hscoped := scoped_of_wf hw, ent := he, wf := hw
    look := fun x A h => by simp [Ctx.lookup] at h }

/-- The parameters as a substitution out of the parameter context. -/
theorem tySub_params (hS : SigClosed S) {d : Nat} {D : DataDecl} (hD : S[d]? = some (.data D))
    {Ψs Φs Ψ Φ Γ τ} {ps : Tm} (hpt : HasTele0 S Ψ Φ Γ ps D.params []) (e : Nat)
    (h0 : ∀ σ, TySub S Ψs Φs [] Ψ Φ Γ σ τ) :
    ∀ j, j ≤ D.params.length → TySub S Ψs Φs (D.paramCtx j) Ψ Φ Γ (lsub (ps.toList.take j).reverse e) τ
  | 0, _ => by simpa [DataDecl.paramCtx] using h0 _
  | j + 1, hj => by
    have hpl : ps.toList.length = D.params.length := by simpa using tele_length hpt
    have ih := tySub_params hS hD hpt e h0 j (by omega)
    have hpj : ps.toList[j]? = some ps.toList[j] := List.getElem?_eq_getElem (by omega)
    have hA : D.params[j]? = some D.params[j] := List.getElem?_eq_getElem (by omega)
    have ha := tele_get hpt j _ _ hpj hA
    have hcl := hS.params d D j _ hD hA
    have hlen : ((ps.toList.take j).reverse).length = j := by simp; omega
    rw [List.append_nil, substList_eq_lsub,
      closed_subst_eq _ j 0 _ (lsub (ps.toList.take j).reverse e) _ τ hcl
        (fun x hx => by rw [lsub_lt (by omega), lsub_lt (by omega)]) (fun i hi => by omega)] at ha
    have := ih.cons ha
    rw [consT_lsub] at this
    have ht : (ps.toList.take (j + 1)).reverse = ps.toList[j] :: (ps.toList.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
    rw [paramCtx_succ D (by omega), ht]
    exact this

/-- The parameters and the point arguments as a substitution out of the point context. -/
theorem tySub_points (hS : SigClosed S) (hW : WfSig S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {Ψs Φs Ψ Φ Γ τ} {ps args : Tm} {e : Nat}
    (hP : TySub S Ψs Φs (D.paramCtx D.params.length) Ψ Φ Γ (lsub ps.toList.reverse e) τ)
    (hat : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hpl : ps.toList.length = D.params.length) :
    ∀ k, k ≤ C.args.length →
      TySub S Ψs Φs (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args.toList ps.toList.reverse k) e) τ
  | 0, _ => by simpa [DataDecl.pointCtx, ptL] using hP
  | k + 1, hk => by
    have ih := tySub_points hS hW hD hC hP hat hpl k (by omega)
    have hal : args.toList.length = C.args.length := by
      have := tele_length hat; rwa [argTys_length] at this
    rw [pointCtx_succ]
    cases hr : C.isRec k
    · simp only [hr, Bool.false_eq_true, if_false, ptL]
      have hk' : k < C.args.length := by omega
      obtain ⟨A, hA⟩ : ∃ A, C.args[k]? = some (.point A) := by
        simp only [Ctor.isRec, List.getElem?_eq_getElem hk'] at hr ⊢
        cases h : C.args[k] with
        | point A => exact ⟨A, rfl⟩
        | recur => simp [h] at hr
      obtain ⟨hcl, -, hnr, -⟩ := ((hW.2 d D hD).2.2 c C hC).1 k A hA
      have hty : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
      have hak : args.toList[k]? = some args.toList[k] := List.getElem?_eq_getElem (by omega)
      have ha := tele_get hat k _ (C.argTy d D.params.length k) hak (argTys_get hk')
      have hFl : ((args.toList.take k).reverse ++ ps.toList.reverse).length = k + D.params.length := by
        simp [hpl]; omega
      have heq : (A.ren (C.pointRen k) id).subst (lsub (ptL C args.toList ps.toList.reverse k) e) τ =
          A.substList ((args.toList.take k).reverse ++ ps.toList.reverse) := by
        rw [subst_ren, substList_eq_lsub,
          closed_subst_eq A _ 0 _ (fun y => lsub (ptL C args.toList ps.toList.reverse k) e (C.pointRen k y))
            _ I.var hcl (fun _ _ => rfl) (fun i hi => by omega)]
        apply subst_freeIn_congr
        intro y hy
        have hyl := freeIn_lt A _ _ _ hcl hy
        have hc : y < k → C.isRec (k - 1 - y) = false := by
          intro hy'
          simp only [Ctor.noRecDeps, List.all_eq_true, List.mem_range] at hnr
          have := hnr (k - 1 - y) (by omega)
          rw [show k - 1 - (k - 1 - y) = y by omega, hy] at this
          simpa using this
        have h1 := ptL_get C args.toList ps.toList.reverse k (by omega) y (by simp [hpl]; omega) hc
        have h2 : ((args.toList.take k).reverse ++ ps.toList.reverse)[y]? =
            some ((args.toList.take k).reverse ++ ps.toList.reverse)[y] :=
          List.getElem?_eq_getElem (by omega)
        rw [lsub_of_getElem? (h1.trans h2), lsub_lt (by omega)]
      rw [← hty] at heq
      rw [← heq] at ha
      have := ih.cons ha
      rw [consT_lsub] at this
      simpa [List.getD_eq_getElem?_getD, hak] using this
    · simpa [hr, ptL] using ih

theorem conBnd_typed (hW : WfSig S) {d : Nat}
    (htr : ∀ {Ψ' Φ' Γ' t u A}, EqTm (S.take d) Ψ' Φ' Γ' t u A → EqTm0 S Ψ' Φ' Γ' t u A)
    {Ψ Φ Γ} {D : DataDecl} {c : Nat} {C : Ctor} {ps args : Tm} {rs : List I} {k : Nat} {ψ : I} {b : Tm}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) (hk : C.bnd[k]? = some (ψ, b))
    (hent : I.Entails Φ (Ctor.cofAt ψ rs)) (hps : ps = Tm.ofList ps.toList)
    (hargs : args = Tm.ofList args.toList)
    (hdata : HasTy0 S Ψ Φ Γ (data d ps) (univ D.level)) (hpt : HasTele0 S Ψ Φ Γ ps D.params [])
    (hat : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hrs : rs.length = C.dims) (hrsc : ∀ r ∈ rs, r.Scoped Ψ) :
    HasTy0 S Ψ Φ Γ (Ctor.bndAt b ps.toList args.toList rs) (data d ps) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, -, hctors⟩ := hW.2 d D hD
  obtain ⟨-, hbndW, -⟩ := hctors c C hC
  obtain ⟨-, hbcl, hsimp, -, hbt⟩ := hbndW k ψ b hk
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length hpt
  have hal : args.toList.length = C.args.length := by
    have := tele_length hat; rwa [argTys_length] at this
  have hw := wf_of_ty hdata
  have hτ : ∀ i < C.dims, ((fun i => rs.reverse.getD i (.var i)) i).Scoped Ψ := fun i hi => by
    show (rs.reverse.getD i (.var i)).Scoped Ψ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    exact hrsc _ (List.mem_reverse.1 (List.getElem_mem _))
  have h0 : ∀ σ, TySub S C.dims ψ [] Ψ Φ Γ σ (fun i => rs.reverse.getD i (.var i)) :=
    fun σ => tySub_nil hτ hent hw
  have hP := tySub_params hS hD hpt (C.args.length + D.params.length) h0 _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hP
  have hσ := tySub_points hS hW hD hC hP hat hpl _ (Nat.le_refl _)
  have hag : ∀ X, C.mentionsRec C.args.length X = false →
      (X.ren (C.pointRen C.args.length) id).subst
        (lsub (ptL C args.toList ps.toList.reverse C.args.length) (C.args.length + D.params.length))
        (fun i => rs.reverse.getD i (.var i)) =
      X.subst (fun j => (args.toList.reverse ++ ps.toList.reverse).getD j (.var j))
        (fun i => rs.reverse.getD i (.var i)) := by
    intro X hm
    rw [subst_ren]
    apply subst_freeIn_congr
    intro y hy
    have hc : y < C.args.length → C.isRec (C.args.length - 1 - y) = false := by
      intro hy'
      simp only [Ctor.mentionsRec, List.any_eq_false, List.mem_range] at hm
      have := hm y hy'
      cases h : C.isRec (C.args.length - 1 - y)
      · rfl
      · simp [h, hy] at this
    have := pt_agree C (R := ps.toList.reverse) hal hc
    rw [List.length_reverse, hpl] at this
    exact this
  have hlook : ∀ j T, j < C.args.length → (D.argCtx d C C.args.length).lookup j = some T →
      HasTy0 S Ψ Φ Γ ((fun j => (args.toList.reverse ++ ps.toList.reverse).getD j (.var j)) j)
        (T.subst (fun j => (args.toList.reverse ++ ps.toList.reverse).getD j (.var j))
          (fun i => rs.reverse.getD i (.var i))) := by
    intro j T hj hT
    rw [lookup_of_get _ _ _ (argCtx_get D d C hj), Option.some.injEq] at hT
    subst hT
    have hkl : C.args.length - 1 - j < args.toList.length := by omega
    have hak : args.toList[C.args.length - 1 - j]? = some args.toList[C.args.length - 1 - j] :=
      List.getElem?_eq_getElem hkl
    have ha := tele_get hat _ _ (C.argTy d D.params.length (C.args.length - 1 - j)) hak
      (argTys_get (by omega))
    have hcl := argTy_closed hS hD hC (C.args.length - 1 - j)
    have hx : (args.toList.reverse ++ ps.toList.reverse).getD j (.var j) =
        args.toList[C.args.length - 1 - j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
        List.getElem?_reverse (by omega)]
      simp only [hal, hak, Option.getD_some]
    show HasTy0 S Ψ Φ Γ ((args.toList.reverse ++ ps.toList.reverse).getD j (.var j)) _
    rw [hx, subst_ren]
    rw [substList_eq_lsub, closed_subst_eq _ _ 0 _
      (fun y => (args.toList.reverse ++ ps.toList.reverse).getD (y + (j + 1)) (.var (y + (j + 1)))) _
      (fun i => rs.reverse.getD (id i) (.var (id i))) hcl (fun y hy => ?_) (fun i hi => by omega)] at ha
    · exact ha
    · have := rev_shift args.toList ps.toList.reverse (C.args.length - 1 - j) y
      rw [show args.toList.length - (C.args.length - 1 - j) = j + 1 by omega] at this
      have hyl : y < ((args.toList.take (C.args.length - 1 - j)).reverse ++ ps.toList.reverse).length := by
        simp [hpl, hal]; omega
      show _ = (args.toList.reverse ++ ps.toList.reverse).getD (y + (j + 1)) (.var (y + (j + 1)))
      rw [lsub_lt hyl, List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem hyl]
      rfl
  have hpv : (Ctor.paramVars D.params.length C.args.length).subst
      (fun j => (args.toList.reverse ++ ps.toList.reverse).getD j (.var j))
      (fun i => rs.reverse.getD i (.var i)) = ps := by
    rw [paramVars_subst hpl, ← hps]
    intro p hp
    have := getElem?_params (X := args.toList.reverse) hp
    rw [List.length_reverse, hal, hpl] at this
    rw [List.getD_eq_getElem?_getD, this]; rfl
  exact (bnd_rec hS htr hD hps hdata hpt hσ hag hlook hpv hτ b).1 hsimp hbt hbcl

end KubusCore.Meta
