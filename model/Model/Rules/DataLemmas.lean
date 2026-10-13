import Model.Rules.DataSem

/-!
# Lemmas for the rules of inductive types
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem toList_ofList_eq : ∀ L : List Tm, (Tm.ofList L).toList = L
  | [] => rfl
  | t :: L => by simp [Tm.ofList, Tm.toList, toList_ofList_eq L]

theorem argEnv_eq_of_lt' {ps pre : List V} {x : ℕ} (hx : x < pre.length + ps.length) :
    argEnv ps pre x = (pre.reverse ++ ps.reverse)[x]'(by simp; omega) := by
  simp [argEnv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega : x < (pre.reverse ++ ps.reverse).length)]

theorem sem_ofList_vlist (S : Sig) (L : List Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (Tm.ofList L) m ρ γ = vlist (L.map fun t => sem S t m ρ γ) := by
  induction L with
  | nil => rfl
  | cons t L ih => simp only [Tm.ofList, List.map_cons, vlist]; rw [← ih]; rfl

theorem ParamsOK.restr {σ : SigV} {D : DataDecl} {ps : RV m} (h : ParamsOK σ D m ps) (g : Hom n m) :
    ParamsOK σ D n (fun k f => ps k (g.comp f)) := fun k f => h k (g.comp f)

theorem plist_pair (a b : V) (n : ℕ) : plist (ZFSet.pair a b) (n + 1) = a :: plist b n := by
  simp only [plist, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp [vnth]
  · apply List.map_congr_left; intro i _; simp [vnth]

/-- Substitution only depends on the free variables. -/
theorem Tm.subst_congr_free : ∀ (t : Tm) (σ σ' : ℕ → Tm) (τ : ℕ → I),
    (∀ x, t.freeIn x = true → σ x = σ' x) → t.subst σ τ = t.subst σ' τ := by
  intro t
  induction t with
  | var x => intro σ σ' τ h; exact h x (by simp [Tm.freeIn])
  | pi A B iA iB | sigma A B iA iB | lam A B iA iB =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]),
      iB (Tm.up σ) (Tm.up σ') τ fun x hx => by
        cases x with
        | zero => rfl
        | succ y => simp only [Tm.up]; rw [h y (by simp [Tm.freeIn, hx])]]
  | elim d ps P bs t ip iP ib it =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [ip σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]),
      iP (Tm.up σ) (Tm.up σ') τ (fun x hx => by
        cases x with
        | zero => rfl
        | succ y => simp only [Tm.up]; rw [h y (by simp [Tm.freeIn, hx])]),
      ib σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), it σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | path A a b iA ia ib =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA _ (fun n => (σ' n).dshift) _ fun x hx => by rw [h x (by simp [Tm.freeIn, hx])],
      ia σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), ib σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | plam A iA | ipi A iA =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA _ (fun n => (σ' n).dshift) _ fun x hx => by rw [h x (by simp [Tm.freeIn, hx])]]
  | transp A φ a iA ia =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA _ (fun n => (σ' n).dshift) _ fun x hx => by rw [h x (by simp [Tm.freeIn, hx])],
      ia σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | hcomp A φ u a iA iu ia =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]),
      iu _ (fun n => (σ' n).dshift) _ fun x hx => by rw [h x (by simp [Tm.freeIn, hx])],
      ia σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | app A B iA iB | pair A B iA iB | tcons A B iA iB =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), iB σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | fst A iA | snd A iA | papp A _ iA | data _ A iA =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | split _ A _ B iA iB | unglue _ A B iA iB =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), iB σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | con _ _ A B _ iA iB =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), iB σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | glue A _ B E iA iB iE | glueEl _ A B E iA iB iE =>
    intro σ σ' τ h
    simp only [Tm.subst]
    rw [iA σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]), iB σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx]),
      iE σ σ' τ fun x hx => h x (by simp [Tm.freeIn, hx])]
  | const _ | univ _ | abort | tnil => intros; rfl

theorem Tm.subst_ofList (σ : ℕ → Tm) (τ : ℕ → I) : ∀ L : List Tm,
    (Tm.ofList L).subst σ τ = Tm.ofList (L.map (·.subst σ τ))
  | [] => rfl
  | t :: L => by simp [Tm.ofList, Tm.subst, Tm.subst_ofList σ τ L]

theorem listLen_unique : ∀ {v : V} {n n' : ℕ}, ListLen v n → ListLen v n' → n = n'
  | v, 0, 0, _, _ => rfl
  | v, 0, n' + 1, h, h' => by
    simp only [ListLen] at h; obtain ⟨⟨a, b, rfl⟩, -⟩ := h'
    exact absurd h (pair_ne_empty a b)
  | v, n + 1, 0, h, h' => by
    simp only [ListLen] at h'; obtain ⟨⟨a, b, rfl⟩, -⟩ := h
    exact absurd h' (pair_ne_empty a b)
  | v, n + 1, n' + 1, h, h' => by rw [listLen_unique h.2 h'.2]

/-- The parameter variables substituted by the parameters. -/
theorem paramVars_substList (ps : List Tm) (pre : List Tm) :
    (Ctor.paramVars ps.length pre.length).substList (pre ++ ps.reverse) = Tm.ofList ps := by
  rw [Ctor.paramVars, Tm.substList, Tm.subst_ofList, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, Tm.subst, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), List.getElem?_reverse (by omega)]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  congr 1; omega

theorem sem_eq_sigUpTo {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) {A : Tm} (hA : A.ConstsLt (d + 1))
    (hm : A.mentionsData d = false) : sem S A = interp (sigUpTo S d) univC TyCode A := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 hd
  refine (interp_congr_md _ _ (sigUpTo_agree S S.length hk.le) (fun m => ?_) A hA hm).symm
  rw [sigUpTo_cst_ge S d d m le_rfl, show sigUpTo S S.length = sigV S from rfl, sigV_cst_data hd]

/-- The condition under which `argTySem` is the raw type. -/
theorem argTySem_eq {σ : SigV} {D : DataDecl} {d c j n : ℕ} {psv : V} {pre : List V} :
    argTySem σ D d c j n psv pre = if j < (D.ctors.getD c default).args.length ∧
      (D.ctors.getD c default).isRec j = false ∧ argPreValid σ D d c j n psv pre
    then argTyRaw σ D d c j n psv pre else emptyC n := rfl

theorem argTyRaw_take_eq {σ : SigV} {D : DataDecl} {d c j n : ℕ} {psv : V} {pre pre' : List V}
    (h : pre.take j = pre'.take j) : argTyRaw σ D d c j n psv pre = argTyRaw σ D d c j n psv pre' := by
  simp only [argTyRaw, h]

/-- The type of a point argument instantiated by earlier arguments and parameters. -/
theorem sem_argTy_subst {d : ℕ} {D : DataDecl} (hd : S[d]? = some (.data D)) (hsyn : DataSyn d D) {c : ℕ}
    {C : Ctor} (hC : D.ctors[c]? = some C) {j : ℕ} {A : Tm} (hA : C.args[j]? = some (.point A))
    (pre ps : List Tm) (hpre : pre.length = j) (hps : ps.length = D.params.length) {ρ : IEnv m} {γ : ℕ → V}
    (hnat : ∀ t ∈ pre ++ ps.reverse, Natural S t m ρ γ) :
    sem S (A.substList (pre ++ ps.reverse)) m ρ γ =
      argTyRaw (sigUpTo S d) D d c j m (sem S (Tm.ofList ps) m ρ γ) (pre.reverse.map fun t => sem S t m ρ γ) := by
  obtain ⟨hcl, hcs, hmd, -⟩ := hsyn.2.2 c C hC j A hA
  have harg : (D.ctors.getD c default).argTy d D.params.length j = A := by
    rw [getD_ctors hC]; simp [Ctor.argTy, hA]
  rw [Tm.substList, sem_subst S A m ρ γ _ _ (natural_substList hnat), sem_eq_sigUpTo hd hcs hmd, argTyRaw, harg,
    plist_sem _ _ _ (by rw [toList_ofList_eq, hps]), toList_ofList_eq,
    List.take_of_length_le (by simp [hpre])]
  refine interp_congr_closed _ _ _ A _ 0 hcl m _ _ _ _ (fun _ h => absurd h (by omega)) fun x hx => ?_
  rw [sem_substList_env _ _ _ x (by simp; omega), argEnv_eq_of_lt' (by simp; omega)]
  have e : ((pre.reverse.map fun t => sem S t m ρ γ).reverse ++ (ps.map fun t => sem S t m ρ γ).reverse) =
      (pre ++ ps.reverse).map fun t => sem S t m ρ γ := by simp [List.map_append, List.map_reverse]
  rw [List.getElem_of_eq e, List.getElem_map]

end

end Model
