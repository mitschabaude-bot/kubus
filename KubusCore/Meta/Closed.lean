import KubusCore.Meta.Basic

/-!
# Metatheory: closed terms, list terms and the signature

Substitution only depends on the free variables of a term (`closed_subst_eq`). The typing
rules of inductive types instantiate declarations of the signature (parameter types, argument
types, boundaries) by substituting lists of terms; these commute with substitution because
the declarations of a well-formed signature are closed (`SigClosed`, implied by `WfSig`).
-/

namespace KubusCore.Meta

open Tm

/-- Substitution only depends on the free variables. -/
theorem closed_subst_eq (t : Tm) : ∀ (n m : Nat) (σ σ' : Nat → Tm) (τ τ' : Nat → I),
    t.closedB n m = true → (∀ x < n, σ x = σ' x) → (∀ i < m, τ i = τ' i) →
    t.subst σ τ = t.subst σ' τ' := by
  have hup : ∀ {n : Nat} {σ σ' : Nat → Tm}, (∀ x < n, σ x = σ' x) → ∀ x < n + 1, up σ x = up σ' x := by
    intro n σ σ' h x hx; cases x with
    | zero => rfl
    | succ x => simp only [up]; rw [h x (by omega)]
  have hdup : ∀ {n : Nat} {σ σ' : Nat → Tm}, (∀ x < n, σ x = σ' x) →
      ∀ x < n, (fun k => (σ k).dshift) x = (fun k => (σ' k).dshift) x := by
    intro n σ σ' h x hx; simp only; rw [h x hx]
  have hIup : ∀ {m : Nat} {τ τ' : Nat → I}, (∀ i < m, τ i = τ' i) → ∀ i < m + 1, I.up τ i = I.up τ' i := by
    intro m τ τ' h i hi; cases i with
    | zero => rfl
    | succ i => simp only [I.up]; rw [h i (by omega)]
  have hI : ∀ {r : I} {m : Nat} {τ τ' : Nat → I}, r.scopedB m = true → (∀ i < m, τ i = τ' i) →
      r.subst τ = r.subst τ' := fun hr h => subst_scoped_eq ((I.scopedB_iff _ _).1 hr) h
  induction t with
  | var x => intro n m σ σ' τ τ' h h1 _; simp [closedB] at h; exact h1 x h
  | const | univ | abort | tnil => intros; rfl
  | pi A B ihA ihB | sigma A B ihA ihB | lam A B ihA ihB =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]; rw [ihA n m σ σ' τ τ' h.1 h1 h2, ihB (n + 1) m _ _ τ τ' h.2 (hup h1) h2]
  | app f a ihf iha | pair f a ihf iha | tcons f a ihf iha =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]; rw [ihf n m σ σ' τ τ' h.1 h1 h2, iha n m σ σ' τ τ' h.2 h1 h2]
  | fst p ih | snd p ih | data _ p ih =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB] at h
    simp only [subst]; rw [ih n m σ σ' τ τ' h h1 h2]
  | path A a b ihA iha ihb =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [ihA n (m + 1) _ _ _ _ h.1.1 (hdup h1) (hIup h2), iha n m σ σ' τ τ' h.1.2 h1 h2,
      ihb n m σ σ' τ τ' h.2 h1 h2]
  | plam t ih | ipi t ih =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB] at h
    simp only [subst]; rw [ih n (m + 1) _ _ _ _ h (hdup h1) (hIup h2)]
  | papp p r ih =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]; rw [ih n m σ σ' τ τ' h.1 h1 h2, hI h.2 h2]
  | split φ t ψ u iht ihu =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [hI h.1.1.1 h2, iht n m σ σ' τ τ' h.1.1.2 h1 h2, hI h.1.2 h2, ihu n m σ σ' τ τ' h.2 h1 h2]
  | transp A φ a ihA iha =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [ihA n (m + 1) _ _ _ _ h.1.1 (hdup h1) (hIup h2), hI h.1.2 h2, iha n m σ σ' τ τ' h.2 h1 h2]
  | hcomp A φ u a ihA ihu iha =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [ihA n m σ σ' τ τ' h.1.1.1 h1 h2, hI h.1.1.2 h2, ihu n (m + 1) _ _ _ _ h.1.2 (hdup h1) (hIup h2),
      iha n m σ σ' τ τ' h.2 h1 h2]
  | glue A φ T e ihA ihT ihe =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [ihA n m σ σ' τ τ' h.1.1.1 h1 h2, hI h.1.1.2 h2, ihT n m σ σ' τ τ' h.1.2 h1 h2,
      ihe n m σ σ' τ τ' h.2 h1 h2]
  | glueEl φ e t a ihe iht iha =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [hI h.1.1.1 h2, ihe n m σ σ' τ τ' h.1.1.2 h1 h2, iht n m σ σ' τ τ' h.1.2 h1 h2,
      iha n m σ σ' τ τ' h.2 h1 h2]
  | unglue φ e g ihe ihg =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [hI h.1.1 h2, ihe n m σ σ' τ τ' h.1.2 h1 h2, ihg n m σ σ' τ τ' h.2 h1 h2]
  | con d c ps args rs ihps iha =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true, List.all_eq_true] at h
    simp only [subst]
    rw [ihps n m σ σ' τ τ' h.1.1 h1 h2, iha n m σ σ' τ τ' h.1.2 h1 h2]
    congr 1
    exact List.map_congr_left fun r hr => hI (h.2 r hr) h2
  | elim d ps P bs t ihps ihP ihbs iht =>
    intro n m σ σ' τ τ' h h1 h2; simp only [closedB, Bool.and_eq_true] at h
    simp only [subst]
    rw [ihps n m σ σ' τ τ' h.1.1.1 h1 h2, ihP (n + 1) m _ _ τ τ' h.1.1.2 (hup h1) h2,
      ihbs n m σ σ' τ τ' h.1.2 h1 h2, iht n m σ σ' τ τ' h.2 h1 h2]

theorem closed_subst_id {t : Tm} {n m : Nat} (h : t.closedB n m = true) {σ : Nat → Tm} {τ : Nat → I}
    (h1 : ∀ x < n, σ x = .var x) (h2 : ∀ i < m, τ i = .var i) : t.subst σ τ = t := by
  rw [closed_subst_eq t n m σ Tm.var τ I.var h h1 h2, subst_var]

/-! ## List terms -/

theorem toList_ofList (L : List Tm) : (Tm.ofList L).toList = L := by
  induction L <;> simp_all [Tm.ofList, Tm.toList]

theorem ofList_subst (L : List Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (Tm.ofList L).subst σ τ = Tm.ofList (L.map (·.subst σ τ)) := by
  induction L <;> simp_all [Tm.ofList, Tm.subst]

theorem ofList_ren (L : List Tm) (ρ δ : Nat → Nat) :
    (Tm.ofList L).ren ρ δ = Tm.ofList (L.map (·.ren ρ δ)) := by
  induction L <;> simp_all [Tm.ofList, Tm.ren]

/-- A literal list term. -/
def IsList (t : Tm) : Prop := t = Tm.ofList t.toList

theorem toList_subst {t : Tm} (h : IsList t) (σ : Nat → Tm) (τ : Nat → I) :
    (t.subst σ τ).toList = t.toList.map (·.subst σ τ) := by
  rw [h, ofList_subst, toList_ofList, toList_ofList]

theorem isList_subst {t : Tm} (h : IsList t) (σ : Nat → Tm) (τ : Nat → I) : IsList (t.subst σ τ) := by
  unfold IsList; rw [toList_subst h, h, ofList_subst, toList_ofList]

theorem apps_subst (f : Tm) (as : List Tm) (σ : Nat → Tm) (τ : Nat → I) :
    (Tm.apps f as).subst σ τ = Tm.apps (f.subst σ τ) (as.map (·.subst σ τ)) := by
  induction as generalizing f <;> simp_all [Tm.apps, Tm.subst]

theorem papps_subst (f : Tm) (rs : List I) (σ : Nat → Tm) (τ : Nat → I) :
    (Tm.papps f rs).subst σ τ = Tm.papps (f.subst σ τ) (rs.map (·.subst τ)) := by
  induction rs generalizing f <;> simp_all [Tm.papps, Tm.subst]

/-- Instantiating a declaration closed below the length of the list commutes with substitution. -/
theorem substList_subst {A : Tm} {L : List Tm} (h : A.closedB L.length 0 = true) (σ : Nat → Tm)
    (τ : Nat → I) : (A.substList L).subst σ τ = A.substList (L.map (·.subst σ τ)) := by
  simp only [Tm.substList, subst_subst]
  apply closed_subst_eq A L.length 0 _ _ _ _ h
  · intro x hx
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.length_map]
    rw [List.getElem?_eq_getElem hx]; rfl
  · intro i hi; omega

/-! ## Signatures -/

/-- The syntactic part of `WfSig`: the declarations of the signature are closed. -/
structure SigClosed (S : Sig) : Prop where
  defn : ∀ (k : Nat) (t A : Tm), S[k]? = some (.defn t A) → t.closedB 0 0 = true ∧ A.closedB 0 0 = true
  params : ∀ (d : Nat) (D : DataDecl) (j : Nat) (A : Tm), S[d]? = some (.data D) →
    D.params[j]? = some A → A.closedB j 0 = true
  args : ∀ (d : Nat) (D : DataDecl) (c : Nat) (C : Ctor) (k : Nat) (A : Tm), S[d]? = some (.data D) →
    D.ctors[c]? = some C → C.args[k]? = some (.point A) → A.closedB (D.params.length + k) 0 = true
  bnd : ∀ (d : Nat) (D : DataDecl) (c : Nat) (C : Ctor) (k : Nat) (ψ : I) (b : Tm),
    S[d]? = some (.data D) → D.ctors[c]? = some C → C.bnd[k]? = some (ψ, b) →
    ψ.Scoped C.dims ∧ b.closedB (D.params.length + C.args.length) C.dims = true

theorem sigClosed_of_wfSig {S : Sig} (h : WfSig S) : SigClosed S where
  defn k t A hk := ⟨(h.1 k t A hk).1, (h.1 k t A hk).2.1⟩
  params d D j A hd hj := ((h.2 d D hd).2.1 j A hj).1
  args d D c C k A hd hc hk := ((h.2 d D hd).2.2 c C hc).1 k A hk |>.1
  bnd d D c C k ψ b hd hc hk := ⟨(((h.2 d D hd).2.2 c C hc).2.1 k ψ b hk).1,
    (((h.2 d D hd).2.2 c C hc).2.1 k ψ b hk).2.1⟩

end KubusCore.Meta
