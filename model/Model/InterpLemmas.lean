import Model.Sem

/-!
# Renaming and substitution lemmas for the interpretation
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-! ### Environments -/

@[simp] theorem TEnv.cons_zero (γ : ℕ → V) (a : V) : TEnv.cons γ a 0 = a := rfl
@[simp] theorem TEnv.cons_succ (γ : ℕ → V) (a : V) (x : ℕ) : TEnv.cons γ a (x + 1) = γ x := rfl

theorem TEnv.restr_cons (γ : ℕ → V) (a : V) (f : Hom k m) :
    TEnv.restr (TEnv.cons γ a) f = TEnv.cons (TEnv.restr γ f) (res f a) := by
  funext x; cases x <;> rfl

theorem TEnv.restr_restr (γ : ℕ → V) (f : Hom k m) (g : Hom n k) :
    TEnv.restr (TEnv.restr γ f) g = TEnv.restr γ (f.comp g) := by
  funext x; simp [TEnv.restr, res_res]

theorem TEnv.cons_comp_upRen (γ : ℕ → V) (a : V) (ρ' : ℕ → ℕ) :
    (fun x => TEnv.cons γ a (Tm.upRen ρ' x)) = TEnv.cons (fun x => γ (ρ' x)) a := by
  funext x; cases x <;> rfl

theorem IEnv.ext_comp_upRen (ρ : IEnv m) (δ : ℕ → ℕ) :
    (fun i => ρ.ext (Tm.upRen δ i)) = IEnv.ext (fun i => ρ (δ i)) := by
  funext i; cases i <;> rfl

theorem IEnv.cons_comp_upRen (ρ : IEnv m) (r : DM m) (δ : ℕ → ℕ) :
    (fun i => ρ.cons r (Tm.upRen δ i)) = IEnv.cons (fun i => ρ (δ i)) r := by
  funext i; cases i <;> rfl

theorem restr_ext_comp_upRen (ρ : IEnv m) (δ : ℕ → ℕ) (g : Hom k (m + 1)) :
    (fun i => (ρ.ext.restr g) (Tm.upRen δ i)) = (IEnv.ext (fun i => ρ (δ i))).restr g := by
  funext i; cases i <;> rfl

theorem ival_ren (ρ : IEnv m) (δ : ℕ → ℕ) (r : I) : ival ρ (r.ren δ) = ival (fun i => ρ (δ i)) r := by
  rw [I.ren, ival.subst]; rfl

/-! ### Renaming -/

theorem sem_ren (S : Sig) : ∀ (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) (ρ' δ : ℕ → ℕ),
    sem S (t.ren ρ' δ) m ρ γ = sem S t m (fun i => ρ (δ i)) (fun x => γ (ρ' x)) := by
  intro t
  induction t with
  | var x => intros; rfl
  | const c => intros; rfl
  | univ l => intros; rfl
  | pi A B ihA ihB =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    have hB : (fun k (f : Hom k m) a => interp (cstFn S) univC TyCode (B.ren (Tm.upRen ρ') δ) k (ρ.restr f)
        (TEnv.cons (TEnv.restr γ f) a)) = (fun k f a => interp (cstFn S) univC TyCode B k
          (IEnv.restr (fun i => ρ (δ i)) f) (TEnv.cons (TEnv.restr (fun x => γ (ρ' x)) f) a)) := by
      funext k f a; rw [ihB]; congr 1; funext x; cases x <;> rfl
    simp only [ihA, hB]
  | lam A t ihA iht =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    rw [ihA]; congr 1; funext k f a
    rw [iht]; congr 1; funext x; cases x <;> rfl
  | app f a ihf iha =>
    intro m ρ γ ρ' δ; simp only [sem, interp, Tm.ren] at *; simp only [ihf, iha]; rfl
  | sigma A B ihA ihB =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    have hB : (fun k (f : Hom k m) a => interp (cstFn S) univC TyCode (B.ren (Tm.upRen ρ') δ) k (ρ.restr f)
        (TEnv.cons (TEnv.restr γ f) a)) = (fun k f a => interp (cstFn S) univC TyCode B k
          (IEnv.restr (fun i => ρ (δ i)) f) (TEnv.cons (TEnv.restr (fun x => γ (ρ' x)) f) a)) := by
      funext k f a; rw [ihB]; congr 1; funext x; cases x <;> rfl
    simp only [ihA, hB]
  | pair a b iha ihb =>
    intro m ρ γ ρ' δ; simp only [sem, interp, Tm.ren] at *; simp only [iha, ihb]
  | fst p ih => intro m ρ γ ρ' δ; simp only [sem, interp, Tm.ren] at *; rw [ih]
  | snd p ih => intro m ρ γ ρ' δ; simp only [sem, interp, Tm.ren] at *; rw [ih]
  | path A a b ihA iha ihb =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ihA, iha, ihb, IEnv.ext_comp_upRen, restr_ext_comp_upRen]; rfl
  | plam t ih =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ih, IEnv.ext_comp_upRen, restr_ext_comp_upRen]; rfl
  | papp p r ih =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    rw [ih, ival_ren]
  | ipi A ih =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ih, IEnv.ext_comp_upRen, restr_ext_comp_upRen]; rfl
  | split φ t ψ u iht ihu =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [iht, ihu, ival_ren]
  | abort => intros; rfl
  | transp A φ a ihA iha =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ihA, iha, ival_ren, IEnv.ext_comp_upRen, restr_ext_comp_upRen]; rfl
  | hcomp A φ u a ihA ihu iha =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ihA, iha, ihu, ival_ren, IEnv.cons_comp_upRen]; rfl
  | glue A φ T e ihA ihT ihe =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ihA, ihT, ihe, ival_ren]; rfl
  | glueEl φ e t a ihe iht iha =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    simp only [ihe, iht, iha, ival_ren]; rfl
  | unglue φ e g ihe ihg =>
    intro m ρ γ ρ' δ
    simp only [sem, interp, Tm.ren] at *
    rw [ihe, ihg, ival_ren]

/-! ### Naturality -/

theorem Natural.restr {S : Sig} {s : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S s m ρ γ)
    (f : Hom k m) : Natural S s k (ρ.restr f) (TEnv.restr γ f) := by
  intro n g
  rw [IEnv.restr_restr, TEnv.restr_restr, h, h, res_res]

theorem natural_var (S : Sig) (x : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Natural S (.var x) m ρ γ := by
  intro k f; rfl

theorem sem_shift (S : Sig) (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (a : V) :
    sem S t.shift m ρ (TEnv.cons γ a) = sem S t m ρ γ := by
  rw [Tm.shift, sem_ren]; rfl

theorem sem_dshift (S : Sig) (t : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S t.dshift (m + 1) ρ.ext γ = sem S t (m + 1) (ρ.restr (Hom.wk m)) γ := by
  rw [Tm.dshift, sem_ren]; rfl

theorem sem_dshift_cons (S : Sig) (t : Tm) (ρ : IEnv m) (r : DM m) (γ : ℕ → V) :
    sem S t.dshift m (ρ.cons r) γ = sem S t m ρ γ := by
  rw [Tm.dshift, sem_ren]; rfl

theorem Natural.shift {S : Sig} {s : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S s m ρ γ) (a : V) :
    Natural S s.shift m ρ (TEnv.cons γ a) := by
  intro k f
  rw [TEnv.restr_cons, sem_shift, sem_shift, h]

theorem Natural.up {S : Sig} {σ : ℕ → Tm} {ρ : IEnv m} {γ : ℕ → V}
    (h : ∀ x, Natural S (σ x) m ρ γ) (a : V) : ∀ x, Natural S (Tm.up σ x) m ρ (TEnv.cons γ a)
  | 0 => natural_var S 0 ρ _
  | x + 1 => (h x).shift a

theorem Natural.dshift {S : Sig} {s : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S s m ρ γ) :
    Natural S s.dshift (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) := by
  intro k f
  have e1 : sem S s.dshift k (ρ.ext.restr f) (TEnv.restr (TEnv.restr γ (Hom.wk m)) f) =
      sem S s k (ρ.restr ((Hom.wk m).comp f)) (TEnv.restr γ ((Hom.wk m).comp f)) := by
    rw [Tm.dshift, sem_ren, TEnv.restr_restr]; rfl
  rw [e1, h, sem_dshift, h, res_res]

theorem Natural.dshift_cons {S : Sig} {s : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S s m ρ γ)
    (g : Hom n m) (r : DM n) : Natural S s.dshift n ((ρ.restr g).cons r) (TEnv.restr γ g) := by
  intro k f
  rw [IEnv.cons_restr, sem_dshift_cons, sem_dshift_cons, (h.restr g) k f]

theorem ival_up_ext (ρ : IEnv m) (τ : ℕ → I) :
    (fun i => ival ρ.ext (I.up τ i)) = IEnv.ext (fun i => ival ρ (τ i)) := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp only [I.up, I.shift, ival_ren]; rfl

theorem ival_up_cons (ρ : IEnv n) (r : DM n) (τ : ℕ → I) :
    (fun i => ival (ρ.cons r) (I.up τ i)) = IEnv.cons (fun i => ival ρ (τ i)) r := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp only [I.up, I.shift, ival_ren]; rfl

/-! ### Substitution -/

theorem sem_subst (S : Sig) : ∀ (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) (σ : ℕ → Tm) (τ : ℕ → I),
    (∀ x, Natural S (σ x) m ρ γ) →
    sem S (t.subst σ τ) m ρ γ = sem S t m (fun i => ival ρ (τ i)) (fun x => sem S (σ x) m ρ γ) := by
  intro t
  induction t with
  | var x => intros; rfl
  | const c => intros; rfl
  | univ l => intros; rfl
  | pi A B ihA ihB =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hB : (fun k (f : Hom k m) a => interp (cstFn S) univC TyCode (B.subst (Tm.up σ) τ) k (ρ.restr f)
        (TEnv.cons (TEnv.restr γ f) a)) = (fun k f a => interp (cstFn S) univC TyCode B k
          (IEnv.restr (fun i => ival ρ (τ i)) f)
          (TEnv.cons (TEnv.restr (fun x => sem S (σ x) m ρ γ) f) a)) := by
      funext k f a
      rw [ihB _ _ _ _ _ (Natural.up (fun x => (hσ x).restr f) a)]
      congr 1; funext x; cases x with
      | zero => rfl
      | succ x => exact (sem_shift S _ _ _ a).trans ((hσ x) k f)
    simp only [ihA _ _ _ _ _ hσ, hB]
  | lam A t ihA iht =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    rw [ihA _ _ _ _ _ hσ]; congr 1; funext k f a
    rw [iht _ _ _ _ _ (Natural.up (fun x => (hσ x).restr f) a)]
    congr 1; funext x; cases x with
    | zero => rfl
    | succ x => exact (sem_shift S _ _ _ a).trans ((hσ x) k f)
  | app f a ihf iha =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have ha' : ∀ k (g : Hom k m), interp (cstFn S) univC TyCode (a.subst σ τ) k (ρ.restr g) (TEnv.restr γ g) =
        interp (cstFn S) univC TyCode a k (IEnv.restr (fun i => ival ρ (τ i)) g)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) g) := by
      intro k g; rw [iha _ _ _ _ _ (fun x => (hσ x).restr g)]; congr 1; funext x; exact (hσ x) k g
    simp only [ha', ihf _ _ _ _ _ hσ, iha _ _ _ _ _ hσ]
  | sigma A B ihA ihB =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hB : (fun k (f : Hom k m) a => interp (cstFn S) univC TyCode (B.subst (Tm.up σ) τ) k (ρ.restr f)
        (TEnv.cons (TEnv.restr γ f) a)) = (fun k f a => interp (cstFn S) univC TyCode B k
          (IEnv.restr (fun i => ival ρ (τ i)) f)
          (TEnv.cons (TEnv.restr (fun x => sem S (σ x) m ρ γ) f) a)) := by
      funext k f a
      rw [ihB _ _ _ _ _ (Natural.up (fun x => (hσ x).restr f) a)]
      congr 1; funext x; cases x with
      | zero => rfl
      | succ x => exact (sem_shift S _ _ _ a).trans ((hσ x) k f)
    simp only [ihA _ _ _ _ _ hσ, hB]
  | pair a b iha ihb =>
    intro m ρ γ σ τ hσ; simp only [sem, interp, Tm.subst] at *; rw [iha _ _ _ _ _ hσ, ihb _ _ _ _ _ hσ]
  | fst p ih => intro m ρ γ σ τ hσ; simp only [sem, interp, Tm.subst] at *; rw [ih _ _ _ _ _ hσ]
  | snd p ih => intro m ρ γ σ τ hσ; simp only [sem, interp, Tm.subst] at *; rw [ih _ _ _ _ _ hσ]
  | path A a b ihA iha ihb =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hA' : interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) (m + 1) ρ.ext
        (TEnv.restr γ (Hom.wk m)) = interp (cstFn S) univC TyCode A (m + 1) (IEnv.ext (fun i => ival ρ (τ i)))
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) := by
      rw [ihA _ _ _ _ _ (fun x => (hσ x).dshift), ival_up_ext]
      congr 1; funext x; exact (sem_dshift S _ _ _).trans ((hσ x) _ _)
    have hres : ∀ k (g : Hom k (m + 1)), interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) k
        (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp (cstFn S) univC TyCode A k ((IEnv.ext (fun i => ival ρ (τ i))).restr g)
          (TEnv.restr (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) g) := by
      intro k g
      rw [ihA _ _ _ _ _ (fun x => ((hσ x).dshift).restr g)]
      have e1 : (fun i => ival (ρ.ext.restr g) (I.up τ i)) = (IEnv.ext (fun i => ival ρ (τ i))).restr g := by
        rw [← ival_up_ext]; rfl
      rw [e1]; congr 1; funext x
      exact ((hσ x).dshift k g).trans (by rw [sem_dshift, (hσ x) _ (Hom.wk m)]; rfl)
    simp only [hA', hres, iha _ _ _ _ _ hσ, ihb _ _ _ _ _ hσ]
  | plam t ih =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hval : interp (cstFn S) univC TyCode (t.subst (fun n => (σ n).dshift) (I.up τ)) (m + 1) ρ.ext
        (TEnv.restr γ (Hom.wk m)) = interp (cstFn S) univC TyCode t (m + 1) (IEnv.ext (fun i => ival ρ (τ i)))
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) := by
      rw [ih _ _ _ _ _ (fun x => (hσ x).dshift), ival_up_ext]
      congr 1; funext x; exact (sem_dshift S _ _ _).trans ((hσ x) _ _)
    have hres : ∀ k (g : Hom k (m + 1)), interp (cstFn S) univC TyCode (t.subst (fun n => (σ n).dshift) (I.up τ)) k
        (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp (cstFn S) univC TyCode t k ((IEnv.ext (fun i => ival ρ (τ i))).restr g)
          (TEnv.restr (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) g) := by
      intro k g
      rw [ih _ _ _ _ _ (fun x => ((hσ x).dshift).restr g)]
      have e1 : (fun i => ival (ρ.ext.restr g) (I.up τ i)) = (IEnv.ext (fun i => ival ρ (τ i))).restr g := by
        rw [← ival_up_ext]; rfl
      rw [e1]; congr 1; funext x
      exact ((hσ x).dshift k g).trans (by rw [sem_dshift, (hσ x) _ (Hom.wk m)]; rfl)
    simp only [hval, hres]
  | papp p r ih =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    rw [ih _ _ _ _ _ hσ, ival.subst]
  | ipi A ih =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hA' : interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) (m + 1) ρ.ext
        (TEnv.restr γ (Hom.wk m)) = interp (cstFn S) univC TyCode A (m + 1) (IEnv.ext (fun i => ival ρ (τ i)))
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) := by
      rw [ih _ _ _ _ _ (fun x => (hσ x).dshift), ival_up_ext]
      congr 1; funext x; exact (sem_dshift S _ _ _).trans ((hσ x) _ _)
    have hres : ∀ k (g : Hom k (m + 1)), interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) k
        (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp (cstFn S) univC TyCode A k ((IEnv.ext (fun i => ival ρ (τ i))).restr g)
          (TEnv.restr (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) g) := by
      intro k g
      rw [ih _ _ _ _ _ (fun x => ((hσ x).dshift).restr g)]
      have e1 : (fun i => ival (ρ.ext.restr g) (I.up τ i)) = (IEnv.ext (fun i => ival ρ (τ i))).restr g := by
        rw [← ival_up_ext]; rfl
      rw [e1]; congr 1; funext x
      exact ((hσ x).dshift k g).trans (by rw [sem_dshift, (hσ x) _ (Hom.wk m)]; rfl)
    simp only [hA', hres]
  | split φ t ψ u iht ihu =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    simp only [iht _ _ _ _ _ hσ, ihu _ _ _ _ _ hσ, ival.subst]
  | abort => intros; rfl
  | transp A φ a ihA iha =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hA' : interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) (m + 1) ρ.ext
        (TEnv.restr γ (Hom.wk m)) = interp (cstFn S) univC TyCode A (m + 1) (IEnv.ext (fun i => ival ρ (τ i)))
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) := by
      rw [ihA _ _ _ _ _ (fun x => (hσ x).dshift), ival_up_ext]
      congr 1; funext x; exact (sem_dshift S _ _ _).trans ((hσ x) _ _)
    have hres : ∀ k (g : Hom k (m + 1)), interp (cstFn S) univC TyCode (A.subst (fun n => (σ n).dshift) (I.up τ)) k
        (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        interp (cstFn S) univC TyCode A k ((IEnv.ext (fun i => ival ρ (τ i))).restr g)
          (TEnv.restr (TEnv.restr (fun x => sem S (σ x) m ρ γ) (Hom.wk m)) g) := by
      intro k g
      rw [ihA _ _ _ _ _ (fun x => ((hσ x).dshift).restr g)]
      have e1 : (fun i => ival (ρ.ext.restr g) (I.up τ i)) = (IEnv.ext (fun i => ival ρ (τ i))).restr g := by
        rw [← ival_up_ext]; rfl
      rw [e1]; congr 1; funext x
      exact ((hσ x).dshift k g).trans (by rw [sem_dshift, (hσ x) _ (Hom.wk m)]; rfl)
    have ha' : ∀ k (g : Hom k m), interp (cstFn S) univC TyCode (a.subst σ τ) k (ρ.restr g) (TEnv.restr γ g) =
        interp (cstFn S) univC TyCode a k (IEnv.restr (fun i => ival ρ (τ i)) g)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) g) := by
      intro k g; rw [iha _ _ _ _ _ (fun x => (hσ x).restr g)]; congr 1; funext x; exact (hσ x) k g
    simp only [hA', hres, ha', iha _ _ _ _ _ hσ, ival.subst]
  | hcomp A φ u a ihA ihu iha =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hu' : ∀ n (h : Hom n m) r, interp (cstFn S) univC TyCode (u.subst (fun n => (σ n).dshift) (I.up τ)) n
        ((ρ.restr h).cons r) (TEnv.restr γ h) = interp (cstFn S) univC TyCode u n
          ((IEnv.restr (fun i => ival ρ (τ i)) h).cons r) (TEnv.restr (fun x => sem S (σ x) m ρ γ) h) := by
      intro n h r
      rw [ihu _ _ _ _ _ (fun x => (hσ x).dshift_cons h r), ival_up_cons]
      congr 1; funext x; exact (sem_dshift_cons S _ _ _ _).trans ((hσ x) _ _)
    have hA' : ∀ k (g : Hom k m), interp (cstFn S) univC TyCode (A.subst σ τ) k (ρ.restr g) (TEnv.restr γ g) =
        interp (cstFn S) univC TyCode A k (IEnv.restr (fun i => ival ρ (τ i)) g)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) g) := by
      intro k g; rw [ihA _ _ _ _ _ (fun x => (hσ x).restr g)]; congr 1; funext x; exact (hσ x) k g
    have ha' : ∀ k (g : Hom k m), interp (cstFn S) univC TyCode (a.subst σ τ) k (ρ.restr g) (TEnv.restr γ g) =
        interp (cstFn S) univC TyCode a k (IEnv.restr (fun i => ival ρ (τ i)) g)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) g) := by
      intro k g; rw [iha _ _ _ _ _ (fun x => (hσ x).restr g)]; congr 1; funext x; exact (hσ x) k g
    simp only [hA', ha', ihA _ _ _ _ _ hσ, iha _ _ _ _ _ hσ, ival.subst, hu']
  | glue A φ T e ihA ihT ihe =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    have hT : ∀ k (f : Hom k m), interp (cstFn S) univC TyCode (T.subst σ τ) k (ρ.restr f) (TEnv.restr γ f) =
        interp (cstFn S) univC TyCode T k (IEnv.restr (fun i => ival ρ (τ i)) f)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) f) := by
      intro k f; rw [ihT _ _ _ _ _ (fun x => (hσ x).restr f)]; congr 1; funext x; exact (hσ x) k f
    have he : ∀ k (f : Hom k m), interp (cstFn S) univC TyCode (e.subst σ τ) k (ρ.restr f) (TEnv.restr γ f) =
        interp (cstFn S) univC TyCode e k (IEnv.restr (fun i => ival ρ (τ i)) f)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) f) := by
      intro k f; rw [ihe _ _ _ _ _ (fun x => (hσ x).restr f)]; congr 1; funext x; exact (hσ x) k f
    simp only [ihA _ _ _ _ _ hσ, ival.subst, hT, he]
  | glueEl φ e t a ihe iht iha =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    simp only [ihe _ _ _ _ _ hσ, iht _ _ _ _ _ hσ, iha _ _ _ _ _ hσ, ival.subst]
    have ht : ∀ k (f : Hom k m), interp (cstFn S) univC TyCode (t.subst σ τ) k (ρ.restr f) (TEnv.restr γ f) =
        interp (cstFn S) univC TyCode t k (IEnv.restr (fun i => ival ρ (τ i)) f)
          (TEnv.restr (fun x => sem S (σ x) m ρ γ) f) := by
      intro k f; rw [iht _ _ _ _ _ (fun x => (hσ x).restr f)]; congr 1; funext x; exact (hσ x) k f
    simp only [ht]
  | unglue φ e g ihe ihg =>
    intro m ρ γ σ τ hσ
    simp only [sem, interp, Tm.subst] at *
    rw [ihe _ _ _ _ _ hσ, ihg _ _ _ _ _ hσ, ival.subst]

end

end Model
