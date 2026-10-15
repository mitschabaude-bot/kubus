import Model.DataInv
import KubusCore.Boundary

/-!
# Syntactic boundary agreement in the constructor algebra

The boundary check implies overlap agreement for arbitrary values, independently of typing. The induction on constructor indices proves overlap agreement and soundness of constructor normalization together.
-/

set_option autoImplicit false

namespace Model.Boundary

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

mutual
def read (F : ℕ → List V → List (DM n) → V) (γ : ℕ → V) (ρ : IEnv n) : Tm → V
  | .var j => γ j
  | .con _ c _ as rs => F c (readArgs F γ ρ as) (rs.map (ival ρ))
  | _ => junkV n
def readArgs (F : ℕ → List V → List (DM n) → V) (γ : ℕ → V) (ρ : IEnv n) : Tm → List V
  | .tcons a as => read F γ ρ a :: readArgs F γ ρ as
  | _ => []
end

theorem read_kv {F : ℕ → List V → List (DM n) → V} (hF : ∀ c as rs, IsKV n (F c as rs))
    {γ : ℕ → V} (hγ : ∀ j, IsKV n (γ j)) (ρ : IEnv n) (t : Tm) : IsKV n (read F γ ρ t) := by
  cases t <;> first | exact hγ _ | exact hF _ _ _ | exact isKV_junkV

theorem read_ofList (F : ℕ → List V → List (DM n) → V) (γ : ℕ → V) (ρ : IEnv n) (as : List Tm) :
    readArgs F γ ρ (Tm.ofList as) = as.map (read F γ ρ) := by
  induction as <;> simp_all [Tm.ofList, readArgs]

theorem read_eq_evalBnd (F : ℕ → List V → List (DM n) → V) (args : List V) (rs : List (DM n)) (t : Tm) :
    read F (fun j => res (Hom.id n) (args.reverse.getD j ∅)) (renv rs) t = evalBnd F args rs t ∧
    readArgs F (fun j => res (Hom.id n) (args.reverse.getD j ∅)) (renv rs) t = evalBndList F args rs t := by
  induction t <;> simp_all [read, readArgs, evalBnd, evalBndList]

theorem read_eval (F G : ℕ → List V → List (DM n) → V) (γ : ℕ → V) (ρ : IEnv n)
    (H : ℕ → List Tm → List I → Tm)
    (hH : ∀ c as rs, read F γ ρ (H c as rs) = G c (as.map (read F γ ρ)) (rs.map (ival ρ)))
    (σ : ℕ → Tm) (τ : ℕ → I) (t : Tm) :
    read F γ ρ (KubusCore.Boundary.eval H σ τ t) =
      read G (fun j => read F γ ρ (σ j)) (fun i => ival ρ (τ i)) t ∧
    (KubusCore.Boundary.evalArgs H σ τ t).map (read F γ ρ) =
      readArgs G (fun j => read F γ ρ (σ j)) (fun i => ival ρ (τ i)) t := by
  induction t with
  | var j => exact ⟨rfl, rfl⟩
  | con d c ps as rs _ ihas =>
    refine ⟨?_, rfl⟩
    simp only [KubusCore.Boundary.eval, read, hH, ihas.2, List.map_map]
    congr 1
    exact List.map_congr_left fun r _ => ival.subst ρ τ r
  | tcons a as iha ihas =>
    exact ⟨rfl, by simp only [KubusCore.Boundary.evalArgs, List.map_cons, readArgs, iha.1, ihas.2]⟩
  | _ => exact ⟨rfl, rfl⟩

theorem inear_ival (ρ : IEnv n) : ∀ {rs ss : List I}, KubusCore.Boundary.INear rs ss →
    rs.map (ival ρ) = ss.map (ival ρ)
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => False.elim h
  | r :: rs, s :: ss, h => by
    simp only [List.map_cons]
    rw [ival.congr_eq h.1 ρ, inear_ival ρ h.2]

theorem read_near (F : ℕ → List V → List (DM n) → V) (γ : ℕ → V) (ρ : IEnv n) :
    ∀ (t u : Tm), KubusCore.Boundary.Near t u →
      read F γ ρ t = read F γ ρ u ∧ readArgs F γ ρ t = readArgs F γ ρ u := by
  intro t
  induction t with
  | var x =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    subst h; exact ⟨rfl, rfl⟩
  | tnil =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    exact ⟨rfl, rfl⟩
  | tcons a as iha ihas =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    exact ⟨rfl, by simp only [readArgs, (iha _ h.1).1, (ihas _ h.2).2]⟩
  | con d c ps as rs _ ihas =>
    intro u h; cases u <;> simp only [KubusCore.Boundary.Near] at h
    obtain ⟨rfl, rfl, rfl, ha, hrs⟩ := h
    refine ⟨?_, rfl⟩
    simp only [read, (ihas _ ha).2]
    congr 1
    exact inear_ival ρ hrs
  | _ => intro u h; cases u <;> cases h

/-- Agreement of all boundary clauses of constructor `c`, with arbitrary arguments. -/
def RawOvl (ctors : List Ctor) (c : ℕ) : Prop :=
  ∀ ψ b ψ' b', (ψ, b) ∈ (ctors.getD c default).bnd → (ψ', b') ∈ (ctors.getD c default).bnd →
    ∀ (n : ℕ) (args : List V) (rs : List (DM n)),
      (ival (renv rs) ψ).holds → (ival (renv rs) ψ').holds →
      evalBnd (conBefore ctors c n) args rs b = evalBnd (conBefore ctors c n) args rs b'

theorem con_eq_bnd {ctors : List Ctor} {c : ℕ} (ho : RawOvl ctors c) {ψ : I} {b : Tm}
    (hb : (ψ, b) ∈ (ctors.getD c default).bnd) (args : List V) (rs : List (DM n))
    (hh : (ival (renv rs) ψ).holds) :
    conV ctors n c args rs = evalBnd (conBefore ctors c n) args rs b := by
  apply (isKV_conV _ _ _ _).ext (isKV_evalBnd (isKV_conBefore _ _ _) _ _ _)
  intro k f
  rw [conV_eq, dat_mkKV]
  have hf : ((ival (renv rs) ψ).restr f).holds := hh.restr f
  obtain ⟨⟨ψ', b'⟩, hb'⟩ := bndAtMap_isSome hb hf
  rw [hb']
  obtain ⟨hm', hh'⟩ := bndAtMap_some hb'
  change dat (evalBnd (conBefore ctors c n) args rs b') k f = _
  rw [← here_res, ← here_res, res_evalBnd_conBefore, res_evalBnd_conBefore]
  congr 1
  exact ho ψ' b' ψ b hm' hb k (args.map (res f)) (rs.map (·.restr f))
    (by rwa [← ival_renv_restr]) (by rwa [← ival_renv_restr])

/-- The constructor normalizer denotes the constructor applied to the denotations of its arguments. -/
def ConSound (ctors : List Ctor) (d : ℕ) (ps : Tm) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (γ : ℕ → V) (ρ : IEnv n), (∀ j, IsKV n (γ j)) → ∀ as rs,
    read (conV ctors n) γ ρ (KubusCore.Boundary.conNF ctors d ps c as rs) =
      conV ctors n c (as.map (read (conV ctors n) γ ρ)) (rs.map (ival ρ))

theorem args_env (F : ℕ → List V → List (DM n) → V) (hF : ∀ c as rs, IsKV n (F c as rs))
    (γ : ℕ → V) (hγ : ∀ j, IsKV n (γ j)) (ρ : IEnv n) (as : List Tm) :
    (fun j => read F γ ρ (as.reverse.getD j .abort)) =
      (fun j => res (Hom.id n) ((as.map (read F γ ρ)).reverse.getD j ∅)) := by
  funext j
  rw [← List.map_reverse]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : as.reverse[j]? with
  | none => simp [read, res, junkV, dat_empty0]
  | some a => simp only [Option.map_some, Option.getD_some]; exact (res_id (read_kv hF hγ ρ a)).symm

theorem dims_env (ρ : IEnv n) (rs : List I) :
    (fun i => ival ρ (rs.reverse.getD i .zero)) = renv (rs.map (ival ρ)) := by
  funext i
  simp only [renv, ← List.map_reverse, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rs.reverse[i]? <;> rfl

theorem con_sound {ctors : List Ctor} {d c : ℕ} {ps : Tm} (ho : RawOvl ctors c)
    (ih : ∀ c' < c, ConSound ctors d ps c') : ConSound ctors d ps c := by
  intro n γ ρ hγ as rs
  have hH : ∀ c' xs ss,
      read (conV ctors n) γ ρ
        (if c' < c then KubusCore.Boundary.conNF ctors d ps c' xs ss else .abort) =
      conBefore ctors c n c' (xs.map (read (conV ctors n) γ ρ)) (ss.map (ival ρ)) := by
    intro c' xs ss
    by_cases hc' : c' < c
    · simp only [hc', ↓reduceIte, conBefore, ↓reduceDIte]
      exact ih c' hc' n γ ρ hγ xs ss
    · simp [hc', conBefore, read]
  rw [KubusCore.Boundary.conNF]
  split
  · simp only [read, read_ofList]
  · rename_i ψ b hb
    have hm := List.mem_of_find?_eq_some hb
    have hh : I.Entails .one (ψ.subst fun i => rs.reverse.getD i .zero) := by
      simpa using List.find?_some hb
    have hhold := entails_holds (ρ := ρ) hh (show (ival ρ .one).holds from rfl)
    rw [ival.subst, dims_env] at hhold
    have he := (read_eval (conV ctors n) (conBefore ctors c n) γ ρ
      (fun c' xs ss => if c' < c then KubusCore.Boundary.conNF ctors d ps c' xs ss else .abort) hH
      (fun j => as.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) b).1
    rw [args_env _ (fun c xs ss => isKV_conV ctors c xs ss) γ hγ ρ as, dims_env,
      (read_eq_evalBnd _ _ _ b).1] at he
    exact he.trans (con_eq_bnd ho hm _ _ hhold).symm

theorem face_sub_env (ρ : IEnv n) (α : I.Face)
    (hα : ∀ l ∈ α, ρ l.1 = ival ρ (I.ofDir l.2)) :
    (fun i => ival ρ (KubusCore.Boundary.faceSub α i)) = ρ := by
  funext i
  induction α with
  | nil => rfl
  | cons l α ih =>
    obtain ⟨j, e⟩ := l
    simp only [KubusCore.Boundary.faceSub]
    by_cases hij : i = j
    · subst i; rw [if_pos rfl]; exact (hα (j, e) (List.mem_cons_self ..)).symm
    · rw [if_neg hij]; exact ih (fun l hl => hα l (List.mem_cons_of_mem _ hl))

theorem holding_face {ρ : IEnv n} {φ : I} (hh : (ival ρ φ).holds) :
    ∃ α ∈ φ.faces, ∀ l ∈ α, ρ l.1 = ival ρ (I.ofDir l.2) := by
  obtain ⟨α, hα, hl⟩ := (Cof.eval_eq_one_iff_faces
    (fun j => (ρ j).defn.isK3 (Pt.allA_isK3 n)) φ).1 hh
  refine ⟨α, hα, fun l hl' => holds_lit ?_⟩
  have h := hl l hl'
  obtain ⟨j, e⟩ := l
  change (I.lit j e).eval (fun i => (ρ i).fn (Pt.allA n)) = I.M4.one
  cases e <;> simp_all [Cof.LitHolds, I.lit, I.eval]

theorem agree_sound {ctors : List Ctor} {d np nargs c : ℕ} {φ : I} {b b' : Tm}
    (ih : ∀ c' < c, ∀ ps, ConSound ctors d ps c')
    (ha : KubusCore.Boundary.Agree ctors d np nargs c φ b b')
    (args : List V) (rs : List (DM n)) (hh : (ival (renv rs) φ).holds) :
    evalBnd (conBefore ctors c n) args rs b = evalBnd (conBefore ctors c n) args rs b' := by
  let F := conV ctors n
  let γ := fun j => res (Hom.id n) (args.reverse.getD j ∅)
  let ρ := renv rs
  have hγ : ∀ j, IsKV n (γ j) := fun _ => isKV_res _ _
  obtain ⟨α, hα, hρα⟩ := holding_face hh
  have hH : ∀ c' xs ss,
      read F γ ρ (if c' < c then KubusCore.Boundary.conNF ctors d (Ctor.paramVars np nargs) c' xs ss else .abort) =
      conBefore ctors c n c' (xs.map (read F γ ρ)) (ss.map (ival ρ)) := by
    intro c' xs ss
    by_cases hc' : c' < c
    · simp only [hc', ↓reduceIte, conBefore, ↓reduceDIte]
      exact ih c' hc' _ n γ ρ hγ xs ss
    · simp [hc', conBefore, read, F]
  have hnf : ∀ t, read F γ ρ (KubusCore.Boundary.nf ctors d np nargs c α t) =
      evalBnd (conBefore ctors c n) args rs t := by
    intro t
    have he := (read_eval F (conBefore ctors c n) γ ρ _ hH Tm.var (KubusCore.Boundary.faceSub α) t).1
    change read F γ ρ (KubusCore.Boundary.nf ctors d np nargs c α t) = _ at he
    rw [face_sub_env ρ α hρα] at he
    exact he.trans (read_eq_evalBnd _ _ _ t).1
  rw [← hnf b, ← hnf b']
  exact (read_near F γ ρ _ _ (ha α hα)).1

theorem raw_ovl (ctors : List Ctor) (d np : ℕ)
    (ha : ∀ c C, ctors[c]? = some C → ∀ ψ b ψ' b', (ψ, b) ∈ C.bnd → (ψ', b') ∈ C.bnd →
      KubusCore.Boundary.Agree ctors d np C.args.length c (.and ψ ψ') b b') :
    ∀ c, RawOvl ctors c := by
  have hp : ∀ c, RawOvl ctors c ∧ ∀ ps, ConSound ctors d ps c := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      have ho : RawOvl ctors c := by
        intro ψ b ψ' b' hb hb' n args rs hψ hψ'
        cases hC : ctors[c]? with
        | none =>
          rw [List.getD_eq_getElem?_getD, hC] at hb
          change (ψ, b) ∈ ([] : List (I × Tm)) at hb
          cases hb
        | some C =>
          have hget := getD_ctors hC
          rw [hget] at hb hb'
          exact agree_sound (fun c' hc' => (ih c' hc').2) (ha c C hC ψ b ψ' b' hb hb')
            args rs (holds_and.2 ⟨hψ, hψ'⟩)
      exact ⟨ho, fun ps => con_sound ho (fun c' hc' => (ih c' hc').2 ps)⟩
  exact fun c => (hp c).1

end

end Model.Boundary
