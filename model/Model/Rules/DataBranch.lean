import Model.Rules.DataLemmas
import Model.Rules.CompLemmas

/-!
# Branches of the eliminator: iterated applications

Peeling the Π- and interval-Π-types of a branch type by applying to arguments.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- Extend a term environment by a list of values, the first one innermost. -/
def TEnv.consL (γ : ℕ → V) (as : List V) : ℕ → V := as.foldl TEnv.cons γ

/-- Extend an interval environment by a list of points, the first one innermost. -/
def IEnv.consL (ρ : IEnv m) (rs : List (DM m)) : IEnv m := rs.foldl IEnv.cons ρ

theorem TEnv.consL_kv {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x)) : ∀ {as : List V}, (∀ a ∈ as, IsKV m a) →
    ∀ x, IsKV m (TEnv.consL γ as x)
  | [], _, x => hγ x
  | a :: as, h, x => by
    simp only [TEnv.consL, List.foldl_cons]
    exact TEnv.consL_kv (γ := TEnv.cons γ a) (fun y => by cases y <;> simp [TEnv.cons, hγ, h a List.mem_cons_self])
      (fun b hb => h b (List.mem_cons_of_mem _ hb)) x

/-- Applying a function of a Π-type to arguments of the domains. -/
theorem apps_foldr_pi {ρ : IEnv m} : ∀ (Ts : List Tm) (inner : Tm) (γ : ℕ → V) (f : V) (as : List V),
    (∀ x, IsKV m (γ x)) → TyOK S (Ts.foldr Tm.pi inner) m ρ γ →
    f ∈ El (sem S (Ts.foldr Tm.pi inner) m ρ γ) (Hom.id m) → ∀ (hl : as.length = Ts.length),
    (∀ i (hi : i < as.length), as[i] ∈ El (sem S (Ts[i]'(by omega)) m ρ (TEnv.consL γ (as.take i))) (Hom.id m)) →
    TyOK S inner m ρ (TEnv.consL γ as) ∧ appsV m f as ∈ El (sem S inner m ρ (TEnv.consL γ as)) (Hom.id m)
  | [], inner, γ, f, as, _, hty, hf, hl, _ => by
    cases as with
    | nil => exact ⟨hty, hf⟩
    | cons => simp at hl
  | T :: Ts, inner, γ, f, as, hγ, hty, hf, hl, has => by
    cases as with
    | nil => simp at hl
    | cons a as =>
      simp only [List.foldr_cons] at hty hf
      obtain ⟨hAkv, l, hl', hV, hWF⟩ := hty.pi_at
      rw [sem_pi hAkv] at hV hWF hf
      obtain ⟨-, hfam, -⟩ := WF.pi_inv hAkv (isKV_famV _ _) hWF
      have ha : a ∈ El (sem S T m ρ γ) (Hom.id m) := by simpa using has 0 (by simp)
      have hρ : ρ.restr (Hom.id m) = ρ := IEnv.restr_id ρ
      have hγ' : TEnv.restr γ (Hom.id m) = γ := TEnv.restr_id_of_kv hγ
      have hfa : appV m f a ∈ El (sem S (Ts.foldr Tm.pi inner) m ρ (TEnv.cons γ a)) (Hom.id m) := by
        rw [El_piC, res_id hAkv, res_id (isKV_famV _ _)] at hf
        have := appV_mem_piElSet hf ha
        rwa [apZ_dat_famV _ _ _ ha, hρ, hγ'] at this
      have hty' : TyOK S (Ts.foldr Tm.pi inner) m ρ (TEnv.cons γ a) := by
        have hw := hfam m (Hom.id m) a ha
        rw [apZ_dat_famV _ _ _ ha, hρ, hγ'] at hw
        refine ⟨l, hl', Or.inl ⟨hw, ?_⟩⟩
        have := Vt_below (below_piC_fam _ _ (isKV_famV _ _) a ⟨_, by rw [dat_famV]; exact mem_fnZ.2 ⟨_, ha, rfl⟩⟩) hV
        rwa [apZ_dat_famV _ _ _ ha, hρ, hγ'] at this
      have hakv : IsKV m a := (WF.pi_inv hAkv (isKV_famV _ _) hWF).1.fib.elKV _ _ _ ha
      have := apps_foldr_pi Ts inner (TEnv.cons γ a) (appV m f a) as
        (fun y => by cases y <;> simp [TEnv.cons, hγ, hakv]) hty' hfa (by simpa using hl)
        (fun i hi => by simpa [TEnv.consL] using has (i + 1) (by simp; omega))
      simpa [TEnv.consL, appsV] using this

/-- `n` interval-Π-types around `inner`. -/
def ipiN (k : ℕ) (inner : Tm) : Tm := (List.range k).foldl (fun acc _ => Tm.ipi acc) inner

theorem ipiN_succ (k : ℕ) (inner : Tm) : ipiN (k + 1) inner = Tm.ipi (ipiN k inner) := by
  simp [ipiN, List.range_succ, List.foldl_append]

/-- Applying an element of interval-Π-types to points. -/
theorem papps_ipiN : ∀ (rs : List (DM m)) (inner : Tm) (ρ : IEnv m) (γ : ℕ → V) (f : V),
    (∀ x, IsKV m (γ x)) → TyOK S (ipiN rs.length inner) m ρ γ →
    f ∈ El (sem S (ipiN rs.length inner) m ρ γ) (Hom.id m) →
    TyOK S inner m (IEnv.consL ρ rs) γ ∧ pappsV m f rs ∈ El (sem S inner m (IEnv.consL ρ rs) γ) (Hom.id m)
  | [], inner, ρ, γ, f, _, hty, hf => ⟨hty, hf⟩
  | r :: rs, inner, ρ, γ, f, hγ, hty, hf => by
    simp only [List.length_cons] at hty hf
    rw [ipiN_succ] at hty hf
    obtain ⟨hN, hL, hsem, l, hl, hV, hW⟩ := hty.ipi_at
    rw [hsem, mem_El_ipiC hL] at hf
    obtain ⟨p, hp, rfl⟩ := hf
    have hfr : pappV m (pathOfLine m p) r ∈ El (sem S (ipiN rs.length inner) m (ρ.cons r) γ) (Hom.id m) := by
      rw [pappV_pathOfLine, line_endpt hγ hN r, El_res, Hom.comp_id]
      have := hW.fib.elRes _ _ _ hp m (Hom.endpt m r)
      rwa [Hom.id_comp] at this
    have hty' : TyOK S (ipiN rs.length inner) m (ρ.cons r) γ := by
      refine ⟨l, hl, Or.inl ⟨?_, ?_⟩⟩
      · rw [line_endpt hγ hN r]; exact hW.res _
      · rw [line_endpt hγ hN r]; exact res_mem_Vt hV _
    have := papps_ipiN rs inner (ρ.cons r) γ _ hγ hty' hfr
    simpa [IEnv.consL, pappsV] using this

end

end Model
