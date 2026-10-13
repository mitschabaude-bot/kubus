import Model.Canon.KanAll
import Model.Canon.Statement

/-!
# Canonicity: the definitions and inductive types of the signature are computable, and the final
theorem
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The interval substitution out of the empty interval context. -/
def ISub.none (k : ℕ) : ISub k 0 := ⟨fun _ => .zero, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem natural_var (x : ℕ) : Natural S (.var x) k (idEnv k) (γ0 k) := fun _ _ => rfl

theorem natural_lsub_nil (y : ℕ) : Natural S (lsub [] 0 y) k (idEnv k) (γ0 k) := natural_var _

/-- The computable substitution out of the empty context. -/
def CSub.nil (S : Sig) (k : ℕ) : CSub S 0 .one [] k where
  σ := ISub.none k
  γ := lsub [] 0
  face := ent_refl _
  nat _ := natural_var _
  look x A h := by simp [Ctx.lookup] at h

variable (hW : WfSig S)
include hW

theorem constsLt_of_take {n : ℕ} (hn : n ≤ S.length) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t A : Tm}
    (h : HasTy (S.take n) Ψ Φ Γ t A) : t.ConstsLt n := by
  have := (sound_ty (sigOK_of_wfSig _ (S.take n) rfl (wfSig_take hW n)) h).2.1
  simpa [List.length_take, Nat.min_eq_left hn] using this

/-- The parameters of an inductive type, computable at their types, as a computable substitution
out of the parameter context. -/
theorem csub_params {D : DataDecl} (hcl : ∀ (j : ℕ) (A : Tm), D.params[j]? = some A → A.closedB j 0 = true)
    {ps : List Tm} (hpl : ps.length = D.params.length)
    (hps : ∀ j (hj : j < ps.length) (hj' : j < D.params.length), RE S k (D.params[j].substList (ps.take j).reverse) ps[j]) :
    ∀ j, j ≤ D.params.length → ∃ c : CSub S 0 .one (D.paramCtx j) k, c.γ = lsub (ps.take j).reverse 0 ∧ c.σ = ISub.none k
  | 0, _ => ⟨by simpa [DataDecl.paramCtx] using CSub.nil S k, by simp [DataDecl.paramCtx]; rfl, by
      simp [DataDecl.paramCtx]; rfl⟩
  | j + 1, hj => by
    obtain ⟨c, hcγ, hcσ⟩ := csub_params hcl hpl hps j (by omega)
    have hjp : j < D.params.length := by omega
    have hA := hps j (by omega) hjp
    have hcl' : (D.params[j]).closedB ((ps.take j).reverse).length 0 = true := by
      have := hcl j _ (List.getElem?_eq_getElem hjp); simpa [Nat.min_eq_left (show j ≤ ps.length by omega)] using this
    have hA' : RE S k ((D.params[j]).subst c.γ c.σ.τ) ps[j] := by
      rw [hcγ, subst_lsub_closed hcl']; exact hA
    rw [paramCtx_succ D hjp]
    refine ⟨c.ext hW _ _ hA', ?_, hcσ⟩
    show consT ps[j] c.γ = _
    rw [hcγ, consT_lsub]
    congr 1
    rw [List.take_add_one, List.getElem?_eq_getElem (show j < ps.length by omega)]
    simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]

/-- The parameters and earlier point arguments of a constructor, computable at their types, as a
computable substitution out of the point context. -/
theorem csub_points {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ps args : List Tm} (hpl : ps.length = D.params.length)
    (hps : ∀ j (hj : j < ps.length) (hj' : j < D.params.length), RE S k (D.params[j].substList (ps.take j).reverse) ps[j])
    (hlen : args.length ≤ C.args.length)
    (hargs : ∀ i (hi : i < args.length), C.isRec i = false →
      RE S k ((C.argTy d D.params.length i).substList ((args.take i).reverse ++ ps.reverse)) args[i]) :
    ∀ i, i ≤ args.length → ∃ c' : CSub S 0 .one (D.pointCtx d C i) k,
      c'.γ = lsub (ptL C args ps.reverse i) 0 ∧ c'.σ = ISub.none k
  | 0, _ => by
    obtain ⟨c', hγ, hσ⟩ := csub_params hW (params_closed (sigClosed_of_wfSig hW) hD |> fun h j A hA => by
      simpa using h j A hA) hpl hps D.params.length (Nat.le_refl _)
    have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
    rw [hpc]
    refine ⟨c', ?_, hσ⟩
    rw [hγ, List.take_of_length_le (by omega)]; rfl
  | i + 1, hi => by
    obtain ⟨c', hγ, hσ⟩ := csub_points hD hC hpl hps hlen hargs i (by omega)
    rw [pointCtx_succ]
    by_cases hr' : C.isRec i = true
    · rw [if_pos hr']
      refine ⟨c', ?_, hσ⟩
      rw [hγ]; simp [ptL, hr']
    · have hr : C.isRec i = false := by simpa using hr'
      rw [if_neg hr']
      have hiC : i < C.args.length := by omega
      obtain ⟨A0, hA0⟩ := point_of_not_rec hiC hr
      have hAk : C.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
      have hA : RE S k (((C.argTy d D.params.length i).ren (C.pointRen i) id).subst c'.γ c'.σ.τ) args[i] := by
        rw [hγ, hAk, pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 c'.σ.τ]
        have := hargs i (by omega) hr
        rwa [hAk] at this
      refine ⟨c'.ext hW _ _ hA, ?_, hσ⟩
      show consT args[i] c'.γ = _
      rw [hγ, consT_lsub]
      simp only [ptL, hr, Bool.false_eq_true, if_false, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < args.length by omega), Option.getD_some]
      rfl

/-- The definitions and inductive types of a well-formed signature are computable, by induction
on their index. -/
theorem hyp_all (hGC : GlueCompat S) : ∀ n, n ≤ S.length → Hyp S n
  | 0, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun d hd => absurd hd (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hH := hyp_all hGC n (by omega)
    refine ⟨fun i hi t A hiS k' => ?_, fun d hd D hD c C hC k' ps args hpl hps hlt hr hargs => ?_⟩
    · by_cases hin : i < n
      · exact hH.defn i hin t A hiS k'
      obtain rfl : i = n := by omega
      obtain ⟨htc, hAc, -, hty⟩ := hW.1 i t A hiS
      have ht0 := htr_of hW i hty
      have hcl := constsLt_of_take hW (by omega) hty
      have := fund_ty hW id hH hGC ht0 (KOK.of_constsLt (kanOracle hW hGC) hcl) k' (CSub.nil S k')
      rwa [closed_subst_id hAc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _)),
        closed_subst_id htc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _))] at this
    · by_cases hdn : d < n
      · exact hH.data d hdn D hD c C hC k' ps args hpl hps hlt hr hargs
      obtain rfl : d = n := by omega
      obtain ⟨A0, hA0⟩ := point_of_not_rec hlt hr
      obtain ⟨c', hγ, -⟩ := csub_points hW hD hC hpl hps hlt.le hargs args.length (Nat.le_refl _)
      have hP := pt_typed hW (htr_of hW d) hD hC hA0
      have hPc := constsLt_of_take hW (by omega) (((hW.2 d D hD).2.2 c C hC).1 _ A0 hA0).2.2.2.2
      have := fund_ty hW id hH hGC hP (KOK.of_constsLt (kanOracle hW hGC) hPc) k' c'
      rw [hγ, pt_inst hW hD hC hA0 (Nat.le_refl _) (by simp [hpl]) 0 c'.σ.τ, List.take_length] at this
      have hAk : C.argTy d D.params.length args.length = A0 := by simp [Ctor.argTy, hA0]
      rw [hAk]
      exact ((RE_univ_iff hW).1 this).2.2

end

end Model.Canon
