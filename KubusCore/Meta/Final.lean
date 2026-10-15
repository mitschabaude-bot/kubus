import KubusCore.Meta.SigWk
import KubusCore.Meta.ConBnd
import KubusCore.Meta.HcompCon

/-!
# Metatheory: the spec and the minimal judgments agree on well-formed signatures

`ContractaTyped` (the boundary rule `conBnd`) holds for every well-formed signature, by strong
induction on the signature: a boundary's type equations are checked in the prefix before its
inductive type, where the spec's judgments are minimal ones by the induction hypothesis. Hence
`spec_to_minimal` needs no hypothesis beyond `WfSig`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- Generation for constructors: the premises of the `con` rule at the natural type
`data d ps`, followed by conversions. -/
theorem gen_conF {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {d c ps args rs}
    (ht : s = .con d c ps args rs) :
    IntroTy S Ψ Φ Γ (con d c ps args rs) (data d ps) ∧ TyChainC S Ψ Φ Γ (data d ps) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨hI, ch⟩ := gen_conF h0 ht
    exact ⟨hI, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨hI, ch⟩ := gen_conF h2 ht
    exact ⟨hI.restrict hs he, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨hI, ch⟩ := gen_conF h1 ht
    exact ⟨hI, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con h0 h1 h2 h3 h4 h5 h6 h7 => by cases ht; exact ⟨⟨rfl, _, _, h0, h1, h2, h3, h4, h5, h6, h7⟩, .refl _⟩
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem contractaTyped_of (hW : WfSig S)
    (htr : ∀ (d : Nat) (D : DataDecl), S[d]? = some (.data D) →
      ∀ {Ψ Φ Γ t u A}, EqTm (S.take d) Ψ Φ Γ t u A → EqTm0 S Ψ Φ Γ t u A)
    (htr' : ∀ (d : Nat) (D : DataDecl), S[d]? = some (.data D) →
      ∀ {Ψ Φ Γ t A}, HasTy (S.take d) Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A) :
    ContractaTyped S where
  hcompCon := fun h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    hcompCon_of (sigClosed_of_wfSig hW) hW (htr' _ _ h0) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  transpCon := fun hD hne hC hps hargs htele hL hφ hc hI hX hl r tb ch =>
    transpCon_of (sigClosed_of_wfSig hW) hW (htr' _ _ hD) hD hne hC hps hargs htele hL hφ hc hI hX hl r tb ch
  conBnd := fun hD hC hk hent hps hargs h => by
    obtain ⟨⟨_, D', C', hD', hC', _, hdata, hpt, hat, hrs, hrsc⟩, ch⟩ := gen_conF h rfl
    rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
    exact ch.transport (conBnd_typed hW (htr _ _ hD) hD hC hk hent hps hargs hdata hpt hat hrs hrsc)

/-- Every well-formed signature has typed definitions and typed contracta. -/
theorem wf_typed : ∀ (n : Nat) (S : Sig), S.length = n → WfSig S → SigTyped0 S ∧ ContractaTyped S := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S hn hS
    have hpre : ∀ k, k < S.length → SigTyped0 (S.take k) ∧ ContractaTyped (S.take k) := fun k hk =>
      ih k (by omega) (S.take k) (by simp [List.length_take]; omega) (wfSig_take hS k)
    have hC : ContractaTyped S := contractaTyped_of hS
      (fun d D hD {Ψ Φ Γ t u A} e => by
        have hd : d < S.length := (List.getElem?_eq_some_iff.1 hD).1
        obtain ⟨hT', hC'⟩ := hpre d hd
        have hinc : ∀ (j : Nat) (e : Entry), (S.take d)[j]? = some e → S[j]? = some e :=
          fun j e h => (getElem?_take_some h).2
        exact sigwk_eq hinc (spec_to_minimal_eq_of (wfSig_take hS d) hT' hC' e))
      (fun d D hD {Ψ Φ Γ t A} e => by
        have hd : d < S.length := (List.getElem?_eq_some_iff.1 hD).1
        obtain ⟨hT', hC'⟩ := hpre d hd
        have hinc : ∀ (j : Nat) (e : Entry), (S.take d)[j]? = some e → S[j]? = some e :=
          fun j e h => (getElem?_take_some h).2
        exact sigwk_ty hinc (spec_to_minimal_of (wfSig_take hS d) hT' hC' e))
    refine ⟨sigTyped0_of_wfSig n S hn hS fun k => ?_, hC⟩
    by_cases hk : k < S.length
    · exact (hpre k hk).2
    · rw [List.take_of_length_le (by omega)]; exact hC

/-- The spec's typing judgment adds nothing to the minimal one. -/
theorem spec_to_minimal (hS : WfSig S) {Ψ Φ Γ t A} (h : HasTy S Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ t A :=
  spec_to_minimal_of hS (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2 h

theorem spec_to_minimal_eq (hS : WfSig S) {Ψ Φ Γ t u A} (h : EqTm S Ψ Φ Γ t u A) : EqTm0 S Ψ Φ Γ t u A :=
  spec_to_minimal_eq_of hS (wf_typed _ S rfl hS).1 (wf_typed _ S rfl hS).2 h

/-! ## The minimal statement -/

mutual
theorem bndTyped_of0 {m ψ Γ C Γp lvl ctors d np} :
    ∀ t, Ctor.bndTyped0 S m ψ Γ C Γp lvl ctors d np t → Ctor.bndTyped S m ψ Γ C Γp lvl ctors d np t
  | .con _ c' ps as _, h => by
    unfold Ctor.bndTyped0 at h; unfold Ctor.bndTyped
    split at h
    · rename_i C' hc; rw [hc]; exact bndTypedArgs_of0 _ _ _ _ _ h
    · rename_i hc; rw [hc]; trivial
  | .var .., _ | .const .., _ | .univ .., _ | .pi .., _ | .lam .., _ | .app .., _ | .sigma .., _
  | .pair .., _ | .fst .., _ | .snd .., _ | .path .., _ | .plam .., _ | .papp .., _ | .ipi .., _
  | .split .., _ | .abort, _ | .transp .., _ | .hcomp .., _ | .glue .., _ | .glueEl .., _
  | .unglue .., _ | .tnil, _ | .tcons .., _ | .data .., _ | .elim .., _ => by
    simp [Ctor.bndTyped]
theorem bndTypedArgs_of0 {m ψ Γ C Γp lvl ctors d np} (C' : Ctor) (ps : Tm) :
    ∀ (k : Nat) (prev : List Tm) (t : Tm), Ctor.bndTypedArgs0 S m ψ Γ C Γp lvl ctors d np C' ps k prev t →
      Ctor.bndTypedArgs S m ψ Γ C Γp lvl ctors d np C' ps k prev t
  | k, prev, .tcons a as, h => by
    unfold Ctor.bndTypedArgs0 at h; unfold Ctor.bndTypedArgs
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨fun j T ha hr hT => let ⟨x, y, e⟩ := h1 j T ha hr hT; ⟨x, y, toFull_eq e⟩,
      fun hr => bndTyped_of0 a (h2 hr), bndTypedArgs_of0 C' ps (k + 1) (a :: prev) as h3⟩
  | _, _, .var .., _ | _, _, .const .., _ | _, _, .univ .., _ | _, _, .pi .., _ | _, _, .lam .., _
  | _, _, .app .., _ | _, _, .sigma .., _ | _, _, .pair .., _ | _, _, .fst .., _ | _, _, .snd .., _
  | _, _, .path .., _ | _, _, .plam .., _ | _, _, .papp .., _ | _, _, .ipi .., _ | _, _, .split .., _
  | _, _, .abort, _ | _, _, .transp .., _ | _, _, .hcomp .., _ | _, _, .glue .., _
  | _, _, .glueEl .., _ | _, _, .unglue .., _ | _, _, .tnil, _ | _, _, .con .., _
  | _, _, .data .., _ | _, _, .elim .., _ => by simp [Ctor.bndTypedArgs]
end

theorem wfSig_of_wfSig0 (h : WfSig0 S) : WfSig S := by
  refine ⟨fun k t A hk => ?_, fun k D hk => ?_⟩
  · obtain ⟨h1, h2, ⟨l, h3⟩, h4⟩ := h.1 k t A hk
    exact ⟨h1, h2, ⟨l, toFull_ty h3⟩, toFull_ty h4⟩
  · obtain ⟨hl, hp, hc⟩ := h.2 k D hk
    refine ⟨hl, fun j A hj => ?_, fun c C hC => ?_⟩
    · obtain ⟨a, b, e⟩ := hp j A hj
      exact ⟨a, b, e.elim (fun e => .inl (toFull_ty e)) .inr⟩
    · obtain ⟨ha, hb, ho⟩ := hc c C hC
      refine ⟨fun k A hk => ?_, fun k ψ b hk => ?_, ho⟩
      · obtain ⟨a1, a2, a3, a4, a5⟩ := ha k A hk
        exact ⟨a1, a2, a3, toFull_ty a4, toFull_ty a5⟩
      · obtain ⟨b1, b2, b3, b4, b5⟩ := hb k ψ b hk
        exact ⟨b1, b2, b3, toFull_ty b4, bndTyped_of0 _ b5⟩

/-- Consistency of the minimal judgments follows from consistency of the spec. -/
theorem consistent0_of (h : Consistent) : Consistent0 :=
  fun S t hS ht => h S t (wfSig_of_wfSig0 hS) (toFull_ty ht)

/-- Over a signature that is well-formed in the spec's sense (e.g. one the kernel accepts),
a closed term of `(A : U₀) → A` in the minimal judgments would be one in the spec. -/
theorem no_bot0_of (h : Consistent) {S : Sig} (hS : WfSig S) (t : Tm) :
    ¬ HasTy0 S 0 .one [] t (.pi (.univ 0) (.var 0)) :=
  fun ht => h S t hS (toFull_ty ht)

end KubusCore.Meta
