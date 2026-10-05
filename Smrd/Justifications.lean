import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo
import Smrd.Conjuncts

/-!
# Justifications (Appendix A.3–A.5)

Justifications `j : (P, D) ⊢^δ w` of effectful events (Definition `def:justs`),
the forwarding relations (`def:fwd-rels`), closed relabel-equivalence
(`def:rel-eq`), and the generation of the justification set `𝕁` from
pre-justifications by the elaborations Value Assignment, Strengthening,
Forwarding, Write Elision, Lifting and Weakening (`def:gen-just`).

The stages `𝕁₀ ⊆ 𝕁₁ ⊆ …` of the paper are collapsed into one inductive
predicate `Generated`, whose derivations are the elements of `⋃ᵢ 𝕁ᵢ`.

## Representation choices

* The justified event `w` is a *copy* of an event of `𝔼`, carrying its own
  location and value expressions. The paper matches a copy to its event by
  control label; since elaborations change neither, we match it by the event
  id, which the copy keeps.
* `D` and the symbols of a set of events coincide, as symbols are the ids of
  the events introducing them (`symbols(D) = D` on symbol-introducing events).
* The environment `g = [val(e₂) ↦ val(e₁)]` of Forwarding replaces the
  expression `val(e₂)`, which for store-store forwarding is the value written
  and not a symbol (`Expr.replace`).
* The origins `e ∈ S` of Strengthening are required to be `⊑`-related to `w`
  strictly: a reflexive reading would put `(w, w)` into `DP` for an allocation
  constraining its own symbol.
-/

/-- A justification `j : (P, D) ⊢^δ w`. -/
structure Justification where
  P : Expr
  D : List EventId
  δ : FwdCtx
  w : Event
  deriving Repr

/-- A relabelling `Λ : Symbols ⇀ Symbols`. -/
abbrev Relabelling := Sym → Option Sym

/-- `⟦α⟧_Λ` -/
def Relabelling.app (Λ : Relabelling) (α : Sym) : Sym := (Λ α).getD α

/-- `Λ` is one-to-one on its domain. -/
def Relabelling.Injective (Λ : Relabelling) : Prop :=
  ∀ a b c, Λ a = some c → Λ b = some c → a = b

/-- The pre-justification of an effectful event, `𝕁₀`:
    `(valres(w), origin x ∪ origin e) ⊢^{(∅,∅)} (w : W x e)`,
    `(valres(a), origin e) ⊢^{(∅,∅)} (a : A α e)`, and
    `(valres(d), origin e) ⊢^{(∅,∅)} (d : D e)`. The symbol an allocation
    introduces is not among its dependencies. -/
def preJust (w : Event) : Option Justification :=
  match w.kind with
  | .write _ x e => some ⟨w.valres, x.syms ++ e.syms, .empty, w⟩
  | .alloc _ e   => some ⟨w.valres, e.syms, .empty, w⟩
  | .dealloc e   => some ⟨w.valres, e.syms, .empty, w⟩
  | _            => none

namespace EventStructure

variable (es : EventStructure)

/-! ## Forwarding relations (Definition `def:fwd-rels`) -/

/-- `e₁ -F'_j→ e₂ ≜ e₁ ∈ pred_δ(e₂, P) ∧ loc(e₁) ≡_{P ∧ ψ_δ} loc(e₂)` -/
def fwdBase (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.pred j.δ e₂ j.P.holds e₁ ∧
    ∃ ev₁ ev₂ l₁ l₂, es.ev e₁ = some ev₁ ∧ es.ev e₂ = some ev₂ ∧
      ev₁.loc = some l₁ ∧ ev₂.loc = some l₂ ∧
      EquivUnder (Pred.and j.P.holds (j.δ.psi es)) l₁ l₂

/-- `e₁ -F_j→ e₂`: store forwarding `W × R_rlx`, store-store forwarding
    `W × W_rlx`, and load forwarding `R × R`. -/
def fwdRel (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.fwdBase j e₁ e₂ ∧
    ((es.cls Event.isWrite e₁ ∧ es.cls Event.isRlxR e₂) ∨
     (es.cls Event.isWrite e₁ ∧ es.cls Event.isRlxW e₂) ∨
     (es.cls Event.isRead e₁ ∧ es.cls Event.isRead e₂))

/-- `e₁ -WE_j→ e₂`, on pairs of writes. -/
def weRel (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.fwdBase j e₁ e₂ ∧ es.cls Event.isWrite e₁ ∧ es.cls Event.isWrite e₂

/-! ## Closed relabel-equivalence (Definition `def:rel-eq`) -/

/-- `P₁ : x₁ ≅^Λ_δ P₂ : x₂` on expressions:
    `∃ x. (⟦P₁ ⇒ x₁ = x⟧_Λ ∧ (P₂ ⇒ x₂ = x)) ≡_{ψ_δ} ⊤`. -/
def relabEqExpr (δ : FwdCtx) (Λ : Relabelling) (P₁ x₁ P₂ x₂ : Expr) : Prop :=
  ∃ x : Expr,
    EquivUnder (δ.psi es)
      (.and ((Expr.imp P₁ (.eq x₁ x)).rename Λ) (Expr.imp P₂ (.eq x₂ x))) Expr.tt

/-- Relabel equivalence of two events, by the shape of their actions. -/
def relabEq (δ : FwdCtx) (Λ : Relabelling) (P₁ : Expr) (e₁ : Event) (P₂ : Expr)
    (e₂ : Event) : Prop :=
  let locs := ∃ l₁ l₂, e₁.loc = some l₁ ∧ e₂.loc = some l₂ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂
  let vals := ∃ v₁ v₂, e₁.val = some v₁ ∧ e₂.val = some v₂ ∧ es.relabEqExpr δ Λ P₁ v₁ P₂ v₂
  if (e₁.isRead && e₂.isRead) || (e₁.isWrite && e₂.isWrite) || (e₁.isAlloc && e₂.isAlloc) then
    locs ∧ vals
  else if e₁.isDealloc && e₂.isDealloc then locs
  else if e₁.isFence && e₂.isFence then True
  else False

/-- `P₁ : e₁ ≅^Λ_δ* P₂ : e₂`, closed through `pred_δ`. The recursion
    descends along `≼`, which is well-founded on the finite event structures
    the semantics generates, so the inductive (least) reading is the intended
    one. -/
inductive ClosedRelabEq (δ : FwdCtx) (Λ : Relabelling) : Expr → Event → Expr → Event → Prop
  | mk {P₁ P₂ : Expr} {e₁ e₂ : Event} :
      es.relabEq δ Λ P₁ e₁ P₂ e₂ →
      ((∀ x, ¬ es.pred δ e₁.id P₁.holds x) ↔ (∀ x, ¬ es.pred δ e₂.id P₂.holds x)) →
      (∀ x₁ x₂ ev₁ ev₂, es.pred δ e₁.id P₁.holds x₁ → es.pred δ e₂.id P₂.holds x₂ →
        es.ev x₁ = some ev₁ → es.ev x₂ = some ev₂ → ClosedRelabEq δ Λ P₁ ev₁ P₂ ev₂) →
      ClosedRelabEq δ Λ P₁ e₁ P₂ e₂

/-! ## Generating justifications (Definition `def:gen-just`) -/

/-- `valres(e)` of an event id, `⊤` for an id with no event. -/
def valresOf (e : EventId) : Expr := ((es.ev e).map Event.valres).getD Expr.tt

/-- The predicate Strengthening produces, `P ∧ Q ∧ ⋀_{e ∈ S} valres(e)`. -/
def strPred (P Q : Expr) (S : List EventId) : Expr :=
  .and P (.and Q (Expr.conj (S.map es.valresOf)))

theorem strPred_holds {P Q : Expr} {S : List EventId} {f : Valuation}
    (h : (es.strPred P Q S).holds f) : P.holds f :=
  ((Expr.holds_and _ _ f).1 h).1

theorem syms_strPred {P Q : Expr} {S : List EventId} :
    ∀ α ∈ P.syms, α ∈ (es.strPred P Q S).syms :=
  fun _ h => List.mem_append_left _ h

theorem conjuncts_strPred {P Q : Expr} {S : List EventId} :
    ∀ c ∈ P.conjuncts, c ∈ (es.strPred P Q S).conjuncts :=
  fun _ h => List.mem_append_left _ h

/-- `j ∈ 𝕁`, relative to the global guarantees `Ω`. Every elaboration asks
    that the predicate it produces be consistent with `Ω`,
    `P_j ∧ Ω ≢ ⊥`. -/
inductive Generated (Ω : Pred) : Justification → Prop
  /-- Pre-justifications, where the value restriction is satisfiable. -/
  | pre {w : Event} {j : Justification} :
      w ∈ es.events → preJust w = some j → Sat w.valres.holds →
      Generated Ω j
  /-- Value Assignment (Definition `def:elab-va`): substitute a value `v` with
      `α ≡_P v` in the location and value of a justified write, recomputing
      `D` and leaving `P` unchanged. -/
  | va {j₁ : Justification} {o : MemOrd} {x e : Expr} {α : Sym} {v : Val} :
      Generated Ω j₁ →
      j₁.w.kind = .write o x e →
      EquivUnder j₁.P.holds (.sym α) (.val v) →
      Sat (Pred.and j₁.P.holds Ω) →
      Generated Ω
        { P := j₁.P
          D := (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms
          δ := j₁.δ
          w := { j₁.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) } }
  /-- Strengthening (Definition `def:elab-str`): conjoin a predicate `Q` and
      the value restrictions of the origins `S` it introduces,
      `P' = P ∧ Q ∧ ⋀_{e ∈ S} valres(e)`, with
      `S = origin(symbols(P')) ∖ origin(symbols(P))`. The equation for `S` is
      a fixed point, as `valres(e)` may itself bring in symbols; `S` is given
      and checked against it. `P'` is built syntactically, so
      `symbols(P') ⊇ symbols(P)` and `P'` entails `P`. -/
  | str {j₁ : Justification} (Q : Expr) (S : List EventId) :
      Generated Ω j₁ →
      (∀ e, e ∈ S ↔ e ∈ (strPred es j₁.P Q S).syms ∧ e ∉ j₁.P.syms) →
      (∀ e ∈ S, j₁.δ.Remap e e) →
      (∀ e ∈ S, (es.poR e j₁.w.id ∨ es.poR j₁.w.id e) ∧ ¬ es.ppo j₁.P.holds j₁.δ j₁.w.id e) →
      Sat (Pred.and (strPred es j₁.P Q S).holds Ω) →
      Generated Ω { j₁ with P := strPred es j₁.P Q S }
  /-- Forwarding (Definition `def:elab-fwd`) along `e₁ -F_{j₁}→ e₂`, applying
      `g = [val(e₂) ↦ val(e₁)]` to the predicate and to the justified write.
      The extended forwarding context must be well-formed (`def:fwd-ctx`). -/
  | fwd {j₁ : Justification} {o : MemOrd} {x e : Expr} {e₁ e₂ : EventId}
      {ev₁ ev₂ : Event} {v₁ v₂ : Expr} :
      Generated Ω j₁ →
      j₁.w.kind = .write o x e →
      es.fwdRel j₁ e₁ e₂ →
      es.ev e₁ = some ev₁ → es.ev e₂ = some ev₂ →
      ev₁.val = some v₁ → ev₂.val = some v₂ →
      FwdCtx.WF { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] } →
      Sat (Pred.and (j₁.P.replace v₂ v₁).holds Ω) →
      Generated Ω
        { P := j₁.P.replace v₂ v₁
          D := (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms
          δ := { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] }
          w := { j₁.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) } }
  /-- Write Elision (Definition `def:elab-we`), adding `(e₂, e₁)` to `WE`; the
      extended forwarding context must be well-formed (`def:fwd-ctx`). -/
  | we {j₁ : Justification} {e₁ e₂ : EventId} :
      Generated Ω j₁ →
      es.weRel j₁ e₁ e₂ →
      FwdCtx.WF { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } →
      Sat (Pred.and j₁.P.holds Ω) →
      Generated Ω { j₁ with δ := { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } }
  /-- Lifting (Definition `def:elab-lift`): `(⟦P₁⟧_Λ ∨ P₂, D₂) ⊢^δ w₂`. -/
  | lift {j₁ j₂ : Justification} (Λ : Relabelling) :
      Generated Ω j₁ → Generated Ω j₂ →
      j₁.δ = j₂.δ →
      Λ.Injective →
      es.ClosedRelabEq j₁.δ Λ j₁.P j₁.w j₂.P j₂.w →
      (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ.app α = e) →
      (∀ α ∈ j₁.D, ∃ ev₁ ev₂, es.ev α = some ev₁ ∧ es.ev (Λ.app α) = some ev₂ ∧
        es.ClosedRelabEq j₁.δ Λ j₁.P ev₁ j₂.P ev₂) →
      Sat (Pred.and (Expr.or (j₁.P.rename Λ) j₂.P).holds Ω) →
      Generated Ω { j₂ with P := .or (j₁.P.rename Λ) j₂.P }
  /-- Weakening (Definition `def:elab-weak`): drop a conjunct the global
      guarantees imply. Predicates are read up to their conjuncts
      (Paragraph `par:conj`), so `j₁.P` is `P' ∧ Pw` up to `ConjEq`, and any
      one conjunct can be dropped. -/
  | weak {j₁ : Justification} {P' Pw : Expr} :
      Generated Ω j₁ →
      j₁.P.ConjEq (.and P' Pw) →
      Entails Ω Pw.holds →
      Sat (Pred.and P'.holds Ω) →
      Generated Ω { j₁ with P := P' }

/-- Every generated justification has a predicate consistent with `Ω`, or is
    a pre-justification with a satisfiable value restriction. -/
theorem Generated.sat {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    Sat j.P.holds ∨ ∃ w ∈ es.events, preJust w = some j := by
  cases h with
  | pre hw hj _ => exact Or.inr ⟨_, hw, hj⟩
  | va _ _ _ hs | fwd _ _ _ _ _ _ _ _ hs | we _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩
  | str _ _ _ _ _ _ hs | weak _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩
  | lift _ _ _ _ _ _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩

end EventStructure
