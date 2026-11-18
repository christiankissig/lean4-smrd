import Smrd.RMWWFDenote

/-!
# Synchronisation order, coherence consequences, allocator reuse

Program-independent facts about executions that proofs about concrete
programs take as premises: which pairs of `⊑` the frozen `≼` keeps, that
synchronisation lies inside `nta`, the per-location consequences of RC11's
coherence axiom, and `allocDisjoint` in the form a reuse argument consumes.

* **`≼` lives on `X ∖ †`** (`ppo_not_elided`): every part of `≼` is
  remapped under `δ`, and `remap_δ` maps into non-elided events. So "not
  elided" is necessary in each lemma below, not only sufficient.
* **Release, acquire, same location.** For `a ⊑ b` in `X`, neither elided,
  `a ≠ b`: `b` a release write (`ppo_of_rel`, and `ppo_rel_iff`), `a` an
  acquire read (`ppo_of_acq`, `ppo_acq_iff`), or locations equal outright,
  `mustAlias`, with a model of MoRDor's combined predicate under which both
  locations evaluate (`ppo_of_mustAlias`; inside one justification window no
  model is needed, `ppo_of_mustAlias_win`); two accesses of one global need
  only `Sat P_m` (`ppo_of_glob`). The pair is anchored at its later end; no
  condition on forwarding or elision elsewhere in `δ` is needed.
* **Synchronisation inside `nta`.** Under `RMWWF` and a location model, the
  `rmw` pairs are in `≼` (`rmw_ppo`), so release sequences are `nta`-paths
  and `SW ⊆ nta` between non-fence events whose release write is not elided
  (`sw_nta`). The head of a release sequence must not be elided: Write
  Elision may elide a releasing write into a later releasing write
  (`weNoRel` allows it), and the elided write lies in no `DP ∪ ≼ ∪ rf`
  edge out of it, while `SW` still starts at it through `⊑|loc`. The
  *synchronisation order* `(≼ ∪ SW)⁺` (`syncOrd`) is inside `nta`
  (`syncOrd_nta`) and, where `≼ ⊆ ⊑`, inside RC11's `HB` (`syncOrd_hb`;
  `≼ ⊆ ⊑` is `Smrd.PpoTail.ppo_po` with `ppoStep_po_we`, or
  `Smrd.CoherenceT.dep_po_T`). RC11's `HB` contains all of `⊑` and is not
  inside `nta`.
* **RMW pairs.** `rmw` and the RMW part of `≼` read an RMW's condition under
  the predicate and `valres_X`, so a pair of `X` whose condition guards the
  write (`holds_of_guard`), or is `⊤`, is in `rmw` (`rmwRel_of_valresX`), and
  `≼_sync ; rmwPairs` and `rmwPairs ; ≼_sync` give `≼` from before a releasing
  RMW write to its read (`ppo_of_rel_rmw`) and from an RMW write to what its
  acquiring read precedes, in a justification window (`ppo_of_rmw_acq`).
* **Coherence** (RC11's axiom, under a coherence order): CoWW, CoWR, CoRW,
  CoRR (`coWW_co`, `coWR_co`, `coRW_co`, `coRR_co`).
* **Allocator** (`alloc_reuse`, `alloc_ne`): two distinct allocations of `X`
  at one location have a deallocation of one of them not `nta`-after the
  other's allocation.
-/

namespace Execution

variable {es : EventStructure} {x : Execution}

/-! ## `≼` lives on `X ∖ †` -/

/-- **Every step of `≼` relates non-elided events**: each part is remapped,
    and `remap_δ` maps into `X ∖ †`. -/
theorem ppoStep_not_elided {a b : EventId} (h : x.ppoStep es a b) :
    ¬ x.elided a ∧ ¬ x.elided b := by
  obtain ⟨-, -, ⟨j, -, ⟨⟨_, _, _, ra, rb⟩, _⟩, -⟩ |
    ⟨⟨⟨_, _, _, ra, rb⟩, _⟩ | ⟨⟨⟨_, _, _, ra, rb⟩, _⟩, _⟩, -⟩⟩ := h
  all_goals exact ⟨remap_not_elided ra, remap_not_elided rb⟩

/-- **`≼` relates non-elided events only.** -/
theorem ppo_not_elided {a b : EventId} (h : x.ppo es a b) : ¬ x.elided a ∧ ¬ x.elided b := by
  obtain ⟨-, -, h⟩ := h
  induction h with
  | single h => exact ppoStep_not_elided h
  | tail _ h ih => exact ⟨ih.1, (ppoStep_not_elided h).2⟩

/-! ## Release, acquire, same location -/

/-- **Release.** `a ⊑ w`, `w` a release write, both in `X`, neither elided:
    `a ≼ w` (MoRDor's `ppo_sync`, anchored at `w`). -/
theorem ppo_of_rel {a w : EventId} (ha : x.X a) (hw : x.X w) (hna : ¬ x.elided a)
    (hnw : ¬ x.elided w) (hpo : es.poR a w) (hne : a ≠ w) (hrel : es.cls Event.isRelW w) :
    x.ppo es a w := by
  have hrelM : es.cls Event.isRelM w := by
    obtain ⟨e, he, h⟩ := hrel; exact ⟨e, he, by simp [Event.isRelM, h]⟩
  exact ppo_of_step ha hw ⟨.inl ha, .inl hw, .inr ⟨.inl ⟨⟨a, w, ⟨hpo, .inr hrelM⟩,
    remap_self_of_not_elided hna, remap_self_of_not_elided hnw⟩, hne⟩,
    anchored_of_po (.inl hw) hpo⟩⟩

/-- **Release, exactly**: for `a ⊑ w` in `X` with `w` a release write,
    `a ≼ w` iff neither is elided. -/
theorem ppo_rel_iff {a w : EventId} (ha : x.X a) (hw : x.X w) (hpo : es.poR a w) (hne : a ≠ w)
    (hrel : es.cls Event.isRelW w) : x.ppo es a w ↔ ¬ x.elided a ∧ ¬ x.elided w :=
  ⟨ppo_not_elided, fun ⟨hna, hnw⟩ => ppo_of_rel ha hw hna hnw hpo hne hrel⟩

/-- **Acquire.** `r ⊑ b`, `r` an acquire read, both in `X`, neither elided:
    `r ≼ b` (MoRDor's `ppo_sync`, anchored at `b`). -/
theorem ppo_of_acq {r b : EventId} (hr : x.X r) (hb : x.X b) (hnr : ¬ x.elided r)
    (hnb : ¬ x.elided b) (hpo : es.poR r b) (hne : r ≠ b) (hacq : es.cls Event.isAcqR r) :
    x.ppo es r b := by
  have hacqM : es.cls Event.isAcqM r := by
    obtain ⟨e, he, h⟩ := hacq; exact ⟨e, he, by simp [Event.isAcqM, h]⟩
  exact ppo_of_step hr hb ⟨.inl hr, .inl hb, .inr ⟨.inl ⟨⟨r, b, ⟨hpo, .inl hacqM⟩,
    remap_self_of_not_elided hnr, remap_self_of_not_elided hnb⟩, hne⟩,
    anchored_of_po (.inl hb) hpo⟩⟩

/-- **Acquire, exactly**: for `r ⊑ b` in `X` with `r` an acquire read,
    `r ≼ b` iff neither is elided. -/
theorem ppo_acq_iff {r b : EventId} (hr : x.X r) (hb : x.X b) (hpo : es.poR r b) (hne : r ≠ b)
    (hacq : es.cls Event.isAcqR r) : x.ppo es r b ↔ ¬ x.elided r ∧ ¬ x.elided b :=
  ⟨ppo_not_elided, fun ⟨hnr, hnb⟩ => ppo_of_acq hr hb hnr hnb hpo hne hacq⟩

/-- The location of `a`, if any, evaluates under `f`. -/
def LocDef (es : EventStructure) (f : Valuation) (a : EventId) : Prop :=
  ∀ e l, es.ev a = some e → e.loc = some l → (l.eval f).isSome

/-- **Same location.** `a ⊑ b` with locations equal outright (`mustAlias`),
    both in `X`, neither elided, and a model of MoRDor's combined predicate
    `P_m` under which both locations evaluate: `a ≼ b` (MoRDor's `ppo_loc`,
    anchored at `b`). The model is what `ppo_loc`'s alias filter asks. -/
theorem ppo_of_mustAlias {a b : EventId} (ha : x.X a) (hb : x.X b) (hna : ¬ x.elided a)
    (hnb : ¬ x.elided b) (hpo : es.poR a b) (hne : a ≠ b) (hm : es.mustAlias a b)
    (hdef : ∃ f, x.Pm es f ∧ LocDef es f a ∧ LocDef es f b) : x.ppo es a b := by
  obtain ⟨f, hP, hda, hdb⟩ := hdef
  obtain ⟨ea, eb, la, lb, hea, heb, hla, hlb, hsem⟩ := hm
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hda ea la hea hla)
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hdb eb lb heb hlb)
  have hv : va = vb := hsem f va vb hva hvb
  subst hv
  have hal : es.mayAlias (x.Pm es) a b :=
    ⟨ea, eb, la, lb, hea, heb, hla, hlb, f, hP, by simp [Expr.holds, Expr.eval, hva, hvb]⟩
  exact ppo_of_step ha hb ⟨.inl ha, .inl hb, .inr ⟨.inr ⟨⟨⟨a, b,
    .inr ⟨hpo, .inl ⟨ea, eb, la, lb, hea, heb, hla, hlb, hsem⟩⟩,
    remap_self_of_not_elided hna, remap_self_of_not_elided hnb⟩, hne⟩, hal⟩,
    anchored_of_po (.inl hb) hpo⟩⟩

/-- **Same location under a location model** (`LocModel`, as for condition
    (i) in `Smrd.PpoTail`). -/
theorem ppo_of_mustAlias_locModel {a b : EventId} (ha : x.X a) (hb : x.X b)
    (hna : ¬ x.elided a) (hnb : ¬ x.elided b) (hpo : es.poR a b) (hne : a ≠ b)
    (hm : es.mustAlias a b) (hM : LocModel es x) : x.ppo es a b := by
  obtain ⟨f, hP, -, hdef⟩ := hM
  exact ppo_of_mustAlias ha hb hna hnb hpo hne hm
    ⟨f, hP, fun e l he hl => hdef a e l ha he hl, fun e l he hl => hdef b e l hb he hl⟩

/-- **Same location within one justification window**: `ppo_loc_eq` keeps
    the pair unconditionally, with no model. -/
theorem ppo_of_mustAlias_win {a b : EventId} (ha : x.X a) (hb : x.X b) (hna : ¬ x.elided a)
    (hnb : ¬ x.elided b) (hpo : es.poR a b) (hne : a ≠ b) (hm : es.mustAlias a b)
    (hwin : x.InWin es a b) : x.ppo es a b := by
  obtain ⟨j, hj, hwa, hwb⟩ := hwin
  exact ppo_of_step ha hb ⟨.inl ha, .inl hb, .inl ⟨j, hj, ⟨⟨a, b, .inr ⟨hpo, .inl hm⟩,
    remap_self_of_not_elided hna, remap_self_of_not_elided hnb⟩, hne⟩, hwa, hwb⟩⟩

/-- **Two accesses of one global**: `a ⊑ b` at the global `g`, both in `X`,
    neither elided, `P_m` satisfiable: `a ≼ b`. In particular two reads of one
    global. -/
theorem ppo_of_glob {a b : EventId} {ea eb : Event} {g : Var} (ha : x.X a) (hb : x.X b)
    (hna : ¬ x.elided a) (hnb : ¬ x.elided b) (hpo : es.poR a b) (hne : a ≠ b)
    (hea : es.ev a = some ea) (heb : es.ev b = some eb)
    (hla : ea.loc = some (Expr.glob g)) (hlb : eb.loc = some (Expr.glob g))
    (hsat : Sat (x.Pm es)) : x.ppo es a b := by
  have hdef : ∀ f c (ec : Event), es.ev c = some ec → ec.loc = some (Expr.glob g) →
      LocDef es f c := by
    intro f c ec hec hlc e l he hl
    rw [hec] at he; cases he; rw [hlc] at hl; cases hl
    simp [Expr.glob, Expr.eval]
  obtain ⟨f, hP⟩ := hsat
  refine ppo_of_mustAlias ha hb hna hnb hpo hne
    ⟨ea, eb, _, _, hea, heb, hla, hlb, fun f v₁ v₂ h₁ h₂ => ?_⟩
    ⟨f, hP, hdef f a ea hea hla, hdef f b eb heb hlb⟩
  rw [h₁] at h₂; exact Option.some.inj h₂

/-! ## Synchronisation inside `nta` -/

theorem transGen_first {R : Rel} {a b : EventId} (h : Relation.TransGen R a b) : ∃ c, R a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem nta_of_ppo {a b : EventId} (h : x.ppo es a b) : x.nta es a b := .single (.inl (.inl h))

theorem nta_of_rf {a b : EventId} (h : x.rf a b) : x.nta es a b := .single (.inr h)

theorem nta_trans {a b c : EventId} (h₁ : x.nta es a b) (h₂ : x.nta es b c) : x.nta es a c :=
  transGen_trans h₁ h₂

/-- **`rmw ⊆ ≼`** where the read of each RMW `⊑`-precedes its write at one
    location outright (`RMWWF`, true of every `⟨P⟩_n`, `denote_rmwWF`), `⊑`
    is irreflexive, and a location model exists. RMW accesses are never
    elided (`rmw_not_elided`). -/
theorem rmw_ppo {Ω : Pred} (hx : x.IsExecution es Ω) (hW : RMWWF es)
    (hirr : ∀ a, ¬ es.poR a a) (hM : LocModel es x) {r w : EventId} (h : x.rmwRel es r w) :
    x.ppo es r w := by
  obtain ⟨hr, hw, ent, hent, rfl, rfl, -⟩ := h
  obtain ⟨hpo, hm⟩ := hW ent hent
  exact ppo_of_mustAlias_locModel hr hw
    (fun hel => rmw_not_elided hx hel ⟨ent, hent, .inl rfl⟩)
    (fun hel => rmw_not_elided hx hel ⟨ent, hent, .inr rfl⟩)
    hpo (fun h => hirr _ (h ▸ hpo)) hm hM

/-- A condition every model of `valres_X` satisfies is `⊤` under any predicate
    conjoined with `valres_X`. -/
theorem equivUnder_tt_of_valresX {P : Pred} {c : Expr}
    (hc : ∀ f, x.valresX es f → c.holds f) :
    EquivUnder (Pred.and P (x.valresX es)) c Expr.tt := by
  intro f hf v₁ v₂ h₁ h₂
  have h := hc f hf.2
  unfold Expr.holds at h
  rw [h] at h₁
  simp [Expr.tt, Expr.eval] at h₂
  rw [← Option.some.inj h₁, ← h₂]

/-- The condition guarding a write of `X` holds under every model of `valres_X`. -/
theorem holds_of_guard {w : EventId} (hXw : x.X w) {ew : Event} (hev : es.ev w = some ew)
    {g : Guard} (hg : g ∈ ew.guards) (hgp : g.pos = true) :
    ∀ f, x.valresX es f → g.cond.holds f := fun f hf => by
  have h := (Expr.holds_conj _ f).1 (hf w ew hXw hev) g.expr (List.mem_map_of_mem hg)
  simpa only [Guard.expr, hgp, if_true] using h

/-- `⊤` holds under every valuation. -/
theorem holds_tt (f : Valuation) : Expr.tt.holds f := by
  simp [Expr.holds, Expr.tt, Expr.eval]

/-- **An RMW pair of `X` whose condition `valres_X` entails is in `rmw`**: the
    condition guards the write (`holds_of_guard`), or is `⊤`. In `⟨P⟩_n` every
    `CAS` write is guarded by its condition and every `FADD`'s condition is
    `⊤`. -/
theorem rmwRel_of_valresX {ent : RMWEntry} (hent : ent ∈ es.rmw) {r w : EventId}
    (hr : ent.r = r) (hw : ent.w = w) (hXr : x.X r) (hXw : x.X w)
    (hc : ∀ f, x.valresX es f → ent.cond.holds f) : x.rmwRel es r w :=
  ⟨hXr, hXw, ent, hent, hr, hw, equivUnder_tt_of_valresX hc⟩

/-- **Release into an RMW, carried to its read** (`ppo_sync ; rmwPairs`, in the
    part of the justification of the RMW's write): `a ⊑ w`, `w` the release
    write of an `rmw` entry with read `r ⊑ w`, all three in `X`, `a` not
    elided, `a ≠ r`, the condition entailed by `valres_X`: `a ≼ r`. -/
theorem ppo_of_rel_rmw {Ω : Pred} (hx : x.IsExecution es Ω) {ent : RMWEntry}
    (hent : ent ∈ es.rmw) (hc : ∀ f, x.valresX es f → ent.cond.holds f) {a : EventId}
    (ha : x.X a) (hr : x.X ent.r) (hw : x.X ent.w) (hna : ¬ x.elided a)
    (hpo : es.poR a ent.w) (hrw : es.poR ent.r ent.w) (hne : a ≠ ent.r)
    (hrel : es.cls Event.isRelW ent.w) : x.ppo es a ent.r := by
  have hnr : ¬ x.elided ent.r := fun h => rmw_not_elided hx h ⟨ent, hent, .inl rfl⟩
  have hnw : ¬ x.elided ent.w := fun h => rmw_not_elided hx h ⟨ent, hent, .inr rfl⟩
  have heff : es.cls Event.isEffect ent.w := by
    obtain ⟨e, he, h⟩ := hrel
    refine ⟨e, he, ?_⟩
    revert h; cases hk : e.kind <;> simp [Event.isRelW, Event.isEffect, Event.isWrite, hk]
  obtain ⟨j, hj, hjw, -⟩ := hx.justified ent.w hw heff hnw
  have hrelM : es.cls Event.isRelM ent.w := by
    obtain ⟨e, he, h⟩ := hrel; exact ⟨e, he, by simp [Event.isRelM, h]⟩
  have hbase : es.ppoBaseM (x.PJ es j) (x.PR es j) a ent.r :=
    .inl (.inr (.inl ⟨ent.w, ⟨hpo, .inr hrelM⟩, ent, hent, rfl, rfl,
      equivUnder_tt_of_valresX hc⟩))
  exact ppo_of_step ha hr ⟨.inl ha, .inl hr, .inl ⟨j, hj, ⟨⟨a, ent.r, hbase,
    remap_self_of_not_elided hna, remap_self_of_not_elided hnr⟩, hne⟩,
    .inr (hjw ▸ hpo), .inr (hjw ▸ hrw)⟩⟩

/-- **An RMW's write, carried to what its read acquires** (`rmwPairs ; ppo_sync`,
    in the part of the justification of a write `w₀` at or `⊑`-after `b`): the
    read `r` of an `rmw` entry an acquire, `r ⊑ b`, the write `w ⊑ b`, all in
    `X`, `b` not elided, `w ≠ b`, the condition entailed by `valres_X`: `w ≼ b`. -/
theorem ppo_of_rmw_acq {Ω : Pred} (hx : x.IsExecution es Ω) {ent : RMWEntry}
    (hent : ent ∈ es.rmw) (hc : ∀ f, x.valresX es f → ent.cond.holds f) {b : EventId}
    (hw : x.X ent.w) (hb : x.X b) (hnb : ¬ x.elided b) (hrb : es.poR ent.r b)
    (hne : ent.w ≠ b) (hacq : es.cls Event.isAcqR ent.r) {j : Justification} (hj : j ∈ x.J)
    (hwj : Win es j ent.w) (hbj : Win es j b) : x.ppo es ent.w b := by
  have hnw : ¬ x.elided ent.w := fun h => rmw_not_elided hx h ⟨ent, hent, .inr rfl⟩
  have hacqM : es.cls Event.isAcqM ent.r := by
    obtain ⟨e, he, h⟩ := hacq; exact ⟨e, he, by simp [Event.isAcqM, h]⟩
  have hbase : es.ppoBaseM (x.PJ es j) (x.PR es j) ent.w b :=
    .inl (.inr (.inr ⟨ent.r, ⟨ent, hent, rfl, rfl, equivUnder_tt_of_valresX hc⟩,
      ⟨hrb, .inl hacqM⟩⟩))
  exact ppo_of_step hw hb ⟨.inl hw, .inl hb, .inl ⟨j, hj, ⟨⟨ent.w, b, hbase,
    remap_self_of_not_elided hnw, remap_self_of_not_elided hnb⟩, hne⟩, hwj, hbj⟩⟩

/-- An `rf`-source is not elided (`φ`). -/
theorem not_elided_of_rf (hphi : x.phi es) {w r : EventId} (h : x.rf w r) : ¬ x.elided w :=
  hphi.1 w (.inl ⟨r, h⟩)

/-- **A release sequence from a non-elided write is an `nta`-path**, under
    the conditions of `rmw_ppo`; its tail must be read (`rf w' r`). -/
theorem rs_nta {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es) (hW : RMWWF es)
    (hirr : ∀ a, ¬ es.poR a a) (hM : LocModel es x) {w w' r : EventId}
    (hnw : ¬ x.elided w) (hrs : x.rs es w w') (hrf : x.rf w' r) :
    w = w' ∨ x.nta es w w' := by
  obtain ⟨-, w₀, h₀, -, hseq⟩ := hrs
  -- `w₀` is an `rf`-source, so not elided
  have hn₀ : ¬ x.elided w₀ := by
    rcases hseq with rfl | hseq
    · exact not_elided_of_rf hphi hrf
    · obtain ⟨u, r', hr', -⟩ := transGen_first hseq
      exact not_elided_of_rf hphi hr'
  have hchain : ∀ u v, Rel.plus (x.rfRmw es) u v → x.nta es u v := by
    intro u v huv
    have step : ∀ u v, x.rfRmw es u v → x.nta es u v := by
      rintro u v ⟨r', hr', hrmw⟩
      exact nta_trans (nta_of_rf hr') (nta_of_ppo (rmw_ppo hx hW hirr hM hrmw))
    induction huv with
    | single h => exact step _ _ h
    | tail _ h ih => exact nta_trans ih (step _ _ h)
  have hw₀ : w = w₀ ∨ x.nta es w w₀ := by
    rcases h₀ with rfl | hpl
    · exact .inl rfl
    · rcases poloc_dep_ne' hirr hM hnw hn₀ hpl with hp | hd
      · exact .inr (nta_of_ppo hp)
      · exact .inr (.single (.inl (.inr hd)))
  rcases hseq with rfl | hseq
  · exact hw₀
  · rcases hw₀ with rfl | hw₀
    · exact .inr (hchain _ _ hseq)
    · exact .inr (nta_trans hw₀ (hchain _ _ hseq))

/-- **`SW ⊆ nta`** between events that are not fences, where the releasing
    write is not elided, under `RMWWF`, irreflexive `⊑` and a location model.
    The non-elision of the head is needed: Write Elision may elide a
    releasing write into a later releasing write at its location, and then
    no `DP ∪ ≼ ∪ rf` edge leaves it, while `SW` starts at it through
    `⊑|loc`. -/
theorem sw_nta {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es) (hW : RMWWF es)
    (hirr : ∀ a, ¬ es.poR a a) (hM : LocModel es x) {a b : EventId}
    (hfa : ¬ es.cls Event.isFence a) (hfb : ¬ es.cls Event.isFence b) (hna : ¬ x.elided a)
    (h : x.sw es a b) : x.nta es a b := by
  obtain ⟨-, w, w', r, hw, hrs, hrf, -, hb, -⟩ := h
  have hwa : w = a := by
    rcases hw with h | ⟨hf, -⟩
    · exact h
    · exact absurd hf hfa
  have hbr : b = r := by
    rcases hb with h | ⟨-, hf⟩
    · exact h
    · exact absurd hf hfb
  subst hwa hbr
  rcases rs_nta hx hphi hW hirr hM hna hrs hrf with rfl | h
  · exact nta_of_rf hrf
  · exact nta_trans h (nta_of_rf hrf)

/-- **The synchronisation order** `(≼ ∪ SW)⁺`. -/
def syncOrd (es : EventStructure) (x : Execution) : Rel := Rel.plus ((x.ppo es).union (x.sw es))

/-- The head of an `SW` edge is in `X` where `X ∪ X_F` has no fences. -/
theorem sw_X {Ω : Pred} (hx : x.IsExecution es Ω) (hnf : x.FenceFree es) {a b : EventId}
    (h : x.sw es a b) : x.X a := by
  obtain ⟨-, w, w', r, hw, ⟨-, w₀, h₀, -, hseq⟩, hrf, -, -, -⟩ := h
  rcases hw with rfl | ⟨hf, hpo⟩
  · rcases h₀ with rfl | hpl
    · rcases hseq with rfl | hseq
      · exact (hx.rf_wr _ _ hrf).2.2.1
      · obtain ⟨u, r', hr', -⟩ := transGen_first hseq
        exact (hx.rf_wr _ _ hr').2.2.1
    · exact X_of_XwF hnf hpl.1.1
  · exact absurd hf (hnf _ hpo.1)

/-- **`(≼ ∪ SW)⁺ ⊆ nta`** for executions without fences in `X ∪ X_F`, where
    no releasing write of `X` is elided, under `RMWWF`, irreflexive `⊑` and a
    location model. -/
theorem syncOrd_nta {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es) (hW : RMWWF es)
    (hirr : ∀ a, ¬ es.poR a a) (hM : LocModel es x) (hnf : x.FenceFree es)
    (hrel : ∀ w, x.X w → es.cls Event.isRelW w → ¬ x.elided w) {a b : EventId}
    (h : x.syncOrd es a b) : x.nta es a b := by
  have step : ∀ a b, ((x.ppo es).union (x.sw es)) a b → x.nta es a b := by
    rintro a b (hp | hs)
    · exact nta_of_ppo hp
    · have hXa := sw_X hx hnf hs
      have hrelW : es.cls Event.isRelW a := by
        rcases hs.1 with h | h
        · exact h
        · exact absurd (cls_mono es (fun _ h => isFence_of_isRelF h) h) (hnf a (.inl hXa))
      have hXb : x.XwF es b := by
        obtain ⟨-, w, w', r, -, -, hrf, -, hb, -⟩ := hs
        rcases hb with rfl | ⟨hpo, -⟩
        · exact .inl (hx.rf_wr _ _ hrf).2.2.2
        · exact hpo.2.1
      exact sw_nta hx hphi hW hirr hM (hnf a (.inl hXa)) (hnf b hXb) (hrel a hXa hrelW) hs
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact nta_trans ih (step _ _ h)

/-- **`(≼ ∪ SW)⁺ ⊆ HB`** where `≼ ⊆ ⊑` (`Smrd.PpoTail.ppo_po` with
    `ppoStep_po_we`, or `Smrd.CoherenceT.dep_po_T`). -/
theorem syncOrd_hb (hppo : ∀ a b, x.ppo es a b → es.poR a b) {a b : EventId}
    (h : x.syncOrd es a b) : x.hb es a b := by
  have step : ∀ a b, ((x.ppo es).union (x.sw es)) a b → x.hb es a b := by
    rintro a b (hp | hs)
    · exact .single (.inl ⟨.inl hp.1, .inl hp.2.1, hppo a b hp⟩)
    · exact .single (.inr hs)
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact transGen_trans ih (step _ _ h)

/-! ## Coherence consequences (RC11)

From RC11's coherence axiom (`HB ; ECO?` irreflexive) and a coherence order.
`HB` is RC11's; with `syncOrd_hb` each applies to the synchronisation
order. -/

section Coh

variable {co : Rel}

/-- **CoWW**: writes `w₁ HB w₂` at one location are in `CO` order. -/
theorem coWW_co (hco : x.CoherenceOrder es co) (hC : x.Coherence es co) {w₁ w₂ : EventId}
    (hX₁ : x.X w₁) (hX₂ : x.X w₂) (hW₁ : es.cls Event.isWrite w₁)
    (hW₂ : es.cls Event.isWrite w₂) (hloc : x.sameLoc es w₁ w₂) (hhb : x.hb es w₁ w₂) :
    co w₁ w₂ := by
  by_cases he : w₁ = w₂
  · subst he; exact (hC w₁ ⟨w₁, hhb, .inl rfl⟩).elim
  · rcases hco.total _ _ hX₁ hX₂ hW₁ hW₂ he hloc with h | h
    · exact h
    · exact (hC w₁ ⟨w₂, hhb, .inr (.single (.inl (.inr h)))⟩).elim

/-- **CoWR**: a read `HB`-after a write `w` at its location reads `w` or a
    `CO`-later write. -/
theorem coWR_co (hco : x.CoherenceOrder es co) (hC : x.Coherence es co) {w w' r : EventId}
    (hX : x.X w) (hX' : x.X w') (hW : es.cls Event.isWrite w) (hW' : es.cls Event.isWrite w')
    (hloc : x.sameLoc es w w') (hhb : x.hb es w r) (hrf : x.rf w' r) : w = w' ∨ co w w' := by
  by_cases he : w = w'
  · exact .inl he
  · rcases hco.total _ _ hX hX' hW hW' he hloc with h | h
    · exact .inr h
    · exact (hC w ⟨r, hhb, .inr (.single (.inr ⟨w', hrf, h⟩))⟩).elim

/-- **CoRW**: a write `HB`-after a read at its location is `CO`-after the
    write the read reads. -/
theorem coRW_co (hco : x.CoherenceOrder es co) (hC : x.Coherence es co) {w w' r : EventId}
    (hX : x.X w) (hX' : x.X w') (hW : es.cls Event.isWrite w) (hW' : es.cls Event.isWrite w')
    (hloc : x.sameLoc es w w') (hhb : x.hb es r w) (hrf : x.rf w' r) : co w' w := by
  by_cases he : w = w'
  · subst he; exact (hC r ⟨w, hhb, .inr (.single (.inl (.inl hrf)))⟩).elim
  · rcases hco.total _ _ hX hX' hW hW' he hloc with h | h
    · exact (hC r ⟨w, hhb, .inr (.tail (.single (.inl (.inr h))) (.inl (.inl hrf)))⟩).elim
    · exact h

/-- **CoRR**: reads `r₁ HB r₂` at one location read `CO`-ordered writes. -/
theorem coRR_co (hco : x.CoherenceOrder es co) (hC : x.Coherence es co)
    {w₁ w₂ r₁ r₂ : EventId} (hX₁ : x.X w₁) (hX₂ : x.X w₂) (hW₁ : es.cls Event.isWrite w₁)
    (hW₂ : es.cls Event.isWrite w₂) (hloc : x.sameLoc es w₁ w₂) (hhb : x.hb es r₁ r₂)
    (hrf₁ : x.rf w₁ r₁) (hrf₂ : x.rf w₂ r₂) : w₁ = w₂ ∨ co w₁ w₂ := by
  by_cases he : w₁ = w₂
  · exact .inl he
  · rcases hco.total _ _ hX₁ hX₂ hW₁ hW₂ he hloc with h | h
    · exact .inr h
    · exact (hC r₁ ⟨r₂, hhb,
        .inr (.tail (.single (.inr ⟨w₂, hrf₂, h⟩)) (.inl (.inl hrf₁)))⟩).elim

/-- The writes two `rf` edges read are at one location where the reads are. -/
theorem sameLoc_rf {Ω : Pred} (hx : x.IsExecution es Ω) {w₁ w₂ r₁ r₂ : EventId}
    (hrf₁ : x.rf w₁ r₁) (hrf₂ : x.rf w₂ r₂) (hloc : x.sameLoc es r₁ r₂) :
    x.sameLoc es w₁ w₂ :=
  x.sameLoc_trans es (x.sameLoc_trans es (x.rfLoc_of_isExecution es hx _ _ hrf₁) hloc)
    (x.sameLoc_symm es (x.rfLoc_of_isExecution es hx _ _ hrf₂))

/-- **CoWR in an execution**: `w HB r`, `w` a write of `X` at `r`'s location,
    `r` reads `w'`: `w = w' ∨ co w w'`. -/
theorem coWR_co_exec {Ω : Pred} (hx : x.IsExecution es Ω) (hco : x.CoherenceOrder es co)
    (hC : x.Coherence es co) {w w' r : EventId} (hX : x.X w) (hW : es.cls Event.isWrite w)
    (hloc : x.sameLoc es w r) (hhb : x.hb es w r) (hrf : x.rf w' r) : w = w' ∨ co w w' :=
  coWR_co hco hC hX (hx.rf_wr _ _ hrf).2.2.1 hW (hx.rf_wr _ _ hrf).1
    (x.sameLoc_trans es hloc (x.sameLoc_symm es (x.rfLoc_of_isExecution es hx _ _ hrf))) hhb hrf

/-- **CoRR in an execution**: `r₁ HB r₂` at one location, reading `w₁` and
    `w₂`: `w₁ = w₂ ∨ co w₁ w₂`. -/
theorem coRR_co_exec {Ω : Pred} (hx : x.IsExecution es Ω) (hco : x.CoherenceOrder es co)
    (hC : x.Coherence es co) {w₁ w₂ r₁ r₂ : EventId} (hloc : x.sameLoc es r₁ r₂)
    (hhb : x.hb es r₁ r₂) (hrf₁ : x.rf w₁ r₁) (hrf₂ : x.rf w₂ r₂) : w₁ = w₂ ∨ co w₁ w₂ :=
  coRR_co hco hC (hx.rf_wr _ _ hrf₁).2.2.1 (hx.rf_wr _ _ hrf₂).2.2.1 (hx.rf_wr _ _ hrf₁).1
    (hx.rf_wr _ _ hrf₂).1 (sameLoc_rf hx hrf₁ hrf₂ hloc) hhb hrf₁ hrf₂

end Coh

/-! ## Allocator reuse -/

/-- **Allocator reuse**: under `allocDisjoint` (part of `φ_rf`), two distinct
    allocations of `X` at one location have a deallocation in `X` of one of
    them that is not `nta`-after the other's allocation. -/
theorem alloc_reuse {f : Valuation} (h : x.allocDisjoint es f) {a₁ a₂ : EventId}
    {e₁ e₂ : Event} {α₁ α₂ : Sym} {s₁ s₂ : Expr} (hX₁ : x.X a₁) (hX₂ : x.X a₂) (hne : a₁ ≠ a₂)
    (he₁ : es.ev a₁ = some e₁) (he₂ : es.ev a₂ = some e₂)
    (hk₁ : e₁.kind = .alloc α₁ s₁) (hk₂ : e₂.kind = .alloc α₂ s₂) (heq : f α₁ = f α₂) :
    ∃ d, (x.Frees es f d α₁ ∧ ¬ x.nta es a₂ d) ∨ (x.Frees es f d α₂ ∧ ¬ x.nta es a₁ d) :=
  Classical.byContradiction fun hn =>
    h.2 a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ hX₁ hX₂ hne he₁ he₂ hk₁ hk₂ hn heq

/-- **Allocator reuse, contrapositive**: two distinct allocations of `X` are
    at distinct locations if every deallocation of either location is
    `nta`-after the other allocation. -/
theorem alloc_ne {f : Valuation} (h : x.allocDisjoint es f) {a₁ a₂ : EventId}
    {e₁ e₂ : Event} {α₁ α₂ : Sym} {s₁ s₂ : Expr} (hX₁ : x.X a₁) (hX₂ : x.X a₂) (hne : a₁ ≠ a₂)
    (he₁ : es.ev a₁ = some e₁) (he₂ : es.ev a₂ = some e₂)
    (hk₁ : e₁.kind = .alloc α₁ s₁) (hk₂ : e₂.kind = .alloc α₂ s₂)
    (hd₁ : ∀ d, x.Frees es f d α₁ → x.nta es a₂ d)
    (hd₂ : ∀ d, x.Frees es f d α₂ → x.nta es a₁ d) : f α₁ ≠ f α₂ := by
  intro heq
  obtain ⟨d, ⟨hf, hn⟩ | ⟨hf, hn⟩⟩ := alloc_reuse h hX₁ hX₂ hne he₁ he₂ hk₁ hk₂ heq
  · exact hn (hd₁ d hf)
  · exact hn (hd₂ d hf)

end Execution
