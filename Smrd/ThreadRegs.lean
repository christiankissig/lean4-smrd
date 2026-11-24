import Smrd.SymWFDenote
import Smrd.FwdAcrossJoin
import Smrd.GuardLoss

/-!
# Registers local to a thread (`cond:thread-regs`)

The technical report's Condition `cond:thread-regs`: for every occurrence of
`P₁ ∥ P₂` in the program, no register of `P₁` occurs outside `P₁`, and no
register of `P₂` occurs outside `P₂` (`Stmt.ThreadRegs`, decidable).

Under it, the location, value, size or condition of every event of `⟨P⟩_n`
(`Event.actSyms`) mentions only symbols introduced by events of its own
thread (`denote_threadLocal`): the origin is `⊑`-before the event, and no fork
side of a `∥` contains exactly one of the two (`Stmt.SameThread`). A child's
events mention no symbol of its parent, of its sibling, or of the threads it
spawns; the parent's events mention none of its children's.

Threads are fork sides, addressed by program counter: side `i` of the `∥` at
address `p` is `p ++ [i]` (`Stmt.forkSides`), and an event lies in it when its
program counter extends it. The left side keeps the parent's `ThreadId`, so
`Label.thread` does not separate it from the parent.

* Value restrictions are not covered: code after a branching, a fork among it,
  is interpreted under the outcome, so a thread's guards may mention its
  parent's symbols (`guardEx_parent`).
* The hypothesis is needed: `r := x; (y := r ∥ skip)` hands the read's symbol
  to the child (`leakEx_not_threadRegs`, `leakEx_leaks`). It is needed only
  there: the parent resumes with the register state it forked with and each
  side starts from it, so a thread's symbols reach neither the parent after
  the join nor a sibling, with or without the condition (checked on
  `joinEx_local`, `sibEx_local`; not proved in general). The condition makes that choice unobservable: without it,
  `(r := x ∥ skip); y := r` writes the value `r` held before the fork.
* A `∥` inside a loop body is forked once per iteration, at one address:
  `SameThread` does not separate two iterations' instances of one side.
-/

/-! ## Register occurrences -/

/-- The registers of a program expression. -/
def PExpr.regs : PExpr → List Reg
  | .reg r => [r]
  | .num _ => []
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => a.regs ++ b.regs
  | .not a => a.regs

/-- The registers occurring in a program. -/
def Stmt.regs : Stmt → List Reg
  | .skip | .fence _ => []
  | .seq s₁ s₂ | .par s₁ s₂ => s₁.regs ++ s₂.regs
  | .ite b s₁ s₂ => b.regs ++ s₁.regs ++ s₂.regs
  | .while _ b body => b.regs ++ body.regs
  | .assign r e | .loadPtr _ r e _ | .fadd _ _ r _ e | .malloc r e => r :: e.regs
  | .load _ r _ _ | .addrOf r _ | .free r => [r]
  | .store _ _ e _ => e.regs
  | .storePtr _ e₁ e₂ _ => e₁.regs ++ e₂.regs
  | .cas _ _ r _ e₁ e₂ => r :: (e₁.regs ++ e₂.regs)

/-- The registers occurring outside every `∥` of a program: those of the
    thread interpreting it. -/
def Stmt.topRegs : Stmt → List Reg
  | .par _ _ => []
  | .seq s₁ s₂ => s₁.topRegs ++ s₂.topRegs
  | .ite b s₁ s₂ => b.regs ++ s₁.topRegs ++ s₂.topRegs
  | .while _ b body => b.regs ++ body.topRegs
  | .skip | .fence _ => []
  | .assign r e | .loadPtr _ r e _ | .fadd _ _ r _ e | .malloc r e => r :: e.regs
  | .load _ r _ _ | .addrOf r _ | .free r => [r]
  | .store _ _ e _ => e.regs
  | .storePtr _ e₁ e₂ _ => e₁.regs ++ e₂.regs
  | .cas _ _ r _ e₁ e₂ => r :: (e₁.regs ++ e₂.regs)

/-- The registers occurring inside some `∥` of a program: those of the
    threads it spawns. -/
def Stmt.parRegs : Stmt → List Reg
  | .par s₁ s₂ => s₁.regs ++ s₂.regs
  | .seq s₁ s₂ | .ite _ s₁ s₂ => s₁.parRegs ++ s₂.parRegs
  | .while _ _ body => body.parRegs
  | _ => []

/-- `cond:thread-regs` for a subprogram whose context mentions the registers
    `out`: at every `∥`, no register of a side occurs outside that side. -/
def Stmt.RegsLocal (out : List Reg) : Stmt → Prop
  | .seq s₁ s₂ => s₁.RegsLocal (out ++ s₂.regs) ∧ s₂.RegsLocal (out ++ s₁.regs)
  | .par s₁ s₂ => (∀ r ∈ s₁.regs, r ∉ out ∧ r ∉ s₂.regs) ∧ (∀ r ∈ s₂.regs, r ∉ out) ∧
      s₁.RegsLocal (out ++ s₂.regs) ∧ s₂.RegsLocal (out ++ s₁.regs)
  | .ite b s₁ s₂ =>
      s₁.RegsLocal (out ++ b.regs ++ s₂.regs) ∧ s₂.RegsLocal (out ++ b.regs ++ s₁.regs)
  | .while _ b body => body.RegsLocal (out ++ b.regs)
  | _ => True

instance Stmt.decRegsLocal : (out : List Reg) → (s : Stmt) → Decidable (s.RegsLocal out)
  | out, .seq s₁ s₂ => by
      haveI := Stmt.decRegsLocal (out ++ s₂.regs) s₁
      haveI := Stmt.decRegsLocal (out ++ s₁.regs) s₂
      unfold Stmt.RegsLocal; infer_instance
  | out, .par s₁ s₂ => by
      haveI := Stmt.decRegsLocal (out ++ s₂.regs) s₁
      haveI := Stmt.decRegsLocal (out ++ s₁.regs) s₂
      unfold Stmt.RegsLocal; infer_instance
  | out, .ite b s₁ s₂ => by
      haveI := Stmt.decRegsLocal (out ++ b.regs ++ s₂.regs) s₁
      haveI := Stmt.decRegsLocal (out ++ b.regs ++ s₁.regs) s₂
      unfold Stmt.RegsLocal; infer_instance
  | out, .while _ b body => by
      haveI := Stmt.decRegsLocal (out ++ b.regs) body
      unfold Stmt.RegsLocal; infer_instance
  | _, .skip | _, .assign .. | _, .load .. | _, .store .. | _, .addrOf .. | _, .loadPtr ..
  | _, .storePtr .. | _, .fence .. | _, .fadd .. | _, .cas .. | _, .malloc .. | _, .free .. =>
      isTrue (by simp [Stmt.RegsLocal])

/-- **Registers local to a thread** (Condition `cond:thread-regs`): for every
    occurrence of `P₁ ∥ P₂`, no register of `P₁` occurs outside `P₁`, and no
    register of `P₂` occurs outside `P₂`. -/
def Stmt.ThreadRegs (P : Stmt) : Prop := P.RegsLocal []

instance (P : Stmt) : Decidable P.ThreadRegs := Stmt.decRegsLocal [] P

/-! ## Threads as fork sides -/

/-- The fork sides of a program: `p ++ [i]` for side `i` of the `∥` at address
    `p`. Addresses are the program counters `interp` assigns: the components of
    `;`, `∥` and `if` at `[0]` and `[1]`, a loop body at `[0]`. -/
def Stmt.forkSides : Stmt → List (List Nat)
  | .seq s₁ s₂ | .ite _ s₁ s₂ => s₁.forkSides.map (0 :: ·) ++ s₂.forkSides.map (1 :: ·)
  | .par s₁ s₂ => [0] :: [1] :: (s₁.forkSides.map (0 :: ·) ++ s₂.forkSides.map (1 :: ·))
  | .while _ _ body => body.forkSides.map (0 :: ·)
  | _ => []

/-- Program counters `pc`, `pc'` of `P` in one thread: every fork side of `P`
    contains both or neither. -/
def Stmt.SameThread (P : Stmt) (pc pc' : List Nat) : Prop :=
  ∀ f ∈ P.forkSides, (f <+: pc ↔ f <+: pc')

instance (P : Stmt) (pc pc' : List Nat) : Decidable (P.SameThread pc pc') := by
  unfold Stmt.SameThread; infer_instance

/-- The symbols of an event's action: its location, value, size, or branch
    condition; not its value restriction, nor the symbol a read or allocation
    introduces. -/
def Event.actSyms (e : Event) : List Sym :=
  match e.kind with
  | .branch c => c.syms
  | _ => e.exprSyms

namespace ThreadRegsDenote

open EventStructure SymWFDenote

/-! ## Syntactic lemmas -/

theorem topRegs_sub : ∀ (s : Stmt), ∀ r ∈ s.topRegs, r ∈ s.regs := by
  intro s; induction s <;> intro r hr <;>
    simp_all [Stmt.topRegs, Stmt.regs] <;> grind

theorem parRegs_sub : ∀ (s : Stmt), ∀ r ∈ s.parRegs, r ∈ s.regs := by
  intro s; induction s <;> intro r hr <;>
    simp_all [Stmt.parRegs, Stmt.regs] <;> grind

theorem parRegs_out : ∀ (s : Stmt) (out : List Reg), s.RegsLocal out →
    ∀ r ∈ s.parRegs, r ∉ out := by
  intro s; induction s with
  | seq s₁ s₂ ih₁ ih₂ | ite _ s₁ s₂ ih₁ ih₂ =>
      intro out h r hr
      simp only [Stmt.RegsLocal, Stmt.parRegs, List.mem_append] at h hr
      rcases hr with hr | hr
      · exact fun h' => ih₁ _ h.1 r hr (List.mem_append_left _ (by simp_all))
      · exact fun h' => ih₂ _ h.2 r hr (List.mem_append_left _ (by simp_all))
  | par s₁ s₂ =>
      intro out h r hr
      simp only [Stmt.RegsLocal, Stmt.parRegs, List.mem_append] at h hr
      rcases hr with hr | hr
      · exact (h.1 r hr).1
      · exact h.2.1 r hr
  | «while» _ _ body ih =>
      intro out h r hr
      exact fun h' => ih _ h r hr (List.mem_append_left _ h')
  | _ => intro out _ r hr; simp [Stmt.parRegs] at hr

theorem topRegs_not_parRegs : ∀ (s : Stmt) (out : List Reg), s.RegsLocal out →
    ∀ r ∈ s.topRegs, r ∉ s.parRegs := by
  intro s; induction s with
  | seq s₁ s₂ ih₁ ih₂ =>
      intro out h r hr hp
      simp only [Stmt.RegsLocal, Stmt.topRegs, Stmt.parRegs, List.mem_append] at h hr hp
      rcases hr with hr | hr <;> rcases hp with hp | hp
      · exact ih₁ _ h.1 r hr hp
      · exact parRegs_out s₂ _ h.2 r hp (by simp [topRegs_sub s₁ r hr])
      · exact parRegs_out s₁ _ h.1 r hp (by simp [topRegs_sub s₂ r hr])
      · exact ih₂ _ h.2 r hr hp
  | ite b s₁ s₂ ih₁ ih₂ =>
      intro out h r hr hp
      simp only [Stmt.RegsLocal, Stmt.topRegs, Stmt.parRegs, List.mem_append] at h hr hp
      rcases hp with hp | hp
      · have := parRegs_out s₁ _ h.1 r hp
        rcases hr with (hr | hr) | hr
        · exact this (by simp [hr])
        · exact ih₁ _ h.1 r hr hp
        · exact this (by simp [topRegs_sub s₂ r hr])
      · have := parRegs_out s₂ _ h.2 r hp
        rcases hr with (hr | hr) | hr
        · exact this (by simp [hr])
        · exact this (by simp [topRegs_sub s₁ r hr])
        · exact ih₂ _ h.2 r hr hp
  | «while» _ b body ih =>
      intro out h r hr hp
      simp only [Stmt.RegsLocal, Stmt.topRegs, Stmt.parRegs, List.mem_append] at h hr hp
      rcases hr with hr | hr
      · exact parRegs_out body _ h r hp (by simp [hr])
      · exact ih _ h r hr hp
  | par => intro _ _ r hr; simp [Stmt.topRegs] at hr
  | _ => intro _ _ r _ hp; simp [Stmt.parRegs] at hp

theorem forkSides_ne_nil : ∀ (s : Stmt), ∀ g ∈ s.forkSides, g ≠ [] := by
  intro s; induction s <;> intro g hg <;> simp [Stmt.forkSides] at hg <;> grind

/-! ## Threads, positions and scopes -/

variable (F : List (List Nat))

/-- `pc` lies in the thread whose enclosing fork sides are `Anc`. -/
def InThr (Anc : List (List Nat)) (pc : List Nat) : Prop := ∀ f ∈ F, (f <+: pc ↔ f ∈ Anc)

/-- One thread: every fork side of `F` contains both or neither. -/
def SameThr (a b : List Nat) : Prop := ∀ f ∈ F, (f <+: a ↔ f <+: b)

/-- The subprogram `s` sits at address `q`, in the thread with enclosing fork
    sides `Anc`: the fork sides of `F` above `q` are `Anc`, and those below
    `q` are `s`'s. -/
def Pos (Anc : List (List Nat)) (q : List Nat) (s : Stmt) : Prop :=
  (∀ f ∈ F, f <+: q → f ∈ Anc) ∧ (∀ f ∈ Anc, f <+: q) ∧
    (∀ f ∈ F, q <+: f → f <+: q ∨ ∃ g ∈ s.forkSides, f = q ++ g)

variable {F}

theorem Pos.inThr {Anc : List (List Nat)} {q : List Nat} {s : Stmt} (h : Pos F Anc q s)
    {w : List Nat} (hw : ∀ g ∈ s.forkSides, ¬ g <+: w) : InThr F Anc (q ++ w) := by
  intro f hf
  refine ⟨fun hfw => ?_, fun ha => (h.2.1 f ha).trans (List.prefix_append _ _)⟩
  rcases List.prefix_or_prefix_of_prefix hfw (List.prefix_append q w) with hq | hq
  · exact h.1 f hf hq
  · rcases h.2.2 f hf hq with hq' | ⟨g, hg, rfl⟩
    · exact h.1 f hf hq'
    · exact absurd ((List.prefix_append_right_inj q).1 hfw) (hw g hg)

theorem Pos.inThr_nil {Anc : List (List Nat)} {q : List Nat} {s : Stmt} (h : Pos F Anc q s) :
    InThr F Anc q := by
  simpa using h.inThr (w := []) (fun g hg hp => forkSides_ne_nil s g hg (List.prefix_nil.1 hp))

theorem Pos.inThr_atom {Anc : List (List Nat)} {q : List Nat} {s : Stmt} (h : Pos F Anc q s)
    (hs : s.forkSides = []) (w : List Nat) : InThr F Anc (q ++ w) :=
  h.inThr (fun g hg => by simp [hs] at hg)

theorem not_prefix_snoc {q f : List Nat} {i : Nat} (h₁ : q ++ [i] <+: f) (h₂ : f <+: q) : False := by
  have := (h₁.trans h₂).length_le
  simp at this; omega

/-- Into side `i` of `s`: the fork sides of `s` below `[i]` are `[i]` (a fork)
    or those of `s'`, shifted. -/
theorem Pos.child {Anc Anc' : List (List Nat)} {q : List Nat} {s s' : Stmt} {i : Nat}
    (h : Pos F Anc q s)
    (hA₁ : ∀ f ∈ F, f = q ++ [i] → f ∈ Anc') (hA₂ : ∀ f ∈ Anc, f ∈ Anc')
    (hA₃ : ∀ f ∈ Anc', f ∈ Anc ∨ f = q ++ [i])
    (hsub : ∀ g ∈ s.forkSides, [i] <+: g → g = [i] ∨ ∃ g' ∈ s'.forkSides, g = i :: g') :
    Pos F Anc' (q ++ [i]) s' := by
  refine ⟨fun f hf hp => ?_, fun f ha => ?_, fun f hf hp => ?_⟩
  · rcases List.prefix_concat_iff.1 hp with rfl | hp
    · exact hA₁ _ hf rfl
    · exact hA₂ f (h.1 f hf hp)
  · rcases hA₃ f ha with ha | rfl
    · exact (h.2.1 f ha).trans (List.prefix_append _ _)
    · exact List.prefix_refl _
  · rcases h.2.2 f hf ((List.prefix_append q [i]).trans hp) with hq | ⟨g, hg, rfl⟩
    · exact (not_prefix_snoc hp hq).elim
    · have hig : [i] <+: g := (List.prefix_append_right_inj q).1 hp
      rcases hsub g hg hig with rfl | ⟨g', hg', rfl⟩
      · exact .inl (List.prefix_refl _)
      · exact .inr ⟨g', hg', by simp⟩

/-- A component that is not a fork side: the thread is unchanged. -/
theorem Pos.sub {Anc : List (List Nat)} {q : List Nat} {s s' : Stmt} {i : Nat}
    (h : Pos F Anc q s)
    (hsub : ∀ g ∈ s.forkSides, [i] <+: g → ∃ g' ∈ s'.forkSides, g = i :: g') :
    Pos F Anc (q ++ [i]) s' := by
  refine h.child (fun f hf hfq => ?_) (fun _ h => h) (fun _ h => .inl h)
    (fun g hg hp => .inr (hsub g hg hp))
  subst hfq
  rcases h.2.2 _ hf (List.prefix_append _ _) with hq | ⟨g, hg, hgq⟩
  · exact (not_prefix_snoc (List.prefix_refl _) hq).elim
  · have : g = [i] := (List.append_cancel_left hgq).symm
    subst this
    obtain ⟨g', hg', he⟩ := hsub _ hg (List.prefix_refl _)
    cases he
    exact (forkSides_ne_nil s' _ hg' rfl).elim

/-- Fork side `i` of `s`: the thread is `q ++ [i]`. -/
theorem Pos.fork {Anc : List (List Nat)} {q : List Nat} {s s' : Stmt} {i : Nat}
    (h : Pos F Anc q s)
    (hsub : ∀ g ∈ s.forkSides, [i] <+: g → g = [i] ∨ ∃ g' ∈ s'.forkSides, g = i :: g') :
    Pos F ((q ++ [i]) :: Anc) (q ++ [i]) s' :=
  h.child (fun f _ hf => by simp [hf]) (fun _ h => List.mem_cons_of_mem _ h)
    (fun f hf => by simpa [or_comm] using hf) hsub

/-- `k`'s events take the symbols of their actions from `A`, being in the
    current thread `Anc`, or from a `⊑`-earlier event of `k` in their thread. -/
def Good (Anc : List (List Nat)) (A : Sym → Prop) (k : EventStructure) : Prop :=
  ∀ e ∈ k.events, ∀ α ∈ e.actSyms, (A α ∧ InThr F Anc e.label.pc) ∨
    ∃ a ∈ k.events, a.id = α ∧ (α, e.id) ∈ k.po ∧ SameThr F a.label.pc e.label.pc

def HoldsA (Anc : List (List Nat)) (A : Sym → Prop) (m : Gen EventStructure) : Prop :=
  ∀ σ : GenState, Good (F := F) Anc A (m.run σ).1

variable {Anc : List (List Nat)}

theorem Good.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {k : EventStructure}
    (h : Good (F := F) Anc A k) : Good (F := F) Anc B k := fun e he α hα =>
  (h e he α hα).imp (fun h => ⟨hAB α h.1, h.2⟩) id

/-- A thread's events, seen from its parent: no symbol comes from the scope. -/
theorem Good.forget {Anc' : List (List Nat)} {A : Sym → Prop} {k : EventStructure}
    (h : Good (F := F) Anc' (fun _ => False) k) : Good (F := F) Anc A k := fun e he α hα =>
  (h e he α hα).elim (fun h => h.1.elim) .inr

theorem good_empty (A : Sym → Prop) : Good (F := F) Anc A .empty := fun _ he => by cases he

theorem Good.plus {A : Sym → Prop} {k₁ k₂ : EventStructure} (h₁ : Good (F := F) Anc A k₁)
    (h₂ : Good (F := F) Anc A k₂) : Good (F := F) Anc A (k₁.plus k₂) := by
  intro e he α hα
  rcases List.mem_append.1 he with he | he
  · exact (h₁ e he α hα).imp id fun ⟨a, ha, h1, h2, h3⟩ =>
      ⟨a, List.mem_append_left _ ha, h1, List.mem_append_left _ h2, h3⟩
  · exact (h₂ e he α hα).imp id fun ⟨a, ha, h1, h2, h3⟩ =>
      ⟨a, List.mem_append_right _ ha, h1, List.mem_append_right _ h2, h3⟩

theorem Good.join {A : Sym → Prop} {k₁ k₂ : EventStructure} (h₁ : Good (F := F) Anc A k₁)
    (h₂ : Good (F := F) Anc A k₂) : Good (F := F) Anc A (k₁.join k₂) := by
  intro e he α hα
  rcases List.mem_append.1 he with he | he
  · exact (h₁ e he α hα).imp id fun ⟨a, ha, h1, h2, h3⟩ =>
      ⟨a, List.mem_append_left _ ha, h1,
        List.mem_append_left _ (List.mem_append_left _ h2), h3⟩
  · exact (h₂ e he α hα).imp id fun ⟨a, ha, h1, h2, h3⟩ =>
      ⟨a, List.mem_append_right _ ha, h1,
        List.mem_append_left _ (List.mem_append_right _ h2), h3⟩

theorem Good.addRMW {A : Sym → Prop} {k : EventStructure} (h : Good (F := F) Anc A k)
    (r : EventId) (c : Expr) (w : EventId) : Good (F := F) Anc A (k.addRMW r c w) := h

theorem Good.prefix {A : Sym → Prop} {e : Event} {k : EventStructure}
    (hin : InThr F Anc e.label.pc) (hd : ∀ α ∈ e.actSyms, A α)
    (hk : Good (F := F) Anc (fun α => A α ∨ α = e.id) k) :
    Good (F := F) Anc A («prefix» e k) := by
  intro e' he' α hα
  rcases List.mem_cons.1 he' with rfl | he'
  · exact .inl ⟨hd α hα, hin⟩
  · rcases hk e' he' α hα with ⟨h | rfl, hin'⟩ | ⟨a, ha, h1, h2, h3⟩
    · exact .inl ⟨h, hin'⟩
    · exact .inr ⟨e, List.mem_cons_self, rfl,
        List.mem_append_left _ (List.mem_map.2 ⟨e', he', rfl⟩),
        fun f hf => (hin f hf).trans (hin' f hf).symm⟩
    · exact .inr ⟨a, List.mem_cons_of_mem _ ha, h1, List.mem_append_right _ h2, h3⟩

/-! ## Register states -/

/-- The registers `R` the thread reads hold symbols of `A`; the registers `C`
    of the threads it spawns hold none. -/
def RegsOK (A : Sym → Prop) (R C : Reg → Prop) (ρ : RegState) : Prop :=
  (∀ r, R r → ∀ α ∈ (ρ.get r).syms, A α) ∧ (∀ r, C r → (ρ.get r).syms = [])

theorem get_set (ρ : RegState) (r r' : Reg) (v : Expr) :
    (ρ.set r v).get r' = if r' = r then v else ρ.get r' := by
  by_cases h : r' = r
  · subst h; simp [RegState.get, RegState.set]
  · have hb : (r' == r) = false := by simpa using h
    simp [RegState.get, RegState.set, List.lookup, hb, h]

theorem RegsOK.den {A : Sym → Prop} {R C : Reg → Prop} {ρ : RegState} (h : RegsOK A R C ρ) :
    ∀ (p : PExpr), (∀ r ∈ p.regs, R r) → ∀ α ∈ (p.den ρ).syms, A α := by
  intro p
  induction p with
  | reg r => intro hR α hα; exact h.1 r (hR r (by simp [PExpr.regs])) α hα
  | num n => intro _ α hα; simp [PExpr.den, Expr.num, Expr.syms] at hα
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      intro hR α hα
      simp only [PExpr.den, Expr.syms, List.mem_append] at hα
      simp only [PExpr.regs, List.mem_append] at hR
      rcases hα with hα | hα
      · exact iha (fun r hr => hR r (.inl hr)) α hα
      · exact ihb (fun r hr => hR r (.inr hr)) α hα
  | not a iha => intro hR α hα; simp only [PExpr.den, Expr.syms] at hα; exact iha hR α hα

theorem RegsOK.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {R C : Reg → Prop}
    {ρ : RegState} (h : RegsOK A R C ρ) : RegsOK B R C ρ :=
  ⟨fun r hr α hα => hAB α (h.1 r hr α hα), h.2⟩

theorem RegsOK.set {A : Sym → Prop} {R C : Reg → Prop} {ρ : RegState} (h : RegsOK A R C ρ)
    {r : Reg} (hr : ¬ C r) {v : Expr} (hv : ∀ α ∈ v.syms, A α) :
    RegsOK A R C (ρ.set r v) := by
  refine ⟨fun r' hr' α hα => ?_, fun r' hr' => ?_⟩
  · rw [get_set] at hα; split at hα
    · exact hv α hα
    · exact h.1 r' hr' α hα
  · rw [get_set]; split
    · subst_vars; exact (hr hr').elim
    · exact h.2 r' hr'

/-- The continuation hypothesis: `κ` holds for every larger scope. -/
def KOK (Anc : List (List Nat)) (A : Sym → Prop) (R C : Reg → Prop) (κ : Cont) : Prop :=
  ∀ (B : Sym → Prop), (∀ α, A α → B α) → ∀ ρ φ, RegsOK B R C ρ → HoldsA (F := F) Anc B (κ ρ φ)

theorem KOK.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {R C : Reg → Prop} {κ : Cont}
    (h : KOK (F := F) Anc A R C κ) : KOK (F := F) Anc B R C κ :=
  fun D hBD => h D (fun α hα => hBD α (hAB α hα))

theorem mk_prefix {A : Sym → Prop} (ctx : Ctx) (pc : List Nat) (φ : List Guard)
    (kind : EventId → EventKind) (m : Event → Gen EventStructure)
    (hin : InThr F Anc pc) (hx : ∀ i, ∀ α ∈ (mkE ctx pc φ kind i).actSyms, A α)
    (hm : ∀ e, HoldsA (F := F) Anc (fun α => A α ∨ α = e.id) (m e)) :
    HoldsA (F := F) Anc A (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) := by
  intro σ
  exact Good.prefix hin (hx σ.nextId) (hm _ _)

/-! ## The invariant of `interp` -/

/-- The hypotheses on the subprogram `s` interpreted in a thread that reads the
    registers `R` and spawns threads with the registers `C`. -/
structure SubOK (out : List Reg) (R C : Reg → Prop) (s : Stmt) : Prop where
  loc  : s.RegsLocal out
  top  : ∀ r ∈ s.topRegs, R r
  par  : ∀ r ∈ s.parRegs, C r
  disj : ∀ r ∈ s.topRegs, ¬ C r

theorem forkSides_map {i : Nat} {gs : List (List Nat)} {s' : Stmt}
    (h : gs = s'.forkSides) (g : List Nat) (hg : g ∈ gs.map (i :: ·)) :
    ∃ g' ∈ s'.forkSides, g = i :: g' := by
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg; exact ⟨g', h ▸ hg', rfl⟩

theorem not_map_other {i j : Nat} (hij : i ≠ j) {gs : List (List Nat)} (g : List Nat)
    (hg : g ∈ gs.map (j :: ·)) (hp : [i] <+: g) : False := by
  obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
  simp [List.cons_prefix_cons] at hp; exact hij hp

open EventStructure in
theorem interp_good :
    ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (q : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard) (Anc : List (List Nat)) (A : Sym → Prop)
    (out : List Reg) (R C : Reg → Prop),
    sumB s.loops n + sizeOf s < N → SubOK out R C s → RegsOK A R C ρ → Pos F Anc q s →
    KOK (F := F) Anc A R C κ → HoldsA (F := F) Anc A (interp n ctx q s ρ κ φ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hN, _, _, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, q, s, ρ, κ, φ, Anc, A, out, R, C, hN, hs, hρ, hP, hκ => by
    have hin : InThr F Anc q := hP.inThr_nil
    have hat : ∀ w, s.forkSides = [] → InThr F Anc (q ++ w) := fun w h => hP.inThr_atom h w
    have hden : ∀ p : PExpr, (∀ r ∈ p.regs, r ∈ s.topRegs) → ∀ α ∈ (p.den ρ).syms, A α :=
      fun p hp => hρ.den p (fun r hr => hs.top r (hp r hr))
    have hnc : ∀ r ∈ s.topRegs, ¬ C r := hs.disj
    cases s with
    | skip => rw [interp.eq_def]; exact hκ A (fun _ h => h) ρ φ hρ
    | assign r e =>
        rw [interp.eq_def]
        exact hκ A (fun _ h => h) _ φ (hρ.set (hnc r (by simp [Stmt.topRegs]))
          (hden e (fun r hr => by simp [Stmt.topRegs, hr])))
    | addrOf r x =>
        rw [interp.eq_def]
        exact hκ A (fun _ h => h) _ φ (hρ.set (hnc r (by simp [Stmt.topRegs]))
          (by simp [Expr.glob, Expr.syms]))
    | load o r x vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx q φ _ _ hin
          (fun i α h => by simp [mkE, Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms] at h)
          (fun e => ?_)
        exact hκ _ ext_left _ φ ((hρ.mono ext_left).set (hnc r (by simp [Stmt.topRegs]))
          (by simp [Expr.syms]))
    | loadPtr o r p vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx q φ _ _ hin
          (fun i α h => hden p (fun r hr => by simp [Stmt.topRegs, hr]) α
            (by simpa [mkE, Event.actSyms, Event.exprSyms] using h))
          (fun e => ?_)
        exact hκ _ ext_left _ φ ((hρ.mono ext_left).set (hnc r (by simp [Stmt.topRegs]))
          (by simp [Expr.syms]))
    | store o x v vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx q φ _ _ hin (fun i α h => ?_)
          (fun e => hκ _ ext_left ρ φ (hρ.mono ext_left))
        simp only [mkE, Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms, List.nil_append] at h
        exact hden v (fun r hr => by simp [Stmt.topRegs, hr]) α h
    | storePtr o p v vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx q φ _ _ hin (fun i α h => ?_)
          (fun e => hκ _ ext_left ρ φ (hρ.mono ext_left))
        simp only [mkE, Event.actSyms, Event.exprSyms, List.mem_append] at h
        rcases h with h | h
        · exact hden p (fun r hr => by simp [Stmt.topRegs, hr]) α h
        · exact hden v (fun r hr => by simp [Stmt.topRegs, hr]) α h
    | fence o =>
        rw [interp.eq_def]
        exact mk_prefix ctx q φ _ _ hin
          (fun i α h => by simp [mkE, Event.actSyms, Event.exprSyms] at h)
          (fun e => hκ _ ext_left ρ φ (hρ.mono ext_left))
    | malloc r sz =>
        rw [interp.eq_def]
        refine mk_prefix ctx q φ _ _ hin
          (fun i α h => hden sz (fun r hr => by simp [Stmt.topRegs, hr]) α
            (by simpa [mkE, Event.actSyms, Event.exprSyms] using h))
          (fun e => ?_)
        exact hκ _ ext_left _ φ ((hρ.mono ext_left).set (hnc r (by simp [Stmt.topRegs]))
          (by simp [Expr.syms]))
    | free r =>
        rw [interp.eq_def]
        exact mk_prefix ctx q φ _ _ hin
          (fun i α h => hρ.1 r (hs.top r (by simp [Stmt.topRegs])) α
            (by simpa [mkE, Event.actSyms, Event.exprSyms, PExpr.den] using h))
          (fun e => hκ _ ext_left ρ φ (hρ.mono ext_left))
    | fadd or ow r x v =>
        rw [interp.eq_def]
        intro σ
        refine Good.addRMW (Good.prefix (hat _ rfl) (fun α hα => ?_)
          (Good.prefix (hat _ rfl) (fun α hα => ?_)
            (hκ _ (fun α h => .inl (.inl h)) _ φ ?_ _))) _ _ _
        · simp [Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms] at hα
        · simp only [Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms, List.nil_append,
            List.mem_append, List.mem_singleton] at hα
          rcases hα with h | h
          · exact .inr h
          · exact .inl (hden v (fun r hr => by simp [Stmt.topRegs, hr]) α h)
        · refine ((hρ.mono (fun α h => .inl (.inl h))).set (hnc r (by simp [Stmt.topRegs])) ?_)
          intro α h; simp only [Expr.syms, List.mem_singleton] at h; exact .inl (.inr h)
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        intro σ
        have hA1 : RegsOK (fun α => A α ∨ α = σ.nextId) R C ρ := hρ.mono ext_left
        have hrC : ¬ C r := hnc r (by simp [Stmt.topRegs])
        refine Good.addRMW (Good.prefix (hat _ rfl) (fun α hα => ?_)
          (Good.prefix (hat _ rfl) (fun α hα => ?_)
            (Good.plus
              (Good.prefix (hat _ rfl) (fun α hα => ?_)
                (hκ _ (fun α h => .inl (.inl (.inl h))) _ _ ?_ _))
              (hκ _ (fun α h => .inl (.inl h)) _ _ ?_ _)))) _ _ _
        · simp [Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms] at hα
        · simp only [Event.actSyms, Expr.syms, List.mem_append, List.mem_singleton] at hα
          rcases hα with h | h
          · exact .inr h
          · exact .inl (hden e₁ (fun r hr => by simp [Stmt.topRegs, hr]) α h)
        · simp only [Event.actSyms, Event.exprSyms, Expr.glob, Expr.syms, List.nil_append] at hα
          exact .inl (.inl (hden e₂ (fun r hr => by simp [Stmt.topRegs, hr]) α hα))
        · exact (hA1.mono (fun α h => .inl (.inl h))).set hrC (by simp [Expr.tt, Expr.syms])
        · exact (hA1.mono (fun α h => .inl h)).set hrC (by simp [Expr.ff, Expr.syms])
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        have hT := hs.loc
        simp only [Stmt.RegsLocal] at hT
        have h₁ : SubOK (out ++ s₂.regs) R C s₁ :=
          ⟨hT.1, fun r h => hs.top r (by simp [Stmt.topRegs, h]),
            fun r h => hs.par r (by simp [Stmt.parRegs, h]),
            fun r h => hs.disj r (by simp [Stmt.topRegs, h])⟩
        have h₂ : SubOK (out ++ s₁.regs) R C s₂ :=
          ⟨hT.2, fun r h => hs.top r (by simp [Stmt.topRegs, h]),
            fun r h => hs.par r (by simp [Stmt.parRegs, h]),
            fun r h => hs.disj r (by simp [Stmt.topRegs, h])⟩
        have hP₁ : Pos F Anc (q ++ [0]) s₁ := hP.sub fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_append] at hg
          rcases hg with hg | hg
          · exact forkSides_map rfl g hg
          · exact (not_map_other (by decide) g hg hp).elim
        have hP₂ : Pos F Anc (q ++ [1]) s₂ := hP.sub fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_append] at hg
          rcases hg with hg | hg
          · exact (not_map_other (by decide) g hg hp).elim
          · exact forkSides_map rfl g hg
        exact interp_good N n ctx (q ++ [0]) s₁ ρ _ φ Anc A _ R C (by omega) h₁ hρ hP₁
          (fun B hAB ρ' φ' hρ' => interp_good N n ctx (q ++ [1]) s₂ ρ' κ φ' Anc B _ R C
            (by omega) h₂ hρ' hP₂ (hκ.mono hAB))
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        intro σ
        have hT := hs.loc
        simp only [Stmt.RegsLocal] at hT
        -- each side is a thread of its own: it reads its registers, which the
        -- parent never assigned, and spawns threads with its nested ones
        have hside : ∀ (s' : Stmt) (out' : List Reg), s'.RegsLocal out' →
            (∀ r ∈ s'.regs, C r) →
            SubOK out' (· ∈ s'.topRegs) (· ∈ s'.parRegs) s' ∧
              RegsOK (fun _ => False) (· ∈ s'.topRegs) (· ∈ s'.parRegs) ρ :=
          fun s' out' hl hC => ⟨⟨hl, fun _ h => h, fun _ h => h, topRegs_not_parRegs s' _ hl⟩,
            ⟨fun r hr α hα => (by rw [hρ.2 r (hC r (topRegs_sub s' r hr))] at hα; cases hα),
              fun r hr => hρ.2 r (hC r (parRegs_sub s' r hr))⟩⟩
        obtain ⟨h₁, hρ₁⟩ := hside s₁ _ hT.2.2.1 (fun r h => hs.par r (by simp [Stmt.parRegs, h]))
        obtain ⟨h₂, hρ₂⟩ := hside s₂ _ hT.2.2.2 (fun r h => hs.par r (by simp [Stmt.parRegs, h]))
        have hP₁ : Pos F ((q ++ [0]) :: Anc) (q ++ [0]) s₁ := hP.fork fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | rfl | hg | hg
          · exact .inl rfl
          · simp at hp
          · exact .inr (forkSides_map rfl g hg)
          · exact (not_map_other (by decide) g hg hp).elim
        have hP₂ : Pos F ((q ++ [1]) :: Anc) (q ++ [1]) s₂ := hP.fork fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | rfl | hg | hg
          · simp at hp
          · exact .inl rfl
          · exact (not_map_other (by decide) g hg hp).elim
          · exact .inr (forkSides_map rfl g hg)
        exact Good.join (Good.plus
          (Good.forget (interp_good N n ctx (q ++ [0]) s₁ ρ _ φ _ _ _ _ _ (by omega) h₁ hρ₁ hP₁
            (fun _ _ _ _ _ _ => good_empty _) _))
          (Good.forget (interp_good N n _ (q ++ [1]) s₂ ρ _ φ _ _ _ _ _ (by omega) h₂ hρ₂ hP₂
            (fun _ _ _ _ _ _ => good_empty _) _)))
          (hκ A (fun _ h => h) ρ φ hρ _)
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        intro σ
        have hT := hs.loc
        simp only [Stmt.RegsLocal] at hT
        have hA1 : RegsOK (fun α => A α ∨ α = σ.nextId) R C ρ := hρ.mono ext_left
        have h₁ : SubOK _ R C s₁ :=
          ⟨hT.1, fun r h => hs.top r (by simp [Stmt.topRegs, h]),
            fun r h => hs.par r (by simp [Stmt.parRegs, h]),
            fun r h => hs.disj r (by simp [Stmt.topRegs, h])⟩
        have h₂ : SubOK _ R C s₂ :=
          ⟨hT.2, fun r h => hs.top r (by simp [Stmt.topRegs, h]),
            fun r h => hs.par r (by simp [Stmt.parRegs, h]),
            fun r h => hs.disj r (by simp [Stmt.topRegs, h])⟩
        have hP₁ : Pos F Anc (q ++ [0]) s₁ := hP.sub fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_append] at hg
          rcases hg with hg | hg
          · exact forkSides_map rfl g hg
          · exact (not_map_other (by decide) g hg hp).elim
        have hP₂ : Pos F Anc (q ++ [1]) s₂ := hP.sub fun g hg hp => by
          simp only [Stmt.forkSides, List.mem_append] at hg
          rcases hg with hg | hg
          · exact (not_map_other (by decide) g hg hp).elim
          · exact forkSides_map rfl g hg
        refine Good.prefix hin (fun α hα => ?_)
          (Good.plus (interp_good N n ctx _ s₁ ρ κ _ _ _ _ R C (by omega) h₁ hA1 hP₁
              (hκ.mono ext_left) _)
            (interp_good N n ctx _ s₂ ρ κ _ _ _ _ R C (by omega) h₂ hA1 hP₂
              (hκ.mono ext_left) _))
        simp only [Event.actSyms] at hα
        exact hden b (fun r hr => by simp [Stmt.topRegs, hr]) α hα
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => good_empty A
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          intro σ
          have hT := hs.loc
          simp only [Stmt.RegsLocal] at hT
          have hA1 : RegsOK (fun α => A α ∨ α = σ.nextId) R C ρ := hρ.mono ext_left
          have hb : SubOK _ R C body :=
            ⟨hT, fun r h => hs.top r (by simp [Stmt.topRegs, h]),
              fun r h => hs.par r (by simp [Stmt.parRegs, h]),
              fun r h => hs.disj r (by simp [Stmt.topRegs, h])⟩
          have hPb : Pos F Anc (q ++ [0]) body := hP.sub fun g hg _ => by
            simp only [Stmt.forkSides] at hg
            exact forkSides_map rfl g hg
          refine Good.prefix hin (fun α hα => ?_)
            (Good.plus
              (interp_good N (n.dec ℓ) _ _ body ρ _ _ _ _ _ R C (by omega) hb hA1 hPb
                (fun B hAB ρ' φ' hρ' => interp_good N (n.dec ℓ) _ q (.while ℓ b body) ρ' κ φ'
                  Anc B out R C
                  (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega) hs hρ' hP
                  (hκ.mono (fun α h => hAB α (.inl h)))) _)
              (hκ _ ext_left _ _ hA1 _))
          simp only [Event.actSyms] at hα
          exact hden b (fun r hr => by simp [Stmt.topRegs, hr]) α hα

end ThreadRegsDenote

open ThreadRegsDenote in
/-- **Registers local to a thread make events thread-local**
    (Condition `cond:thread-regs`). Under `Stmt.ThreadRegs`, every symbol of
    an event's location, value, size or condition is the id of an event
    `⊑`-before it in the same thread: every fork side of `P` contains both or
    neither. A child's events take no symbol from the parent before the fork
    or from a sibling; the parent's events after the join take none from its
    children. -/
theorem denote_threadLocal (n : Bounds) {P : Stmt} (hP : P.ThreadRegs) :
    ∀ e ∈ (denote n P).events, ∀ α ∈ e.actSyms, ∃ a ∈ (denote n P).events,
      a.id = α ∧ (α, e.id) ∈ (denote n P).po ∧ P.SameThread a.label.pc e.label.pc := by
  have hs : SubOK [] (fun _ => True) (· ∈ P.parRegs) P :=
    ⟨hP, fun _ _ => trivial, fun _ h => h, topRegs_not_parRegs P [] hP⟩
  have hρ : RegsOK (fun _ => False) (fun _ => True) (· ∈ P.parRegs) [] :=
    ⟨fun r _ α hα => (by simp [RegState.get, List.lookup, Expr.num, Expr.syms] at hα),
      fun r _ => by simp [RegState.get, List.lookup, Expr.num, Expr.syms]⟩
  have hPos : Pos P.forkSides [] [] P :=
    ⟨fun f hf hp => (forkSides_ne_nil P f hf (List.prefix_nil.1 hp)).elim,
      fun _ h => (by cases h), fun f hf _ => .inr ⟨f, hf, rfl⟩⟩
  have h := interp_good (F := P.forkSides) _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) []
    [] (fun _ => False) [] _ _ (Nat.lt_succ_self _) hs hρ hPos
    (fun _ _ _ _ _ _ => good_empty _) {}
  intro e he α hα
  rcases h e he α hα with h | ⟨a, ha, h1, h2, h3⟩
  · exact h.1.elim
  · exact ⟨a, ha, h1, h2, h3⟩

/-! ## Examples -/

namespace ThreadRegsExamples

/-- `r := x; (y := r ∥ skip)`: the child reads the parent's register. -/
def leakEx : Stmt :=
  .seq (.load .rlx "r" "x" false) (.par (.store .rlx "y" (.reg "r") false) .skip)

theorem leakEx_not_threadRegs : ¬ leakEx.ThreadRegs := by decide

/-- The child's write `y := α₀` takes the symbol of the parent's read, which no
    fork side separates from the program start: `cond:thread-regs` is needed
    for `denote_threadLocal`. -/
theorem leakEx_leaks : ¬ ∀ e ∈ (denote (.uniform 1) leakEx).events, ∀ α ∈ e.actSyms,
    ∃ a ∈ (denote (.uniform 1) leakEx).events, a.id = α ∧
      leakEx.SameThread a.label.pc e.label.pc := by
  decide +kernel

/-- `(r := x ∥ skip); y := r` and `(r := x ∥ y := r)` break the condition,
    yet no symbol crosses a fork side: the parent resumes with the register
    state it forked with, and each side starts from it, so a thread's reads
    reach neither its parent after the join nor its sibling. Only the
    parent's registers, handed to a child, carry symbols across (`leakEx`). -/
def joinEx : Stmt :=
  .seq (.par (.load .rlx "r" "x" false) .skip) (.store .rlx "y" (.reg "r") false)

def sibEx : Stmt :=
  .par (.load .rlx "r" "x" false) (.store .rlx "y" (.reg "r") false)

theorem joinEx_sibEx : ¬ joinEx.ThreadRegs ∧ ¬ sibEx.ThreadRegs := by decide

theorem joinEx_local : ∀ e ∈ (denote (.uniform 1) joinEx).events, ∀ α ∈ e.actSyms,
    ∃ a ∈ (denote (.uniform 1) joinEx).events, a.id = α ∧
      joinEx.SameThread a.label.pc e.label.pc := by
  decide +kernel

theorem sibEx_local : ∀ e ∈ (denote (.uniform 1) sibEx).events, ∀ α ∈ e.actSyms,
    ∃ a ∈ (denote (.uniform 1) sibEx).events, a.id = α ∧
      sibEx.SameThread a.label.pc e.label.pc := by
  decide +kernel

/-- `(r := x; y := r ∥ x := 1)`: the register moved into the child. -/
def localEx : Stmt :=
  .par (.seq (.load .rlx "r" "x" false) (.store .rlx "y" (.reg "r") false))
    (.store .rlx "x" (.num 1) false)

theorem localEx_threadRegs : localEx.ThreadRegs := by decide

/-- `r := x; if r = 0 then skip else skip; (y := 1 ∥ skip)`: registers local to
    their threads, yet the child's write is restricted by the parent's read:
    value restrictions are not covered. -/
def guardEx : Stmt :=
  .seq (.load .rlx "r" "x" false)
    (.seq (.ite (.eq (.reg "r") (.num 0)) .skip .skip)
      (.par (.store .rlx "y" (.num 1) false) .skip))

theorem guardEx_threadRegs : guardEx.ThreadRegs := by decide

theorem guardEx_parent : ∃ e ∈ (denote (.uniform 1) guardEx).events, ∃ α ∈ e.valres.syms,
    ∃ a ∈ (denote (.uniform 1) guardEx).events, a.id = α ∧
      ¬ guardEx.SameThread a.label.pc e.label.pc := by
  decide +kernel

/-- The library's examples with threads meet the condition: message passing,
    CoRR, a read after the join (`FwdAcrossJoin`), the guarded child of
    `GuardLoss`; and the single-threaded RCU routine. -/
example : PpoNecessity.mp.ThreadRegs ∧ PpoNecessity.corr.ThreadRegs ∧
    FwdAcrossJoin.prog.ThreadRegs ∧ GuardLoss.prog.ThreadRegs ∧ RoutineHyps.rcu1.ThreadRegs := by
  decide

end ThreadRegsExamples
