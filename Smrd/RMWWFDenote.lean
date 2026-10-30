import Smrd.RoutineHyps
import Smrd.FwdEntailsRMW

/-!
# The RMWs of `⟨P⟩_n` are well-formed (`denote_rmwWF`)

`⟨P⟩_n` is `RMWWF`: the interpreter generates the read and the write of an
RMW in one step (`fadd`, `cas`), the read `⊑`-before the write, both at the
location `Expr.glob x` of the one variable the statement names. An RMW's
location is never a computed expression, so must-alias holds outright.

With `denote_po_trans` and `denote_po_irrefl` (`Smrd.RoutineHyps`), this
drops three hypotheses of `dep_po_R` for the event structures of programs
(`dep_po_R_denote`, `dep_po_R_of_phi_denote`). `PoForest` stays: `⊑` of
`⟨(a ∥ b); c⟩_n` puts both threads below `c` without ordering them, and it
cannot be dropped: `Smrd.FwdAcrossJoin` gives a program and a consistent
execution meeting every other hypothesis with `≼` across the two threads.
-/

namespace RMWWFDenote

open EventStructure Execution

/-- Every RMW entry of `k` has the shape `RMWShapeR`. -/
def RMWOK (k : EventStructure) : Prop :=
  ∀ ent ∈ k.rmw, RMWShapeR k ent.r ent.w

theorem shapeR_mono {k k' : EventStructure} (hsub : ∀ e ∈ k.events, e ∈ k'.events)
    (hpo : ∀ p ∈ k.po, p ∈ k'.po) {r w : EventId} (h : RMWShapeR k r w) : RMWShapeR k' r w := by
  obtain ⟨hp, er, her, ew, hew, h⟩ := h
  exact ⟨hpo _ hp, er, hsub er her, ew, hsub ew hew, h⟩

theorem rmwOK_inv : ESInvR RMWOK := by
  refine ⟨by simp [RMWOK, EventStructure.empty], fun e k hk => ?_,
    fun k k' hk hk' => ?_, fun k k' hk hk' => ?_, fun k r c w hk hs => ?_⟩
  · intro ent hent
    exact shapeR_mono (fun _ h => List.mem_cons_of_mem _ h)
      (fun _ h => List.mem_append_right _ h) (hk ent hent)
  · intro ent hent
    change ent ∈ k.rmw ++ k'.rmw at hent
    rw [List.mem_append] at hent
    rcases hent with h | h
    · exact shapeR_mono (fun _ h => List.mem_append_left _ h)
        (fun _ h => List.mem_append_left _ h) (hk ent h)
    · exact shapeR_mono (fun _ h => List.mem_append_right _ h)
        (fun _ h => List.mem_append_right _ h) (hk' ent h)
  · intro ent hent
    change ent ∈ k.rmw ++ k'.rmw at hent
    rw [List.mem_append] at hent
    rcases hent with h | h
    · exact shapeR_mono (fun _ h => List.mem_append_left _ h)
        (fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) (hk ent h)
    · exact shapeR_mono (fun _ h => List.mem_append_right _ h)
        (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) (hk' ent h)
  · intro ent hent
    change ent ∈ ⟨r, c, w⟩ :: k.rmw at hent
    rw [List.mem_cons] at hent
    rcases hent with rfl | h
    · exact hs
    · exact hk ent h

/-- **The RMWs of `⟨P⟩_n` are well-formed**: each read `⊑`-precedes its write,
    and the two must-alias. -/
theorem denote_rmwWF (n : Bounds) (P : Stmt) : Execution.RMWWF (denote n P) := by
  have hok := interp_invR rmwOK_inv _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) []
    (Nat.lt_succ_self _) (fun _ _ _ => rmwOK_inv.empty) {}
  intro ent hent
  obtain ⟨hp, er, her, ew, hew, hr, hw, -, -, l, hl₁, hl₂⟩ := hok ent hent
  refine ⟨hp, er, ew, l, l, hr ▸ denote_ev n P her, hw ▸ denote_ev n P hew, hl₁, hl₂,
    fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)⟩

variable {x : Execution}

/-- `dep_po_R` for `⟨P⟩_n`: `RMWWF` and the order properties of `⊑` hold. -/
theorem dep_po_R_denote {n : Bounds} {P : Stmt} {Ω : Pred} (hx : x.IsExecution (denote n P) Ω)
    (hF : PoForest (denote n P)) (hT : RMWTightR (denote n P) x)
    (hDP : ∀ a b, x.DP a b → (denote n P).poR a b) (hsat : Sat (x.P (denote n P)))
    (hev : LocsEval (denote n P)) (hE : FwdEntailsImg (denote n P) x) {a b : EventId}
    (h : x.dep (denote n P) a b) : x.poX (denote n P) a b :=
  dep_po_R hx (denote_po_trans n P) (denote_po_irrefl n P) hF hT hDP hsat hev hE
    (denote_rmwWF n P) h

/-- `dep_po_R_of_phi` for `⟨P⟩_n`. -/
theorem dep_po_R_of_phi_denote {n : Bounds} {P : Stmt} {Ω : Pred}
    (hx : x.IsExecution (denote n P) Ω) (hphi : x.phi (denote n P))
    (hF : PoForest (denote n P)) (hT : RMWTightR (denote n P) x)
    (hDP : ∀ a b, x.DP a b → (denote n P).poR a b) (hev : LocsEval (denote n P))
    (hE : FwdEntailsImg (denote n P) x) {a b : EventId} (h : x.dep (denote n P) a b) :
    x.poX (denote n P) a b :=
  dep_po_R_of_phi hx hphi (denote_po_trans n P) (denote_po_irrefl n P) hF hT hDP hev hE
    (denote_rmwWF n P) h

end RMWWFDenote
