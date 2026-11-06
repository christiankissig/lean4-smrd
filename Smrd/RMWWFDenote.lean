import Smrd.RoutineHyps
import Smrd.FwdEntailsRMW

/-!
# The RMWs of `⟨P⟩_n` are well-formed (`denote_rmwWF`)

`⟨P⟩_n` is `RMWWF`: the interpreter generates the read and the write of an
RMW in one step (`fadd`, `cas`), the read `⊑`-before the write, both at the
location `Expr.glob x` of the one variable the statement names. An RMW's
location is never a computed expression, so must-alias holds outright.

With `denote_po_trans` and `denote_po_irrefl` (`Smrd.RoutineHyps`) and
`denote_rmwFailGuard` (`Smrd.RMWTightDenote`), this drops four hypotheses of
`dep_po_R` for the event structures of programs (`dep_po_R_denote`,
`dep_po_R_of_phi_denote`, stated in `Smrd.RMWTightDenote`, which proves
`RMWFailGuard` from the invariant it keeps). `PoForest` is not needed
either: `⊑` of `⟨(a ∥ b); c⟩_n` puts both threads below `c` without ordering
them, and Forwarding's join restriction (`fwdNoJoin`) and Write Elision's
fork restriction (`weNoFork`, through the join condition `weNoJoin` it
implies) keep `≼` from relating them
(`Smrd.FwdAcrossJoin`, `Smrd.WEAcrossFork`).
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

end RMWWFDenote
