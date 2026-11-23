import Smrd.DPPast
import Smrd.FwdEntails

/-!
# Dependencies are thread-internal

The model does not assume that `dep = DP ∪ ≼` refines program order:
Strengthening (`Generated.str`, sMRD's Def. 4.11) admits origins on either side
of the justified write, and `DP` then runs against `⊑` within a thread
(`Smrd.StrBack`). The model's assumption is that `dep` is *thread-internal*:
every pair of `DP ∪ ≼` relates `⊑`-comparable (or equal) events,
`ThreadInternal`. This module proves it.

## The notion of thread

"Same thread" is read as `PoCmp`: `a = b ∨ a ⊑ b ∨ b ⊑ a`. Among the events of
an execution, which are conflict-free, two events are incomparable exactly
when they lie in different threads of a parallel composition (events on two
outcomes of a branching conflict and are never both in `X`). After a join, the
continuation is comparable with both threads, as is the code before a fork:
the order already says what "the same thread" means, and the library's
restrictions on forwarding and elision (`fwdNoJoin`, `weNoJoin`, `Anchored`)
are stated in it. Two other notions are available and are not used:

* thread ids (`Event.thread`): `⟨P₁ ∥ P₂⟩` gives `P₁` the parent's id, so the
  initialising prefix and the first thread share one id while the second
  thread does not. Ids neither separate the prefix from the threads nor say
  anything the generation rules can see;
* segments: not part of the library on `main`.

## Results

* `Generated.joinPast` (`Smrd.DPPast`): every symbol of a generated
  justification has its origin *joinable* with the write (a common `⊑`-upper
  bound), given `SymWF` and the store-store forwarding window (`FwdWin`), with
  no hypothesis on the shape of `⊑`. So `DP ⊆ Joinable`
  (`Execution.dp_joinable`), and where `⊑` is a forest (`PoForest`, no code
  after a join) `DP` is thread-internal (`Execution.dp_thread`).
* `Execution.ppo_po_E`: `≼ ⊆ ⊑` under `FwdEntailsImg`, without any hypothesis
  on `DP`: Strengthening's order condition plays no role for `≼`.
* `Execution.dep_thread`: `DP ∪ ≼` thread-internal under `PoForest`, the
  window and `≼ ⊆ ⊑`; `Execution.dep_thread_E`, `dep_thread_E_of_phi` with
  `≼ ⊆ ⊑` from `FwdEntailsImg`.
* Where `DP ⊆ ⊑` is needed, the results take it as a hypothesis, or derive it
  for justifications of the variant `GeneratedPast` (origins `⊑`-before the
  write; pre-justifications among them): `Execution.dp_po`.

## Where the hypotheses are needed

* `PoForest`: with code after a join, Strengthening and Forwarding
  together move a symbol across threads. In `(w ∥ r := x); y := r; s := y`
  with `w` in the first thread, strengthening `w` with the read `s := y` of the
  continuation (`w ⊑ s`), then store-forwarding `s` from `y := r`, replaces
  `s`'s symbol by `r`'s, from the second thread. `fwdNoJoin` admits it: every
  event `⊑`-below `s` is comparable with `y := r`. Under `GeneratedPast` the
  origin `s` lies `⊑`-before `w` and the forwarded value's symbols with it
  (`GeneratedPast.past`). Not mechanised.
* `FwdWin`: store-store forwarding replaces the *expression* `val(e₂)`, which
  can occur in `P` without `e₂` being related to `w` at all; without the window
  it brings in origins of another thread.
* `≼`: the closure of `≼` composes steps, and comparability is not transitive:
  a step `⊑`-backwards from one thread into the code before a fork, followed by
  a step forwards into a sibling thread, crosses threads. Backward steps come
  from remapping (`Smrd.FwdAcrossAlias`), and `FwdEntailsImg` excludes them.
  Without a segment restriction on Forwarding (a forwarding from the
  initialising prefix into a thread is admitted by `fwdNoJoin`) the library has
  no weaker hypothesis that keeps `≼` thread-internal.
-/

namespace Execution

open EventStructure

variable {es : EventStructure} {x : Execution}

/-- A relation is **thread-internal** if it relates `⊑`-comparable events
    only, or an event to itself. -/
def ThreadInternal (es : EventStructure) (R : Rel) : Prop := ∀ a b, R a b → es.PoCmp a b

/-- `⊑`-forward relations are thread-internal. -/
theorem threadInternal_of_po {R : Rel} (h : ∀ a b, R a b → es.poR a b) : ThreadInternal es R :=
  fun a b hab => .inr (.inl (h a b hab))

/-- **`DP` relates joinable events**: every dependency has a common
    `⊑`-upper bound with its write, given `SymWF` and the store-store
    forwarding window. No hypothesis on the shape of `⊑`. -/
theorem dp_joinable {Ω : Pred} (hJ : ∀ j ∈ x.J, es.Generated Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ∀ a b, x.DP a b → es.Joinable a b := by
  rintro a b ⟨-, -, j, hj, rfl, hab⟩
  exact (hJ j hj).joinPast hwf hpo (hW j hj) a
    (by rcases hab with h | h; exact .inl h; exact .inr (.inl h))

/-- **`DP` is thread-internal** where `⊑` is a forest: Strengthening's origins
    on either side of the write stay in the write's thread. -/
theorem dp_thread {Ω : Pred} (hJ : ∀ j ∈ x.J, es.Generated Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ThreadInternal es x.DP := fun a b h => by
  obtain ⟨d, ha, hb⟩ := dp_joinable hJ hwf hpo hW a b h
  exact hF a b d ha hb

/-- **`≼ ⊆ ⊑` under `FwdEntailsImg`**, with no hypothesis on `DP`. -/
theorem ppo_po_E {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hR : NoRevRMW es x)
    {a b : EventId} (h : x.ppo es a b) : es.poR a b :=
  ppo_po hpo_trans (fun _ _ h => ppoStep_po_E hx hpo_trans hirr hT hsat hev hE hR h) h

/-- **`DP ∪ ≼` is thread-internal**, where `⊑` is a forest, given `SymWF`, the
    forwarding window, and `≼ ⊆ ⊑`. -/
theorem dep_thread {Ω : Pred} (hJ : ∀ j ∈ x.J, es.Generated Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    (hW : ∀ j ∈ x.J, es.FwdWin j) (hppo : ∀ a b, x.ppo es a b → es.poR a b) :
    ThreadInternal es (x.dep es) := by
  rintro a b (h | h)
  · exact .inr (.inl (hppo a b h))
  · exact dp_thread hJ hwf hpo hF hW a b h

/-- **`DP ∪ ≼` is thread-internal for executions**, with `≼ ⊆ ⊑` from
    `FwdEntailsImg` (`ppo_po_E`). -/
theorem dep_thread_E {Ω : Pred} (hx : x.IsExecution es Ω) (hwf : es.SymWF)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x) (hF : PoForest es)
    (hFW : ∀ j ∈ x.J, es.FwdWin j)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hR : NoRevRMW es x) :
    ThreadInternal es (x.dep es) :=
  dep_thread hx.generated hwf hpo_trans hF hFW
    (fun _ _ h => ppo_po_E hx hpo_trans hirr hT hsat hev hE hR h)

/-- `dep_thread_E` from a consistent execution: `φ` gives the model of `P`. -/
theorem dep_thread_E_of_phi {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hwf : es.SymWF) (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x) (hF : PoForest es)
    (hFW : ∀ j ∈ x.J, es.FwdWin j) (hev : LocsEval es) (hE : FwdEntailsImg es x)
    (hR : NoRevRMW es x) : ThreadInternal es (x.dep es) :=
  dep_thread_E hx hwf hpo_trans hirr hT hF hFW
    (by obtain ⟨-, -, f, hf, -⟩ := hphi; exact ⟨f, hf⟩) hev hE hR

end Execution
