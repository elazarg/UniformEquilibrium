/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Stochastic.History
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Basic
import UniformEquilibrium.ProofView.Native.Basic

/-!
# Indexed and native public stochastic histories

The PMF proof view records completed stages in chronological `Fin` order and
stores the current state separately. GameTheory's canonical public history is
a reverse-chronological list of source/action/target records. The maps below
are exact on histories generated from an initial state and expose the policy
translations used by the semantic bridge.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open GameTheory.Math.Probability

namespace StochasticGame.NativeBridge

variable {ι : Type} (G : StochasticGame ι) [Finite G.State]

/-- Decode a reverse-chronological native public history into the indexed PMF
proof view. The empty history starts at `initial`; each newer record appends
one completed source/action pair and supplies the new current state. -/
def histOfPublicHistory (initial : G.State) :
    (history : G.toNative.PublicHistory) → G.Hist history.length
  | [] => G.emptyHist initial
  | record :: history =>
      let prior := histOfPublicHistory initial history
      (Fin.snoc prior.1 (record.source, record.joint), record.target)

@[simp]
theorem histOfPublicHistory_nil (initial : G.State) :
    histOfPublicHistory G initial [] = G.emptyHist initial :=
  rfl

@[simp]
theorem histOfPublicHistory_cons (initial : G.State)
    (record : G.toNative.StageRecord) (history : G.toNative.PublicHistory) :
    histOfPublicHistory G initial (record :: history) =
      (Fin.snoc (histOfPublicHistory G initial history).1
        (record.source, record.joint), record.target) :=
  rfl

/-- Decode a history with one oldest record at the statically simplified
successor length. -/
def histOfAppendSingleton (initial : G.State)
    (continuation : G.toNative.PublicHistory)
    (record : G.toNative.StageRecord) : G.Hist (continuation.length + 1) :=
  cast (congrArg G.Hist (by simp))
    (histOfPublicHistory G initial (continuation ++ [record]))

/-- A history paired with its horizon, so dependent history transformations
can be compared without exposing transports to policy clients. -/
abbrev PackedHist := Σ horizon, G.Hist horizon

/-- Append one completed native record to a packed indexed history. -/
def PackedHist.extend (history : PackedHist G)
    (record : G.toNative.StageRecord) : PackedHist G :=
  ⟨history.1 + 1,
    (Fin.snoc history.2.1 (record.source, record.joint), record.target)⟩

/-- Prefix one completed stage to a packed indexed continuation. -/
def PackedHist.prefix (stage : G.State × (∀ i, G.Act i))
    (history : PackedHist G) : PackedHist G :=
  ⟨history.1 + 1, G.consHist stage history.2⟩

/-- Decode a native public history as a horizon-indexed proof-view history. -/
def packedHistOfPublicHistory (initial : G.State) :
    G.toNative.PublicHistory → PackedHist G
  | [] => ⟨0, G.emptyHist initial⟩
  | record :: history =>
      PackedHist.extend G (packedHistOfPublicHistory initial history) record

@[simp]
theorem packedHistOfPublicHistory_nil (initial : G.State) :
    packedHistOfPublicHistory G initial [] = ⟨0, G.emptyHist initial⟩ :=
  rfl

@[simp]
theorem packedHistOfPublicHistory_cons (initial : G.State)
    (record : G.toNative.StageRecord) (history : G.toNative.PublicHistory) :
    packedHistOfPublicHistory G initial (record :: history) =
      PackedHist.extend G (packedHistOfPublicHistory G initial history) record :=
  rfl

/-- Extending after prefixing is prefixing after extending. -/
theorem PackedHist.extend_prefix (history : PackedHist G)
    (oldest : G.State × (∀ i, G.Act i))
    (latest : G.toNative.StageRecord) :
    PackedHist.extend G (PackedHist.prefix G oldest history) latest =
      PackedHist.prefix G oldest (PackedHist.extend G history latest) := by
  rcases history with ⟨horizon, history⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact (Fin.cons_snoc_eq_snoc_cons oldest history.1
        (latest.source, latest.joint)).symm
    · rfl

/-- Appending one oldest native record is exactly prefixing its completed
stage to the decoded continuation history. -/
theorem packedHistOfPublicHistory_append_singleton (initial : G.State)
    (continuation : G.toNative.PublicHistory)
    (record : G.toNative.StageRecord) :
    packedHistOfPublicHistory G initial (continuation ++ [record]) =
      PackedHist.prefix G (record.source, record.joint)
        (packedHistOfPublicHistory G record.target continuation) := by
  induction continuation with
  | nil =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · funext index
          exact Fin.eq_zero index ▸ rfl
        · rfl
  | cons latest continuation ih =>
      simp only [List.cons_append, packedHistOfPublicHistory_cons]
      rw [ih, PackedHist.extend_prefix]

/-- Encode an indexed proof-view history as a native reverse-chronological
public history. Intermediate targets are the next stored source state. -/
def publicHistoryOfHist : {horizon : ℕ} → G.Hist horizon → G.toNative.PublicHistory
  | 0, _ => []
  | horizon + 1, history =>
      let last := history.1 (Fin.last horizon)
      { source := last.1, joint := last.2, target := history.2 } ::
        publicHistoryOfHist
          (Fin.init history.1, last.1)

@[simp]
theorem publicHistoryOfHist_zero (history : G.Hist 0) :
    publicHistoryOfHist G history = [] :=
  rfl

@[simp]
theorem publicHistoryOfHist_length {horizon : ℕ} (history : G.Hist horizon) :
    (publicHistoryOfHist G history).length = horizon := by
  induction horizon with
  | zero => rfl
  | succ horizon ih =>
      simp only [publicHistoryOfHist, List.length_cons]
      rw [ih]

/-- Encoding and decoding a nonempty indexed history recovers its horizon and
all of its data exactly. -/
@[simp]
theorem packedHistOfPublicHistory_publicHistoryOfHist_succ
    (initial : G.State) {horizon : ℕ}
    (history : G.Hist (horizon + 1)) :
    packedHistOfPublicHistory G initial (publicHistoryOfHist G history) =
      ⟨horizon + 1, history⟩ := by
  induction horizon with
  | zero =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · funext index
          exact Fin.eq_zero index ▸ rfl
        · rfl
  | succ horizon ih =>
      let last := history.1 (Fin.last (horizon + 1))
      let priorHist : G.Hist (horizon + 1) :=
        (Fin.init history.1, last.1)
      let record : G.toNative.StageRecord :=
        { source := last.1, joint := last.2, target := history.2 }
      change PackedHist.extend G
          (packedHistOfPublicHistory G initial
            (publicHistoryOfHist G priorHist)) record = _
      rw [ih priorHist]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · change Fin.snoc (Fin.init history.1)
            (history.1 (Fin.last (horizon + 1))) = history.1
          exact Fin.snoc_init_self _
        · rfl

/-- The zero-stage round trip is exact at its stated initial state. -/
theorem packedHistOfPublicHistory_publicHistoryOfHist_zero
    (initial : G.State) (history : G.Hist 0) (hcurrent : history.2 = initial) :
    packedHistOfPublicHistory G initial (publicHistoryOfHist G history) =
      ⟨0, history⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · funext index
      exact Fin.elim0 index
    · exact hcurrent.symm

/-- Encode a packed indexed history without exposing its horizon. -/
def publicHistoryOfPackedHist (history : PackedHist G) :
    G.toNative.PublicHistory :=
  publicHistoryOfHist G history.2

/-- Encoding after appending one source-compatible completed record puts that
record at the front of the reverse-chronological public history. -/
@[simp]
theorem publicHistoryOfPackedHist_extend (history : PackedHist G)
    (record : G.toNative.StageRecord)
    (hsource : record.source = history.2.2) :
    publicHistoryOfPackedHist G (PackedHist.extend G history record) =
      record :: publicHistoryOfPackedHist G history := by
  rcases history with ⟨horizon, history⟩
  rcases record with ⟨source, joint, target⟩
  dsimp only at hsource
  subst source
  simp [publicHistoryOfPackedHist, PackedHist.extend, publicHistoryOfHist]

/-- Successive public records form one chronological path from `initial`. -/
def IsCoherentPublicHistory (initial : G.State) :
    G.toNative.PublicHistory → Prop
  | [] => True
  | record :: history =>
      IsCoherentPublicHistory initial history ∧
        record.source = (packedHistOfPublicHistory G initial history).2.2

/-- Successive public records form a path from `initial`, and every recorded
transition has positive mass in the proof-view kernel. -/
def IsRealizablePublicHistory (initial : G.State) :
    G.toNative.PublicHistory → Prop
  | [] => True
  | record :: history =>
      IsRealizablePublicHistory initial history ∧
        record.source = (packedHistOfPublicHistory G initial history).2.2 ∧
        record.target ∈ (G.transition record.source record.joint).support

/-- Realizability strengthens source coherence. -/
theorem isCoherentPublicHistory_of_isRealizablePublicHistory
    (initial : G.State) (history : G.toNative.PublicHistory)
    (hrealizable : IsRealizablePublicHistory G initial history) :
    IsCoherentPublicHistory G initial history := by
  induction history with
  | nil => trivial
  | cons record history ih =>
      exact ⟨ih hrealizable.1, hrealizable.2.1⟩

/-- Encoding a coherent decoded public history recovers it exactly. -/
theorem publicHistoryOfPackedHist_packedHistOfPublicHistory
    (initial : G.State) (history : G.toNative.PublicHistory)
    (hcoherent : IsCoherentPublicHistory G initial history) :
    publicHistoryOfPackedHist G
        (packedHistOfPublicHistory G initial history) = history := by
  induction history with
  | nil => rfl
  | cons record history ih =>
      rcases hcoherent with ⟨hcoherent, hsource⟩
      rw [packedHistOfPublicHistory_cons,
        publicHistoryOfPackedHist_extend G _ _ hsource, ih hcoherent]

/-- Decoding a canonical trace ends at the trace's actual state. -/
theorem packedHistOfPublicHistory_trace_current (initial : G.State)
    [∀ i, Nonempty (G.Act i)] :
    ∀ {state : G.State}
      (trace : (G.toNative.toExecution initial).Trace state),
      (packedHistOfPublicHistory G initial
        (G.toNative.publicHistoryOfTrace initial trace)).2.2 = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- Erasing a canonical Protocol event to a stochastic stage record preserves
its positive-support transition witness in the PMF proof view. -/
theorem stageRecordOfEvent_target_mem_proofView_transition_support
    (initial : G.State) [∀ i, Nonempty (G.Act i)]
    (event : (G.toNative.toExecution initial).StepEvent) :
    (G.toNative.stageRecordOfEvent initial event).target ∈
      (G.transition
        (G.toNative.stageRecordOfEvent initial event).source
        (G.toNative.stageRecordOfEvent initial event).joint).support := by
  change event.target ∈
    (G.toNative.transition event.source
      (G.toNative.stageRecordOfEvent initial event).joint).support
  exact
    GameTheory.Stochastic.Game.stageRecordOfEvent_target_mem_transition_support
      G.toNative initial event

/-- Full public monitoring has perfect recall: equality of the complete public
record determines every player's own information/action record. -/
theorem toNative_perfectMonitoring_perfectRecall (initial : G.State)
    [∀ i, Nonempty (G.Act i)] :
    (G.toNative.perfectMonitoring initial).PerfectRecall := by
  intro i first second firstTrace
  induction firstTrace generalizing second with
  | start =>
      intro secondTrace hinfo
      cases secondTrace with
      | start => rfl
      | extend prior joint isLegal realized =>
          rw [G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace,
            G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace] at hinfo
          simp at hinfo
  | @extend source target prior joint isLegal realized ih =>
      intro secondTrace hinfo
      cases secondTrace with
      | start =>
          rw [G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace,
            G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace] at hinfo
          simp at hinfo
      | @extend secondSource secondTarget secondPrior secondJoint
          secondIsLegal secondRealized =>
          rw [G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace,
            G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace] at hinfo
          have hrecords := (List.cons.inj hinfo).1
          have hpriorPublic := (List.cons.inj hinfo).2
          have hpriorInfo :
              (G.toNative.perfectMonitoring initial).infoOf i prior =
                (G.toNative.perfectMonitoring initial).infoOf i secondPrior := by
            rw [G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace,
              G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace]
            exact hpriorPublic
          have hfirstJoint :=
            G.toNative.event_joint_eq_some_stageRecordOfEvent_joint initial
              ⟨source, joint, isLegal, target, realized⟩
          have hsecondJoint :=
            G.toNative.event_joint_eq_some_stageRecordOfEvent_joint initial
              ⟨secondSource, secondJoint, secondIsLegal,
                second, secondRealized⟩
          have haction :
              (G.toNative.stageRecordOfEvent initial
                  ⟨source, joint, isLegal, target, realized⟩).joint i =
                (G.toNative.stageRecordOfEvent initial
                  ⟨secondSource, secondJoint, secondIsLegal,
                    second, secondRealized⟩).joint i :=
            congrArg (fun record => record.joint i) hrecords
          have hfirstJointAt := congrFun hfirstJoint i
          have hsecondJointAt := congrFun hsecondJoint i
          change joint i = _ at hfirstJointAt
          change secondJoint i = _ at hsecondJointAt
          rw [GameTheory.Protocol.InfoSignals.ownPlay_extend,
            GameTheory.Protocol.InfoSignals.ownPlay_extend,
            hfirstJointAt, hsecondJointAt]
          exact congrArg₂ List.cons (Prod.ext hpriorInfo haction)
            (ih secondPrior hpriorInfo)

/-- Every public history projected from GameTheory's Protocol runner is a
source-coherent path of positive-support proof-view transitions. -/
theorem isRealizablePublicHistory_publicHistoryOfTrace (initial : G.State)
    [∀ i, Nonempty (G.Act i)] :
    ∀ {state : G.State}
      (trace : (G.toNative.toExecution initial).Trace state),
      IsRealizablePublicHistory G initial
        (G.toNative.publicHistoryOfTrace initial trace)
  | _, .start => trivial
  | _, .extend prior joint isLegal realized => by
      rw [G.toNative.publicHistoryOfTrace_extend]
      refine ⟨isRealizablePublicHistory_publicHistoryOfTrace initial prior,
        (packedHistOfPublicHistory_trace_current G initial prior).symm, ?_⟩
      exact stageRecordOfEvent_target_mem_proofView_transition_support
        G initial ⟨_, joint, isLegal, _, realized⟩

/-- Every public history projected from GameTheory's Protocol runner is
coherent. -/
theorem isCoherentPublicHistory_publicHistoryOfTrace (initial : G.State)
    [∀ i, Nonempty (G.Act i)] :
    ∀ {state : G.State}
      (trace : (G.toNative.toExecution initial).Trace state),
      IsCoherentPublicHistory G initial
        (G.toNative.publicHistoryOfTrace initial trace)
  | _, trace =>
      isCoherentPublicHistory_of_isRealizablePublicHistory G initial _
        (isRealizablePublicHistory_publicHistoryOfTrace G initial trace)

/-- Decode an encoded indexed history at its statically known horizon. -/
def decodedEncodedHist (initial : G.State) {horizon : ℕ}
    (history : G.Hist horizon) : G.Hist horizon :=
  cast (congrArg G.Hist (publicHistoryOfHist_length G history))
    (histOfPublicHistory G initial (publicHistoryOfHist G history))

/-- Compile one PMF behavior strategy to an ordinary native public policy. -/
def toNativePublicPolicy {i : ι} [Finite (G.Act i)]
    (initial : G.State) (strategy : G.BehaviorStrategy i) :
    G.toNative.PublicPolicy i :=
  fun history =>
    let decoded := packedHistOfPublicHistory G initial history
    finDistOfPMF (strategy decoded.1 decoded.2)

/-- Compile a PMF behavior profile to ordinary native public policies. -/
def toNativePublicProfile [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (initial : G.State)
    (profile : G.BehaviorProfile) : G.toNative.PublicProfile initial :=
  fun i => toNativePublicPolicy G initial (profile i)

@[simp]
theorem toNativePublicProfile_toPMF [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (initial : G.State)
    (profile : G.BehaviorProfile) (i : ι)
    (history : G.toNative.PublicHistory) :
    ((toNativePublicProfile G initial profile i history).toPMF) =
      let decoded := packedHistOfPublicHistory G initial history
      profile i decoded.1 decoded.2 :=
  rfl

/-- Shifting the native public policy past one realized record is exactly the
translation of the proof-view continuation profile. -/
theorem toNativePublicProfile_after_record [Fintype ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (initial : G.State) (profile : G.BehaviorProfile)
    (record : G.toNative.StageRecord) :
    Stochastic.Game.PublicProfile.after
        (toNativePublicProfile G initial profile) [record] =
      toNativePublicProfile G record.target
        (G.shiftProfile profile (record.source, record.joint)) := by
  funext i continuation
  apply FinDist.ext
  simp only [Stochastic.Game.PublicProfile.after_apply,
    toNativePublicProfile, toNativePublicPolicy, toPMF_finDistOfPMF]
  rw [packedHistOfPublicHistory_append_singleton]
  rfl

/-- Compile a PMF behavior profile all the way to GameTheory's canonical
perfect-monitoring behavioral profile. -/
def toNativeBehaviorProfile [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (initial : G.State)
    (profile : G.BehaviorProfile) : G.toNative.BehaviorProfile initial :=
  G.toNative.toBehaviorProfile initial
    (toNativePublicProfile G initial profile)

/-- Decode one ordinary native public policy into the indexed PMF proof
view. -/
def ofNativePublicPolicy {i : ι} (policy : G.toNative.PublicPolicy i) :
    G.BehaviorStrategy i :=
  fun _ history => (policy (publicHistoryOfHist G history)).toPMF

/-- Decode ordinary native public policies into the indexed PMF proof view. -/
def ofNativePublicProfile [∀ i, Nonempty (G.Act i)] (_initial : G.State)
    (profile : G.toNative.PublicProfile _initial) : G.BehaviorProfile :=
  fun i => ofNativePublicPolicy G (profile i)

@[simp]
theorem ofNativePublicProfile_apply [∀ i, Nonempty (G.Act i)]
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (i : ι) {horizon : ℕ} (history : G.Hist horizon) :
    ofNativePublicProfile G initial profile i horizon history =
      (profile i (publicHistoryOfHist G history)).toPMF :=
  rfl

/-- Decoding and recompiling one native public policy recovers it on every
coherent public history. -/
theorem toNativePublicPolicy_ofNativePublicPolicy_of_coherent
    {i : ι} [Finite (G.Act i)] (initial : G.State)
    (policy : G.toNative.PublicPolicy i)
    (history : G.toNative.PublicHistory)
    (hcoherent : IsCoherentPublicHistory G initial history) :
    toNativePublicPolicy G initial (ofNativePublicPolicy G policy) history =
      policy history := by
  apply FinDist.ext
  simp only [toNativePublicPolicy, ofNativePublicPolicy,
    toPMF_finDistOfPMF]
  change (policy (publicHistoryOfPackedHist G
      (packedHistOfPublicHistory G initial history))).toPMF = _
  rw [publicHistoryOfPackedHist_packedHistOfPublicHistory
    G initial history hcoherent]

/-- Decoding and recompiling a native public profile recovers it on every
coherent public history. -/
theorem toNativePublicProfile_ofNativePublicProfile_of_coherent
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (i : ι) (history : G.toNative.PublicHistory)
    (hcoherent : IsCoherentPublicHistory G initial history) :
    toNativePublicProfile G initial
        (ofNativePublicProfile G initial profile) i history =
      profile i history := by
  exact toNativePublicPolicy_ofNativePublicPolicy_of_coherent
    G initial (profile i) history hcoherent

end StochasticGame.NativeBridge

end GameTheory
