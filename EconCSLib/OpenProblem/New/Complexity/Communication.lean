/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.ResourceBounds



section

/-!
# Deterministic public-blackboard communication

Each `BitCommunicationTree` node sends exactly one bit at cost one. The public
transcript determines the sender and continuation; no timing, empty-message, or
secret-termination channel is available. Local computation is uncharged. Long messages
require multiple bit nodes.

This is a public-blackboard. See [Roughgarden, Communication Complexity (for Algorithm
Designers), §§4.2, 7.3], https://arxiv.org/abs/1509.06257.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench
universe u v w

/-!
## One communicated bit per step
-/

/-- An adaptive public-transcript tree with one-bit messages. -/
inductive BitCommunicationTree
    (Party : Type u) (PrivateInput : Party → Type v) (Output : Type w)
  | output (value : Output)
  | send (sender : Party)
      (bit : PrivateInput sender → Bool)
      (next : Bool → BitCommunicationTree Party PrivateInput Output)

/-- Execute a tree on fixed private inputs, returning output and public transcript. -/
def BitCommunicationTree.run
    {Party : Type u} {PrivateInput : Party → Type v} {Output : Type w}
    (profile : (party : Party) → PrivateInput party) :
    BitCommunicationTree Party PrivateInput Output →
      Output × List (Party × Bool)
  | .output value => (value, [])
  | .send sender bit next =>
      let value := bit (profile sender)
      let result := (next value).run profile
      (result.1, (sender, value) :: result.2)

/-- Every transcript entry records exactly one communicated bit. -/
def BitCommunicationTree.communicationCost
    {Party : Type u} {PrivateInput : Party → Type v} {Output : Type w}
    (tree : BitCommunicationTree Party PrivateInput Output)
    (profile : (party : Party) → PrivateInput party) : ℕ :=
  (tree.run profile).2.length

/-- A correct tree fixed before the entire private-input profile. -/
structure BitCommunicationProtocol
    (Party : Type u) (PrivateInput : Party → Type v) {Output : Type w}
    (function : ((party : Party) → PrivateInput party) → Output) where
  tree : BitCommunicationTree Party PrivateInput Output
  correct : ∀ profile, (tree.run profile).1 = function profile

/-- A fixed polynomial bound on communicated bits in the advertised size parameters. -/
def BitCommunicationProtocol.HasCommunicationBound
    {Party : Type u} {PrivateInput : Party → Type v} {Output : Type w}
    {function : ((party : Party) → PrivateInput party) → Output}
    (protocol : BitCommunicationProtocol Party PrivateInput function)
    (coefficient exponent : ℕ)
    (sizes : ((party : Party) → PrivateInput party) → List ℕ) : Prop :=
  ResourceBoundInSizes coefficient exponent sizes
    (fun profile => protocol.tree.communicationCost profile)

end EconCSLib.OpenProblem.New.EconCSBench

end
