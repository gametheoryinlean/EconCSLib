/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly

/-!
# Presentation.Chance.ProfileAssembly — finite-law player-profile assembly

This module is the exact compatibility seam between the established
`ObservedChanceGame.MeasurablePresentation` API and the general measurable
player-kernel assembler.

An explicit measurable `InformationRoles` certificate is still required:
measurable ownership cannot be recovered from the old local correctness
equations alone. Given that certificate and one reference behavioral profile,
`profileAssembly` reuses the old profile's fixed abstract chance lift.

Every finite-law behavioral profile can then be split into tagged player kernels
and reassembled. The resulting compiled event policy is exactly the old
compiled policy.
-/

namespace ExtensiveGame.ObservedChanceGame

open MeasureTheory ProbabilityTheory

universe uN uU

variable {N : Type uN} {U : Type uU}

namespace MeasurablePresentation

variable
  {G : ObservedChanceGame N U}
  {model : MeasurableHistoryModel G}

/-- Construct measurable player-profile assembly data for a finite-law
presentation. The reference profile supplies only the abstract chance lift;
the realized chance law remains the presentation's fixed law. -/
def profileAssembly
    (presentation : MeasurablePresentation G model)
    (roles :
      presentation.toKernelPresentation.InformationRoles)
    (reference : G.observed.BehavioralProfile) :
    presentation.toKernelPresentation.ProfileAssembly :=
  ObservedGame.MeasurableKernelPresentation.ProfileAssembly.ofReference
    roles
    (presentation.toKernelBehavioralProfile reference)

/-- Splitting and reassembling a finite-law profile preserves its original
compiled event policy exactly. -/
theorem profileAssembly_split_reassembly_compiledPolicy
    (presentation : MeasurablePresentation G model)
    (roles :
      presentation.toKernelPresentation.InformationRoles)
    (reference profile : G.observed.BehavioralProfile) :
    let assembly :=
      presentation.profileAssembly roles reference
    (assembly.toKernelBehavioralProfile
        (ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.ofKernelBehavioralProfile
          (assembly := assembly)
          (presentation.toKernelBehavioralProfile profile))).compiledPolicy =
      presentation.compiledPolicy profile := by
  dsimp only
  rw [
    ObservedGame.MeasurableKernelPresentation.ProfileAssembly.toKernelBehavioralProfile_ofKernelBehavioralProfile_compiledPolicy]
  exact presentation.toKernelBehavioralProfile_compiledPolicy profile

end MeasurablePresentation

end ExtensiveGame.ObservedChanceGame
