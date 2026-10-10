/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw
import Lean
import Lean.Replay

/-!
# Finite-law computability and proof audit

Inspect all declarations owned by the finite-law import closure, including
private and generated declarations. Reject noncomputable definitions, unsafe
or partial declarations other than Lean's recursive implementation helpers,
and axiom dependencies beyond Lean's standard logical axioms.
Replay the safe declarations into an environment containing only external
imports, so cached library proofs are checked by the kernel again.
-/

open Lean Elab Command

private def isFiniteLawModule (name : Name) : Bool :=
  (`EconCSLib.Math.Probability.FiniteLaw).isPrefixOf name

elab "#audit_finite_law" : command => do
  let env ← getEnv
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut recursiveHelpers := 0
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let owner := (env.header.modules[index]!).module
      if isFiniteLawModule owner then
        if isNoncomputable env name then
          throwError "Noncomputable finite-law declaration: {name}"
        if info.isUnsafe || info.isPartial then
          let some safeName := Compiler.isUnsafeRecName? name
            | throwError "Unsafe or partial finite-law declaration: {name}"
          let safeInfo ← getConstInfo safeName
          -- A `partial def` has an opaque wrapper, not a total definition.
          unless (safeInfo matches .defnInfo _) &&
              !safeInfo.isUnsafe && !safeInfo.isPartial &&
              env.getModuleIdxFor? safeName == some index do
            throwError "Unsafe or partial finite-law declaration: {safeName}"
          recursiveHelpers := recursiveHelpers + 1
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Forbidden finite-law axiom dependency: {name} uses {axiomName}"
        declarations := declarations.insert name info
  if declarations.isEmpty then
    throwError "The finite-law audit found no declarations"
  let imports := env.header.modules.filterMap fun entry =>
    if isFiniteLawModule entry.module then none
    else some ({ module := entry.module } : Import)
  let base ← liftIO <| importModules imports {} 0
  for (name, _) in declarations.toList do
    if base.contains name then
      throwError "The replay environment already contains {name}"
  let _ ← liftIO <| base.replay declarations
  logInfo m!"FiniteLaw: {declarations.size} declarations; zero noncomputable declarations; \
    standard axiom dependencies; kernel replay passed for \
    {declarations.size - recursiveHelpers} safe declarations \
    ({recursiveHelpers} compiler recursion helpers excluded from replay)."

#audit_finite_law
