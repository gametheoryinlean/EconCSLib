/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.FiniteMarkovChain
import Lean
import Lean.Replay

/-!
# Finite-chain computability and proof audit

Inspect declarations owned by both finite-chain library modules and the worked
example, including private and generated declarations. Reject noncomputable definitions, unsafe
or partial declarations other than Lean's recursive implementation helpers,
and axiom dependencies beyond Lean's standard logical axioms.
Replay the safe declarations into an environment containing only external
imports, so cached library proofs are checked by the kernel again.
-/

open Lean Elab Command

private def isFiniteChainModule (name : Name) : Bool :=
  (`EconCSLib.Math.Probability.FiniteMarkovChain).isPrefixOf name ||
  name == `EconCSLib.Examples.FiniteMarkovChain

elab "#audit_finite_chain" : command => do
  let env ← getEnv
  let executable ← liftIO <| importModules
    #[{ module := `EconCSLib.Math.Probability.FiniteMarkovChain }] {} 0
  for entry in executable.header.modules do
    if entry.module == `EconCSLib.Math.Probability.FiniteMarkovChain.Semantics ||
        entry.module == `EconCSLib.Examples.FiniteMarkovChain then
      throwError "Executable finite-chain import includes the semantic leaf or examples"
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut recursiveHelpers := 0
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let owner := (env.header.modules[index]!).module
      if isFiniteChainModule owner then
        if isNoncomputable env name then
          throwError "Noncomputable finite-chain declaration: {name}"
        if info.isUnsafe || info.isPartial then
          let some safeName := Compiler.isUnsafeRecName? name
            | throwError "Unsafe or partial finite-chain declaration: {name}"
          let safeInfo ← getConstInfo safeName
          -- A `partial def` has an opaque wrapper, not a total definition.
          unless (safeInfo matches .defnInfo _) &&
              !safeInfo.isUnsafe && !safeInfo.isPartial &&
              env.getModuleIdxFor? safeName == some index do
            throwError "Unsafe or partial finite-chain declaration: {safeName}"
          recursiveHelpers := recursiveHelpers + 1
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Forbidden finite-chain axiom dependency: {name} uses {axiomName}"
        declarations := declarations.insert name info
  if declarations.isEmpty then
    throwError "The finite-chain audit found no declarations"
  let imports := env.header.modules.filterMap fun entry =>
    if isFiniteChainModule entry.module then none
    else some ({ module := entry.module } : Import)
  let base ← liftIO <| importModules imports {} 0
  for (name, _) in declarations.toList do
    if base.contains name then
      throwError "The replay environment already contains {name}"
  let _ ← liftIO <| base.replay declarations
  logInfo m!"FiniteMarkovChain: {declarations.size} declarations; zero noncomputable declarations; \
    standard axiom dependencies; kernel replay passed for \
    {declarations.size - recursiveHelpers} safe declarations \
    ({recursiveHelpers} compiler recursion helpers excluded from replay)."

#audit_finite_chain
