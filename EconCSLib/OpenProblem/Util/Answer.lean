/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public meta import Lean.Elab.SyntheticMVars
public import EconCSLib.OpenProblem.Util.AnswerSyntax

import Batteries.Lean.Expr

/-!
# The `answer()` elaborator for EconCSLib open problems

This file provides syntax for marking answers in open-problem statements.

It is adapted from `FormalConjectures.Util.Answer` in
`google-deepmind/formal-conjectures`. EconCSLib keeps the mechanism opt-in under
`EconCSLib.OpenProblem` and uses the option `econcslib.answer`.

`answer(sorry)` is a marker for an unresolved mathematical answer. Replacing it
with a term is not the same as proving the problem: whether the supplied answer
is mathematically meaningful remains a human judgment.
-/

public meta section

namespace EconCSLib.OpenProblem

open Lean Elab Meta Term

/-- A type that captures the current setting for the `answer()` elaborator. -/
inductive AnswerSetting
  /-- Default mode: `answer(sorry)` defaults to `True` when `sorry` has type `Prop`. -/
  | alwaysTrue
  /-- Default mode for `answer(foo)`: postpone elaboration. -/
  | postpone
  /-- Elaborate `answer(foo)` by creating an auxiliary definition with value `foo`. -/
  | withAuxiliary
deriving Inhabited, ToJson, BEq

instance : ToString AnswerSetting where
  toString
    | .postpone => "postpone"
    | .withAuxiliary => "with_auxiliary"
    | .alwaysTrue => "always_true"

instance : KVMap.Value AnswerSetting where
  toDataValue := DataValue.ofString ∘ ToString.toString
  ofDataValue?
    | .ofString "postpone" => some .postpone
    | .ofString "with_auxiliary" => some .withAuxiliary
    | .ofString "always_true" => some .alwaysTrue
    | _ => none

register_option econcslib.answer : AnswerSetting := {
  defValue := .alwaysTrue
  descr := "Modifies the behaviour of the EconCSLib open-problem answer() elaborator."
}

def mkAnswerAnnotation (e : Expr) : Expr := mkAnnotation `answer e

/-- Find the first subexpression carrying the `answer` annotation,
returning the inner expression if found. -/
def findAnswerExpr (e : Expr) : Option Expr :=
  (e.find? fun
    | .mdata m _ => m.contains `answer
    | _ => false).map Expr.mdataExpr!

/-- Collect all subexpressions carrying the `answer` annotation,
returning the inner expressions. -/
partial def findAnswerExprs (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .mdata m inner =>
      go inner (if m.contains `answer then acc.push inner else acc)
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | _ => acc

def elabTermAndAnnotate (stx : TSyntax `term) (expectedType? : Option Expr)
    (postpone : Bool := false) :=
  mkAnswerAnnotation <$> do
    if postpone then
      postponeElabTerm (← `(by exact $stx)) expectedType?
    else
      elabTerm stx expectedType?

/-- Indicates where the answer is in an open-problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    match econcslib.answer.get (← getOptions) with
    | AnswerSetting.postpone => elabTermAndAnnotate a expectedType? true
    | .withAuxiliary =>
      let expr ← elabTermAndSynthesize a expectedType?
      let exprType ← (Meta.inferType expr) >>= instantiateMVars
      if exprType.hasExprMVar then throwPostpone
      let some declName := (← read).declName?
        | throwError "Failed to find the name of the declaration"
      let answerName : Name := declName.str "_answer"
      let levelParamNames : List Name := (collectLevelParams {} exprType).params.toList
      let answerAuxiliaryDecl : DefinitionVal := {
        name := answerName
        levelParams := levelParamNames
        type := exprType
        value := expr
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl answerAuxiliaryDecl) true
      return mkAnswerAnnotation (.const answerName <| levelParamNames.map Level.param)
    | .alwaysTrue =>
      if expectedType? == some (Expr.sort .zero) && a == (← `(term| sorry)) then
        return .const `True []
      else
        elabTermAndAnnotate a expectedType? true
  | _ => Elab.throwUnsupportedSyntax

open InfoTree

/-- An answer term and the context in which it was elaborated. -/
structure AnswerInfo where
  ctx : Elab.ContextInfo
  term : Elab.TermInfo

/-- Print an answer. -/
def AnswerInfo.format (a : AnswerInfo) : Elab.Term.TermElabM MessageData :=
  Meta.withMCtx a.ctx.mctx <| Meta.withLCtx a.term.lctx {} do
    let t ← Meta.inferType a.term.expr
    let m ← Meta.mkFreshExprMVar t
    addMessageContextFull m!"{a.term.expr} in context:{indentD m.mvarId!}"

/-- Find answers by inspecting an `InfoTree`. -/
partial def getAnswers {m} [Monad m] (i : InfoTree) : m (Array AnswerInfo) :=
  go none i
where
  go : _ → InfoTree → _
  | ctx?, context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | some ctx, node i cs => do
    let ctx := i.updateContext? ctx
    if let .ofTermInfo t := i then
      if t.elaborator == ``answerElab then
        if let some ctx := ctx then
          return #[⟨ctx, t⟩]
    return (← cs.mapM (go <| i.updateContext? ctx)).toArray.flatten
  | _, _ => pure #[]

end EconCSLib.OpenProblem
