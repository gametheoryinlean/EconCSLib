/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic

/-!
# EconCSLib.Examples.TicTacToe

Tic-Tac-Toe (3×3 m-n-k game) as an extensive-form game.

A concrete demonstration of the Arena framework on a complete
two-player board game with win detection.

## Attribution

Adapted from `GameTheory/Examples/Board games (m-n-k model).lean` in
[math-xmum/gametheory](https://github.com/math-xmum/gametheory).
-/

/-! ### Board types -/

abbrev Pos := Fin 3 × Fin 3

inductive Mark | X | O
  deriving DecidableEq, Repr

def Mark.other : Mark → Mark | .X => .O | .O => .X

/-- Board = assignment of marks to positions. -/
abbrev Board := Pos → Option Mark

def emptyBoard : Board := fun _ => none

/-- Place a mark at position `p` if empty. -/
def place (b : Board) (p : Pos) (m : Mark) : Board :=
  fun q => if q = p then some m else b q

/-- All positions on the 3×3 board. -/
def allPos : List Pos :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => (i, j)

/-- Is position `p` empty on board `b`? -/
def isEmpty (b : Board) (p : Pos) : Bool := (b p).isNone

/-- All empty positions. -/
def emptyPositions (b : Board) : List Pos := allPos.filter (isEmpty b)

/-! ### Win detection -/

/-- Winning lines: 3 rows + 3 columns + 2 diagonals = 8 lines. -/
def winLines : List (List Pos) :=
  -- Rows
  (List.finRange 3).map (fun i => (List.finRange 3).map (fun j => (i, j))) ++
  -- Columns
  (List.finRange 3).map (fun j => (List.finRange 3).map (fun i => (i, j))) ++
  -- Diagonals
  [[(⟨0,by omega⟩,⟨0,by omega⟩), (⟨1,by omega⟩,⟨1,by omega⟩), (⟨2,by omega⟩,⟨2,by omega⟩)],
   [(⟨0,by omega⟩,⟨2,by omega⟩), (⟨1,by omega⟩,⟨1,by omega⟩), (⟨2,by omega⟩,⟨0,by omega⟩)]]

/-- Does player `m` have 3 in a row? -/
def isWinner (b : Board) (m : Mark) : Bool :=
  winLines.any fun line => line.all fun p => b p == some m

/-! ### Game state -/

/-- State of the tic-tac-toe game. -/
structure TTTState where
  board : Board
  turn : Mark       -- whose turn it is

def TTTState.initial : TTTState := { board := emptyBoard, turn := .X }

def TTTState.isOver (s : TTTState) : Bool :=
  isWinner s.board .X || isWinner s.board .O || (emptyPositions s.board).isEmpty

/-- Apply a move: place current player's mark, switch turns. -/
def TTTState.move (s : TTTState) (p : Pos) : TTTState :=
  { board := place s.board p s.turn, turn := s.turn.other }

/-! ### As an ExtensiveGame -/

/-- Actions = board positions (at all states).
    At terminal states, actions are no-ops (state unchanged). -/
def tttGame : ExtensiveGame (Fin 2) ℤ where
  State := TTTState
  Action := fun _ => Pos
  next s p := if s.isOver then s else s.move p
  init := TTTState.initial
  mover s := if s.isOver then none
    else match s.turn with | .X => some 0 | .O => some 1
  payoff s i :=
    if isWinner s.board .X then (if i = 0 then 1 else -1)
    else if isWinner s.board .O then (if i = 0 then -1 else 1)
    else 0  -- draw

/-! ### A sample game: X wins on diagonal -/

open Mark in
def sampleGame : List Pos := [
  (⟨1,by omega⟩, ⟨1,by omega⟩),  -- X center
  (⟨1,by omega⟩, ⟨0,by omega⟩),  -- O
  (⟨0,by omega⟩, ⟨2,by omega⟩),  -- X
  (⟨2,by omega⟩, ⟨0,by omega⟩),  -- O
  (⟨0,by omega⟩, ⟨0,by omega⟩),  -- X
  (⟨0,by omega⟩, ⟨1,by omega⟩),  -- O
  (⟨2,by omega⟩, ⟨2,by omega⟩)   -- X wins (diagonal)
]

/-- Play a sequence of moves. -/
def playMoves (moves : List Pos) : TTTState :=
  moves.foldl (fun s p => s.move p) TTTState.initial

def finalState := playMoves sampleGame

-- X wins on the diagonal
example : isWinner finalState.board .X = true := by native_decide
example : isWinner finalState.board .O = false := by native_decide
example : finalState.isOver = true := by native_decide

-- Payoffs: X wins → (1, -1)
example : tttGame.payoff finalState 0 = 1 := by native_decide
example : tttGame.payoff finalState 1 = -1 := by native_decide
