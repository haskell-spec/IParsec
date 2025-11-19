import Veriflex.Located
open Veriflex

inductive IndentationRel : Type where
  | Eq : IndentationRel
  | Gt : IndentationRel
  | Ge : IndentationRel
  | Any : IndentationRel

def ParseError : Type := String

abbrev Indentation : Type := Nat

def maxInd : Indentation := 1000

structure IndentationState : Type where
  min : Indentation
  max : Indentation
  absMode : Bool
  rel : IndentationRel

def initialIndentationState : IndentationState :=
  { min := 0, max := maxInd, absMode := False, rel := IndentationRel.Any}

structure State(tok : Type) : Type  where
  input : List (Located tok)
  indent : IndentationState

inductive Consumed (α : Type) : Type where
  | Consumed : α → Consumed α
  | Empty : α → Consumed α

inductive Reply (tok α : Type) : Type where
  | Ok : α → State tok → Reply tok α
  | Error : ParseError → Reply tok α

structure Parsec (tok α : Type) : Type where
  run : (State tok → Consumed (Reply tok α))

/--
Modify the state the parser is run in.
-/
def modifyState {tok α : Type}(f : State tok → State tok)(p : Parsec tok α) : Parsec tok α :=
  Parsec.mk (λ s => p.run (f s))

def parsec_bind {tok α β : Type} :
   Parsec tok α →
   (α -> Parsec tok β) →
   Parsec tok β :=
   open Reply in
   λ ma f => Parsec.mk (λ s =>
     match ma.run s with
     | Consumed.Consumed (Ok a s') => (f a).run s'
     | Consumed.Consumed (Error err) => (Consumed.Consumed (Error err))
     | Consumed.Empty (Ok a s') => (f a).run s'
     | Consumed.Empty (Error err) => Consumed.Empty (Error err)
     )

instance parsecMonad {tok : Type} : Monad (Parsec tok) where
  pure := λ x => Parsec.mk (λ s => Consumed.Empty (Reply.Ok x s))
  bind := parsec_bind



def parse{α : Type} (input : String) (parser : Parsec Char α) : Option α :=
  let initialState : State Char := { input := input.toList.map (λ x => ⟨0,x⟩), indent := initialIndentationState }
  match parser.run initialState with
  | Consumed.Consumed (Reply.Ok res _) => some res
  | Consumed.Empty (Reply.Ok res _) => some res
  | _ => none
