import Veriflex.Located
open Veriflex

inductive IndentationRel : Type where
  | Eq : IndentationRel
  | Gt : IndentationRel
  | Ge : IndentationRel
  | Any : IndentationRel

def ParseError : Type := String

abbrev Indentation : Type := Nat

inductive IndentationSet where
  | Any : IndentationSet
  | Exact : Indentation → IndentationSet
  | Min : Indentation → IndentationSet

def isValidIndent (s : IndentationSet) (i : Indentation) : Bool :=
  match s with
  | IndentationSet.Any => true
  | IndentationSet.Exact e => i = e
  | IndentationSet.Min e => e ≤ i

structure IndentationState : Type where
  set : IndentationSet
  absMode : Bool
  rel : Option IndentationRel

def initialIndentationState : IndentationState :=
  { set := IndentationSet.Any, absMode := False, rel := none}

structure State(tok : Type) : Type  where
  input : List (Located tok)
  indent : IndentationState

/--
Indicates whether the parser has consumed input while producing its result.
`Empty` means that no input has been consumed.
-/
inductive Consumed (α : Type) : Type where
  | Consumed : α → Consumed α
  | Empty : α → Consumed α

/--
Possible Outputs of the parser.
-/
inductive Reply (tok α : Type) : Type where
  | Ok : α → State tok → Reply tok α
  | Error : ParseError → Reply tok α

/--
A parser takes a parser state and produces a result.
-/
structure Parsec (tok α : Type) : Type where
  run : State tok → Consumed (Reply tok α)

/--
Modify the state the parser is run in.
-/
def modifyState {tok α : Type}
                (f : State tok → State tok)
                (p : Parsec tok α)
                : Parsec tok α :=
  Parsec.mk (λ s => p.run (f s))

def putState : State tok → Parsec tok Unit :=
  λ s => Parsec.mk (λ _ => Consumed.Empty (Reply.Ok Unit.unit s))

/--
Get the state the parser is run in.
-/
def getState {tok : Type} : Parsec tok (State tok) :=
  Parsec.mk (λ s => Consumed.Empty (Reply.Ok s s))

/--
The unit of the `Parsec` monad.
-/
def parsec_pure {tok α : Type}(x : α) : Parsec tok α :=
  Parsec.mk (λ s => Consumed.Empty (Reply.Ok x s))

/--
The bind operations of the `Parsec` monad.
-/
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
  pure := parsec_pure
  bind := parsec_bind


def parse {tok α : Type}
          (input : List (Located tok))
          (parser : Parsec tok α)
          : Option α :=
  let initialState : State tok := { input := input, indent := initialIndentationState }
  match parser.run initialState with
  | Consumed.Consumed (Reply.Ok res _) => some res
  | Consumed.Empty (Reply.Ok res _) => some res
  | _ => none
