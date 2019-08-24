module Grammar

import Data.Vect
import Control.Isomorphism

import Language

%default total
%access public export

||| Alphabet of terms must be finite
||| Alphabet of variables must be finite

data MetaSymbol : (term : Type) -> (var : Type) -> Type where
  MSTerm : term -> MetaSymbol term var
  MSVar  : var  -> MetaSymbol term var

(Eq term, Eq var) => Eq (MetaSymbol term var) where
  (==) (MSTerm _) (MSVar _) = False
  (==) (MSVar _) (MSTerm _) = False
  (==) (MSVar u) (MSVar v) = u == v
  (==) (MSTerm s) (MSTerm t) = s == t

%name MetaSymbol ms, ms1, ms2

-- record MetaWord where
--   constructor MkMetaWord
--   term    : Type
--   var     : Type
--   letters : List (MetaSymbol term var)

||| Words are finite sequences
MetaWord : Type -> Type -> Type
MetaWord term var = List (MetaSymbol term var)

%name MetaWord mw, mw1, mw2

MkMetaWord : List (MetaSymbol term var) -> MetaWord term var
MkMetaWord xs = xs

containsVariables : (mw : MetaWord term var) -> Bool
containsVariables mw = foldr orIsAVariable False mw
  where
    orIsAVariable : MetaSymbol term var -> Bool -> Bool
    orIsAVariable (MSTerm t) b = b
    orIsAVariable (MSVar  v) b = True

||| There should be at least one variable on the left side of the rule
data Rule : (term : Type) -> (var : Type) -> Type where
   MkRule : (mw : MetaWord term var ** containsVariables mw = True) -> MetaWord term var -> Rule term var

substitute : (Eq term, Eq var) => (r : Rule term var) -> (mw : MetaWord term var) -> MetaWord term var
substitute _ []           = []
substitute r mw@(x :: xs) = case r of (MkRule (before ** _) after) => if before `isPrefixOf` mw
                                                                         then let rest = drop (length before) mw
                                                                               in after ++ rest
                                                                         else x :: (substitute r xs)

record Grammar term var where
  constructor MkGrammar
  startSymbol : var
  productions : List (Rule term var)

produceStepWord : (Eq term, Eq var) => (g : Grammar term var) -> (mw : MetaWord term var) -> List (MetaWord term var)
produceStepWord g mw = map (\r => substitute r mw) (productions g)

produceStepManyWords : (Eq term, Eq var) => (g : Grammar term var) -> (mws : List (MetaWord term var)) -> List (MetaWord term var)
produceStepManyWords g mws = concatMap (produceStepWord g) mws

data TerminalSymbol : MetaSymbol term var -> Type where
  ReallyTerminal : term -> TerminalSymbol (MSTerm term)

isTerminalSymbol : MetaSymbol term var -> Bool
isTerminalSymbol (MSTerm _) = True
isTerminalSymbol (MSVar  _) = False

castTerminalSymbol : (ms : MetaSymbol term var ** isTerminalSymbol ms = True) -> TerminalSymbol ms
castTerminalSymbol ((MSTerm t) ** pf) = ReallyTerminal ?dsfrhs1
castTerminalSymbol ((MSVar  v) ** pf) = ?castTerminalSymbol_rhs_3

-- isTerminalWord : (mw : MetaWord term var) -> List (ms : MetaSymbol term var ** isTerminalSymbol ms = True)
-- isTerminalWord []        = []
-- isTerminalWord (x :: xs) = case x of
--                                 MSTerm t => (x ** isTerminalSymbol x = True) :: isTerminalWord xs
--                                 MSVar  v => ?rhs2

-- castTerminalWord : (mw : MetaWord term var ** isTerminalWord mw = True) -> LWord term
-- castTerminalWord (mw ** pf) = let q = 1
--                                in MkLWord ?xx

--generatorStep : (Eq term, Eq var) => (g : Grammar term var) -> (to : List (MetaWord term var), nt : List (MetaWord term var)) -> ()
-- (NOT onlyTerminal) |produce-> (step 2, NOT onlyTerminal) |output-> (onlyTerminal)
--         ^                               |
--         +-------------------------------+
--discardTerminals : List (MetaWord term var) -> List (MetaWord term var), List (MetaWord term var)
--discardTerminals = let q = produceStepManyWords xs
--                       ts = filter isTerminalOnly q
--                       ns = q \\ ts
--                    in (ts, ns)

--auti : (x : Var) -> STrans m () [x ::: State (List (MetaWord term var))]
--                               (const [x ::: State (List (MetaWord term var))])

-- TESTS

data TTerm = Zero | One | Two
Eq TTerm where
  Zero == Zero = True
  One == One = True
  Two == Two = True
  _ == _ = False

data TVar  = S | A
Eq TVar where
  S == S = True
  A == A = True
  _ == _ = False


testGrammar : Grammar TTerm TVar
testGrammar = MkGrammar S [rule1, rule2, rule3, rule4, rule5]
  where
    rule1 = let before = MkMetaWord [MSVar S]
                after  = MkMetaWord [MSTerm Zero, MSVar S, MSVar A, MSTerm Two]
             in MkRule (before ** Refl) after
    rule2 = let before = MkMetaWord [MSVar S]
                after  = MkMetaWord []
             in MkRule (before ** Refl) after
    rule3 = let before = MkMetaWord [MSTerm Two, MSVar A]
                after  = MkMetaWord [MSVar A, MSTerm Two]
             in MkRule (before ** Refl) after
    rule4 = let before = MkMetaWord [MSTerm Zero, MSVar A]
                after  = MkMetaWord [MSTerm Zero, MSTerm One]
             in MkRule (before ** Refl) after
    rule5 = let before = MkMetaWord [MSTerm One, MSVar A]
                after  = MkMetaWord [MSTerm One, MSTerm One]
             in MkRule (before ** Refl) after
