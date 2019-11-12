module Language

import Data.List.Quantifiers
import Data.Vect
import Control.Isomorphism

%default total
%access public export

-- TODO finish this

-- data ChomskyTag = Regular | ContextFree | ContextSensitive | RE

||| Word is a vector of alphabet symbols
data LWord : Type -> Type where
  MkLWord : Vect n term -> LWord term

||| Shorter or of equal length
data ShEq : LWord term -> LWord term -> Type where
  MkShEq : (a : Vect m term) -> (b : Vect n term) -> (m `LTE` n) -> ShEq (MkLWord a) (MkLWord b)

data AscWordList : Type -> Type where
  Nil    : AscWordList (LWord term)
  Single : LWord term -> AscWordList (LWord term)
  -- Append : (w1, w2 : LWord term) -> (wl : AscWordList (LWord term)) ->
  --   AscWordList (LWord term)

||| Formal language is a possibly infinite List of words over an alphabet
||| Length of words is increasing
codata Lang : (a : Type) -> Type where
  MkLang : AscWordList term -> Lang term

%name Lang lang, lang1, lang2

-- data LangSlice : (n : Nat) -> (a : Type) -> Type where
--   Nil : LangSlice n a
-- --  NextSlice : ProdRule a -> LangSlice n a -> LangSlice (S n) a

-- ||| Formal language is an inductive family of finite Lists of fixed length words over an alphabet
-- ||| LOL it's grammars all the way down
-- data LangI : (a : Type) -> Type where
--   Slice : ((n : Nat) -> List (Vect n a)) -> LangI a

