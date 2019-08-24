module Language

import Data.List.Quantifiers
import Data.Vect
import Control.Isomorphism

%default total
%access public export

-- data ChomskyTag = Regular | ContextFree | ContextSensitive | RE

||| Alphabet is finite


||| Language word is a finite Vector of alphabet symbols
record LWord a where
  constructor MkLWord
  wsymbols : (n ** Vect n a)

LWord_to_Vect_n_and_back : (lw : LWord a) -> MkLWord (wsymbols lw) = lw
LWord_to_Vect_n_and_back (MkLWord wsymbols) = Refl

Vect_n_to_LWord_and_back : (p : (n ** Vect n a)) -> wsymbols (MkLWord p) = p
Vect_n_to_LWord_and_back p = Refl

||| LWord is trivially a vector
LWord_is_Vect_n : Iso (LWord a) (n ** Vect n a)
LWord_is_Vect_n = MkIso wsymbols MkLWord Vect_n_to_LWord_and_back LWord_to_Vect_n_and_back


||| Formal language is a possibly infinite List of words over an alphabet
||| Blunt and nasty definition
codata Lang : (a : Type) -> Type where
  EmptyFL : Lang a
  PrependWord : LWord a -> Lang a -> Lang a

%name Lang lang, lang1, lang2

-- data LangSlice : (n : Nat) -> (a : Type) -> Type where
--   Nil : LangSlice n a
-- --  NextSlice : ProdRule a -> LangSlice n a -> LangSlice (S n) a

-- ||| Formal language is an inductive family of finite Lists of fixed length words over an alphabet
-- ||| LOL it's grammars all the way down
-- data LangI : (a : Type) -> Type where
--   Slice : ((n : Nat) -> List (Vect n a)) -> LangI a
