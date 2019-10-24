module FiniteMaps

import Data.Vect
import Decidable.Equality

%default total
%access public export

beqKey : DecEq key => (x, y : key) -> Bool
beqKey x y with (decEq x y)
  | (Yes _) = True
  | (No  _) = False

beqKeyOnly : DecEq key => (x, y : (key, value)) -> Bool
beqKeyOnly (k1, _) (k2, _) = beqKey k1 k2


data FiniteMap : Type -> Type -> Type where
  FMDict : Vect n (key, value) -> FiniteMap key value

emptyFMap : DecEq key => FiniteMap key value
emptyFMap = FMDict Nil

lookupFMap : DecEq key => key -> FiniteMap key value -> Maybe value
lookupFMap t (FMDict xs) = lookupBy beqKey t xs

updateFMap : DecEq key => key -> value -> FiniteMap key value -> FiniteMap key value
updateFMap k v (FMDict xs) = case elemIndexBy beqKeyOnly (k, v) xs of
                                 Nothing => FMDict $ (k, v) :: xs
                                 Just i  => FMDict $ replaceAt i (k, v) xs

keysFMap : FiniteMap key value -> (n ** Vect n key)
keysFMap (FMDict {n} xs) = let (k, _) = unzip xs in (n ** k)

data FiniteMultiMap : Type -> Type -> Type where
  FMultiDict : Vect n (key, value) -> FiniteMultiMap key value

emptyFMulti : DecEq key => FiniteMultiMap key value
emptyFMulti = FMultiDict Nil

lookupFMulti : DecEq key => key -> FiniteMultiMap key value -> (n ** Vect n value)
lookupFMulti t (FMultiDict xs) = Data.Vect.mapMaybe (target t) xs
  where
    target : key -> (key, value) -> Maybe value
    target t (k, v) = if beqKey t k
                         then Just v
                         else Nothing

appendFMulti : DecEq key => key -> value -> FiniteMultiMap key value -> FiniteMultiMap key value
appendFMulti k v (FMultiDict xs) = FMultiDict $ (k, v) :: xs

keysFMulti : FiniteMultiMap key value -> (n ** Vect n key)
keysFMulti (FMultiDict {n} xs) = let (k, _) = unzip xs in (n ** k)

