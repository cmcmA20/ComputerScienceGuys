module Grammar

import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import FiniteMaps

%default total
%access public export

||| Alphabets of terms and variables should be finite for the classical theory
data MetaSymbol : Type -> Type -> Type where
  MSTerm : term -> MetaSymbol term var
  MSVar  : var  -> MetaSymbol term var

termInjective : MSTerm x = MSTerm y -> x = y
termInjective Refl = Refl

varInjective  : MSVar  x = MSVar  y -> x = y
varInjective Refl = Refl

Uninhabited (MSVar v = MSTerm t) where
  uninhabited Refl impossible

Uninhabited (MSTerm t = MSVar v) where
  uninhabited Refl impossible

(DecEq term, DecEq var) => DecEq (MetaSymbol term var) where
  decEq (MSTerm x) (MSTerm y) with (decEq x y)
    | Yes prf    = Yes $ cong {f=MSTerm} prf
    | No  contra = No $ contra . termInjective
  decEq (MSVar  x) (MSVar  y) with (decEq x y)
    | Yes prf    = Yes $ cong {f=MSVar} prf
    | No  contra = No $ contra . varInjective
  decEq (MSTerm x) (MSVar  y) = No absurd
  decEq (MSVar  x) (MSTerm y) = No absurd


||| Words are of finite length
data MetaWord : Type -> Type -> Type where
  MSWord : Vect n (MetaSymbol term var) -> MetaWord term var

wordInjective : (MSWord {n=m} x = MSWord {n=n} y) -> (m = n, x = y)
wordInjective Refl = (Refl, Refl)

Uninhabited (MSWord [] = MSWord (x :: xs)) where
  uninhabited Refl impossible

Uninhabited (MSWord (x :: xs) = MSWord []) where
  uninhabited Refl impossible

DecEq (MetaSymbol term var) => DecEq (MetaWord term var) where
  decEq (MSWord {n=Z  } []       ) (MSWord {n=Z  } []       ) = Yes Refl
  decEq (MSWord {n=Z  } []       ) (MSWord {n=S j} (y :: ys)) = No absurd
  decEq (MSWord {n=S i} (x :: xs)) (MSWord {n=Z  } []       ) = No absurd
  decEq (MSWord {n=S i} (x :: xs)) (MSWord {n=S j} (y :: ys)) with (decEq x y)
    | Yes p    with (assert_total (decEq (MSWord xs) (MSWord ys)))
      | Yes q      = let (_, w) = wordInjective q
                      in rewrite p
                      in rewrite w
                      in Yes $ Refl
      | No  contra = No $ \Refl => contra Refl
    | No  contra = No $ \Refl => contra Refl

||| Word specific Elem
data MWElem : MetaSymbol term var -> MetaWord term var -> Type where
  IsPresent : Elem ms xs -> MWElem ms (MSWord xs)

||| Contains at least one variable symbol
data ContainsVar : MetaWord term var -> Type where
  HasNT : (v : var ** Elem (MSVar v) xs) -> ContainsVar (MSWord xs)

||| Production rules can't contain terminal to terminal mapping
data ProdRules : Type -> Type -> Type where
  PRMap : (fmm : FiniteMultiMap (MetaWord term var) (MetaWord term var) ** All ContainsVar (snd (keysFMulti fmm))) ->
    ProdRules term var

record Grammar term var where
  constructor MkGrammar
  pr    : ProdRules term var
  start : var

-- examples
data TestVar  = S

DecEq TestVar where
  decEq S S = Yes Refl

data TestTerm = A | B

Uninhabited (A = B) where
  uninhabited Refl impossible

Uninhabited (B = A) where
  uninhabited Refl impossible

DecEq TestTerm where
  decEq A A = Yes Refl
  decEq B B = Yes Refl
  decEq A B = No absurd
  decEq B A = No absurd

-- S -> aSb
-- S -> ba
testPR : ProdRules TestTerm TestVar
testPR =
  PRMap $
    (  appendFMulti (MSWord [MSVar S]) (MSWord [MSTerm A, MSVar S, MSTerm B]) $
       appendFMulti (MSWord [MSVar S]) (MSWord [MSTerm B, MSTerm A])  $
       emptyFMulti
    ** ([HasNT (S ** Here), HasNT (S ** Here)]))

testGrammar : Grammar TestTerm TestVar
testGrammar = MkGrammar testPR S
