module UnTyped

import Data.Fin

%default total
%access public export

||| It's almost magic that in UTLC we need only a single Nat of state
Context : Type
Context = Nat

||| [U]n[T]yped lambda calculus
data UT : Context -> Type where
  VarF  : (name : String    ) -> UT ctx
  VarB  : (idx  : Fin ctx   ) -> UT ctx
  Lam   : (body : UT (S ctx)) -> UT ctx
  App   : (x, y : UT ctx    ) -> UT ctx

Show (UT ctx) where
  show (VarF name        ) = name
  show (Lam  body        ) = "λ." ++ show body
  show (App  (Lam body) y) = "(λ." ++ show body ++ ") " ++ show y
  show (App  x (App y z) ) = show x ++ " (" ++ show (App y z) ++ ")"
  show (App  x y         ) = show x ++ " " ++ show y
  show (VarB idx         ) {ctx} = showFin {k = ctx} 0 idx
    where
      showFin : Nat -> Fin k -> String
      showFin n FZ     = show n
      showFin n (FS x) = showFin (S n) x

data Val : UT ctx -> Type where
  MkVal : (v : UT 0) -> Val v

||| If the de Bruijn index points to the outer lambda, it returns a Left proof of it
||| Else it strengthens the index
decOut : (i : Fin (S n)) -> Either (i = last {n}) (Fin n)
decOut {n = Z  } FZ     = Left Refl
decOut {n = S k} FZ     = Right FZ
decOut {n = S k} (FS x) = case decOut {n = k} x of
                               Left  prf => rewrite prf in Left Refl
                               Right si  => Right $ FS si

||| The context can be weakened arbitrarily
weakenCtx : UT ctx -> UT (S ctx)
weakenCtx (VarF name) = VarF name
weakenCtx (VarB idx ) = VarB $ weaken idx
weakenCtx (Lam  body) = Lam $ weakenCtx body
weakenCtx (App  x y ) = App (weakenCtx x) (weakenCtx y)

-- ||| Replaces all occurences of the outer variable in a term with another term
-- ||| @ rep replacement term
-- ||| @ tgt where to replace
substOut : (rep : UT ctx) -> (tgt : UT (S ctx)) -> UT ctx
substOut rep (VarF name) = VarF name
substOut rep (VarB idx ) {ctx} =
  case decOut idx of
    Left  l => rep
    Right r => VarB r
--   case decEq (last {n=ctx}) idx of
--        Yes _      => rep
--        No  contra => case decOut idx of
--                           Left  l => void $ contra $ sym l
--                           Right r => VarB r
substOut rep (Lam  body) = Lam $ substOut (weakenCtx rep) body
substOut rep (App  x y ) = App (substOut rep x) (substOut rep y)

||| Beta-reduction step
beta : UT ctx -> UT ctx
beta (VarF name        ) = VarF name
beta (VarB idx         ) = VarB idx
beta (Lam  body        ) = Lam (beta body)
-- Non-trivial interaction, eliminator acts on constructor
beta (App  (Lam body) y) = substOut y body
beta (App  x          y) = App (beta x) (beta y)

||| If the term doesn't mention the outer lambda, the context can be strengthened
strengthenCtx : UT (S ctx) -> Either (UT (S ctx)) (UT ctx)
strengthenCtx (VarF name) = Right $ VarF name
strengthenCtx (VarB idx ) {ctx} = case decOut idx of
                                       Left  _  => Left  $ VarB idx
                                       Right si => Right $ VarB si
strengthenCtx (Lam  body) = case strengthenCtx body of
                                 Left  _  => Left  $ Lam body
                                 Right sb => Right $ Lam sb
strengthenCtx (App  x y ) = case strengthenCtx x of
                                 Left  _  => Left $ App x y
                                 Right sx => case strengthenCtx y of
                                                  Left  _  => Left  $ App x y
                                                  Right sy => Right $ App sx sy

||| Eta-reduction step
etaReduce : UT ctx -> UT ctx
etaReduce (VarF name             ) = VarF name
etaReduce (VarB idx              ) = VarB idx
-- Non-trivial interaction, constructor acts on eliminator
etaReduce (Lam  (App x (VarB FZ))) = case strengthenCtx x of
                                          Left  _  => Lam $ App x (VarB FZ)
                                          Right sx => sx
etaReduce (Lam  body             ) = Lam (etaReduce body)
etaReduce (App  x y              ) = App (etaReduce x) (etaReduce y)

-- ||| Eta-expansion step
etaExpand : UT ctx -> UT ctx
etaExpand x = Lam $ App (weakenCtx x) (VarB FZ)

callByValue : UT ctx -> (v : UT ctx, Val v)
callByValue x = ?wqe
