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
  show (VarF name       ) = name
  show (Lam  body       ) = "λ." ++ show body
  show (App  x (App y z)) = show x ++ " (" ++ show (App y z) ++ ")"
  show (App  x y        ) = show x ++ " " ++ show y
  show (VarB idx        ) {ctx} = showFin {k = ctx} 0 idx
    where
      showFin : Nat -> Fin k -> String
      showFin n FZ     = show n
      showFin n (FS x) = showFin (S n) x

-- ||| Replaces all occurences of the outer variable in a term with another term
-- ||| @ rep replacement term
-- ||| @ tgt where to replace
substOut : (rep : UT ctx) -> (tgt : UT (S ctx)) -> UT ctx
substOut rep (VarF name) = VarF name
substOut rep (VarB idx ) {ctx} =
  case decEq (last {n=ctx}) idx of
       Yes _      => rep
       No  contra => case strengthen' idx of
                          Left  l => void $ contra $ sym l
                          Right r => VarB r
  where
    strengthen' : (i : Fin (S n)) -> Either (i = last {n}) (Fin n)
    strengthen' {n = Z  } FZ     = Left Refl
    strengthen' {n = S k} FZ     = Right FZ
    strengthen' {n = S k} (FS x) = case strengthen' {n = k} x of
                                        Left  prf => rewrite prf in Left Refl
                                        Right si  => Right $ FS si
substOut rep (Lam  body) = Lam $ substOut (weakenCtx rep) body
  where
    weakenCtx : UT ctx -> UT (S ctx)
    weakenCtx (VarF name) = VarF name
    weakenCtx (VarB idx ) = VarB $ weaken idx
    weakenCtx (Lam  body) = Lam $ weakenCtx body
    weakenCtx (App  x y ) = App (weakenCtx x) (weakenCtx y)
substOut rep (App  x y ) = App (substOut rep x) (substOut rep y)

||| Beta-reduction step
beta : UT ctx -> UT ctx
beta (VarF name        ) = VarF name
beta (VarB idx         ) = VarB idx
beta (Lam  body        ) = Lam (beta body)
-- Non-trivial interaction, eliminator acts on constructor
beta (App  (Lam body) y) = substOut y body
beta (App  x          y) = App (beta x) (beta y)

-- ||| Eta-reduction step
-- eta : UT ctx -> UT ctx
-- eta (VarF name             ) = VarF name
-- eta (VarB idx              ) = VarB idx
-- -- Non-trivial interaction, constructor acts on eliminator
-- eta (Lam  (App x (VarB FZ))) = ?joji
-- eta (Lam  body             ) = Lam (eta body)
-- eta (App  x y              ) = App (eta x) (eta y)

