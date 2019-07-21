module Automaton where

type IWord i = [i]

data Automaton s i o = Automaton { inputA :: i -> Bool
                                 , startS :: s
                                 , finalS :: s -> o
                                 , transi :: (s, i) -> s
                                 }

step :: Automaton s i o -> i -> Automaton s i o
step aut x = Automaton { inputA = inputA aut
                       , startS = (transi aut) (startS aut, x)
                       , finalS = finalS aut
                       , transi = transi aut
                       }

process :: Automaton s i o -> IWord i -> o
process aut []     = (finalS aut) (startS aut)
process aut (x:xs) = let newAut = step aut x
                      in process newAut xs

type Recognizer s i = Automaton s i Bool

test1 :: Recognizer Integer Char
test1 = Automaton { inputA = inA
                  , startS = 0
                  , finalS = fS
                  , transi = tr
                  } where
                      inA x = if x == '0' || x == '1' then True else False
                      fS st = if st == 1 then True else False
                      tr (0, '0') = 0
                      tr (0, '1') = 1
                      tr (1, _)   = 1

test2 :: Recognizer Integer Char
test2 = Automaton {
                  inputA = inA,
                  startS = 0,
                  finalS = fS,
                  transi = tr
                  } where
                    inA x  = if x == '0' || x == '1' then True else False
                    fS st  = if st == 8 then True else False
                    tr (0, '0') = 1
                    tr (0, '1') = 1
                    tr (1, '0') = 2
                    tr (1, '1') = 2
                    tr (2, '0') = 3
                    tr (2, '1') = 3
                    tr (3, '0') = 4
                    tr (3, '1') = 4
                    tr (4, '0') = 5
                    tr (4, '1') = 5
                    tr (5, '0') = 6
                    tr (5, '1') = 6
                    tr (6, '0') = 7
                    tr (6, '1') = 7
                    tr (7, '0') = 8
                    tr (7, '1') = 8
                    tr (8, _)   = 9
                    tr (9, _)   = 9
