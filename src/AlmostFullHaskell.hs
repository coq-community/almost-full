module AlmostFullHaskell where 

data WFT x = ZT | SUP (x -> WFT x) 

data Acc x = Acc_Intro (x -> Acc x) 
           | BadAcc -- For refutation  purposes

-- There are two implicit arguments going on here: 
-- In reality it is: 
-- Acc x (R : x -> x -> Prop) (z:x) = Acc_intro (fun y, y R x -> Acc x R y)

afLeLeft, afLeRight :: (Int,Int) -> WFT (Int,Int)
afLeLeft (x,y)  = SUP (\(x',y') -> if x' < x && x' >= 0 then afLeLeft  (x',y') else ZT)
afLeRight (x,y) = SUP (\(x',y') -> if y' < y && x' >= 0 then afLeRight (x',y') else ZT)

afLe :: Int -> WFT Int
afLe x  = if x == 0 then ZT 
          else SUP (\x' -> if x' < x && x' >= 0 then afLe x' else ZT)


oplus_nullary ZT q = q 
oplus_nullary (SUP f) q = SUP (\x -> oplus_nullary (f x) q) 

-- /OplusUnary/
oplus_unary q ZT = q 
oplus_unary ZT q = q 
oplus_unary p@(SUP f) q@(SUP g) 
  = SUP (\x -> oplus_nullary (oplus_unary (f x) q) 
                             (oplus_unary p (g x)))
-- /End/

-- /OplusBinary/
oplus_binary q ZT = q 
oplus_binary ZT q = q 
oplus_binary p@(SUP f) q@(SUP g) 
  = SUP (\x -> oplus_unary (oplus_binary (f x) q) 
                           (oplus_binary p (g x)))
-- /End/

-- AF -> WF using transitivity assumption 
af2wf ZT      y = Acc_Intro (\x -> BadAcc)
af2wf (SUP f) y = Acc_Intro (\z -> af2wf (f y) z) 
  -- Not x! x is only used in the Prop part of this here!

accPredicateForPair = af2wf (oplus_binary (SUP afLeLeft) (SUP afLeRight))

data TestResult = OK | NOTOK1 | NOTOK2
  deriving Show


tester :: (Int -> Acc Int) -> [Int] -> TestResult
tester accPred [] = OK
tester accPred [x] = OK
tester accPred (x:y:rest) = 
   case (accPred x, accPred y) of 
     (BadAcc,_) -> NOTOK1
     (_,BadAcc) -> NOTOK2
     (Acc_Intro f, _) -> tester f (y:rest) 







