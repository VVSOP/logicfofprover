module Tableau where

import Codec.TPTP
import Data.Functor.Identity
import System.IO.Unsafe

removeComment :: [TPTP_Input] -> [TPTP_Input]
removeComment [] = []
removeComment [(Comment _)] = []
removeComment [(AFormula a b c d )] = [(AFormula a b c d )]
removeComment (x:xs) = (removeComment [x])++(removeComment xs)

getFormula ::[TPTP_Input] -> Formula
getFormula [(AFormula _ r f _)] 
	| str == "axiom" = f
	| str == "conjecture" = tableauxForm f
	| str == "theorem" = tableauxForm f
	| otherwise = error "error role!"
	where Role {unrole = str} = r
getFormula (x:xs) = (F (Identity (BinOp fof1 (:&:) fof2)))
	where fof1 = getFormula [x]
	      fof2 = getFormula xs
	

--getAtomicWord  (F (Identity (PredApp (AtomicWord x )[]))) = x

isFalse :: Formula -> Bool
isFalse (F (Identity (BinOp op1 op op2))) = False
isFalse (F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) = False
isFalse (F (Identity (PredApp (AtomicWord x )[])))
	|x=="$false" = True
	|otherwise = False
isFalse (F (Identity ((:~:) (F (Identity (PredApp (AtomicWord x )[]))))))
	|x=="$true" = True
	|otherwise = False

--whether a form is alpha formisalphaForm (F (Identity (BinOp op1 (:&:) op2))) = True
isAlphaForm :: Formula -> Bool
isAlphaForm (F (Identity (BinOp op1 op op2)))
  |op == (:&:) = True
  |op == (:~|:) = True
  |op == (:<=>:) = True
  |otherwise = False
isAlphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 op op2))))))
  |op == (:|:) = True
  |op ==  (:=>:) = True
  |op == (:<=:) = True
  |op == (:~&:) = True
  |op == (:<~>:) = True
  |otherwise = False
isAlphaForm (F (Identity (ac))) = False  

--whether a form is beta form
isBetaForm :: Formula -> Bool
isBetaForm (F (Identity (BinOp op1 op op2))) 
  |op == (:|:) = True
  |op == (:=>:) = True
  |op == (:<=:) = True
  |op == (:~&:) = True
  |op == (:<~>:) = True
  |otherwise = False
isBetaForm (F (Identity ((:~:) (F (Identity (BinOp op1 op op2))))))
  |op == (:&:) = True
  |op == (:~|:) = True
  |op == (:<=>:) = True
  |otherwise = False
isBetaForm (F (Identity (ac))) = False  

-- type of   "~~formula"
isDoubleNag :: Formula -> Bool
isDoubleNag (F (Identity ((:~:) ( F (Identity ((:~:) formula)))))) = True
isDoubleNag (F (Identity (BinOp op1 op op2))) = False
isDoubleNag  ( F (Identity ((:~:) formula))) = False
--doubleNag :: [Formula]->[Formula]
doubleNag (F (Identity ((:~:) ( F (Identity ((:~:) formula)))))) = formula
doubleNag (F (Identity ((:~:) formula))) = ( F (Identity ((:~:) formula)))
doubleNag (F (Identity (BinOp op1 op op2))) = (F (Identity (BinOp op1 op op2)))
doubleNag (F (Identity (PredApp aw t))) = (F (Identity (PredApp aw t)))
--doubleNag [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ] = [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ]

isAtomicWord :: AtomicWord->Bool
isAtomicWord _ = True

--alpha form
alphaForm :: Formula -> [Formula]
alphaForm (F (Identity (BinOp op1 (:&:) op2))) = [doubleNag(op1), doubleNag(op2)]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2)))))) = [doubleNag(F (Identity ((:~:) op1))),doubleNag(F (Identity ((:~:) op2)))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2)))))) = [doubleNag(op1), doubleNag(F (Identity ((:~:) op2)))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))) = [doubleNag(F (Identity ((:~:) op1))), doubleNag(op2)]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~&:) op2)))))) = [doubleNag(op1), doubleNag(op2)]
alphaForm (F (Identity (BinOp op1 (:~|:) op2))) = [doubleNag(F (Identity ((:~:) op1))),doubleNag(F (Identity ((:~:) op2)))]
alphaForm (F (Identity (BinOp op1 (:<=>:) op2))) = [doubleNag((F (Identity (BinOp op1 (:=>:) op2))) ), doubleNag((F (Identity (BinOp op1 (:<=:) op2))) )]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<~>:) op2)))))) = [doubleNag((F (Identity (BinOp op1 (:=>:) op2)))), doubleNag((F (Identity (BinOp op1 (:<=:) op2))))]


--beta form
betaForm :: Formula -> [Formula]
betaForm (F (Identity (BinOp op1 (:|:) op2))) = [doubleNag(op1), doubleNag(op2)]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) = [doubleNag(F (Identity ((:~:) op1))),doubleNag(F (Identity ((:~:) op2)))]
betaForm (F (Identity (BinOp op1 (:=>:) op2))) = [doubleNag(F (Identity ((:~:) op1))), doubleNag(op2)]
betaForm (F (Identity (BinOp op1 (:<=:) op2))) = [doubleNag(op1),doubleNag(F (Identity ((:~:) op2)))]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) = [doubleNag(op1), doubleNag(op2)]
betaForm (F (Identity (BinOp op1 (:~&:) op2))) = [doubleNag(F (Identity ((:~:) op1))),doubleNag(F (Identity ((:~:) op2)))]
betaForm (F (Identity (BinOp op1 (:<~>:) op2))) = [doubleNag((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2))))))), doubleNag((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))))]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<=>:) op2)))))) = [doubleNag((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2))))))), doubleNag((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))))]


--delete element form list
--deleteFromList :: a->[a]->[a]
deleteFromList _ [] = []
deleteFromList x (y:ys) 
	    | x== y = deleteFromList x ys
	    | otherwise = y : deleteFromList x ys

--add element to list
addToList1 y x = y ++ [x]
addToList2 y x z = y ++ [x] ++ [z]

isLiter :: [Formula] -> Bool
isLiter [] = True
isLiter (x:xs) | not(isAlphaForm x) && not(isBetaForm x) && isLiter xs = True
	       | otherwise = False

tableauxForm :: Formula -> Formula
tableauxForm formula = doubleNag(F (Identity ((:~:) formula)))


--tran a formula to clause form 
tran f | isLiter f = [f]

tran (x:xs) 
	    | isAlphaForm x = t1++t2 
	    | isBetaForm x = t3
	    | otherwise = t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  tran (s ++ [aop1])
		      t2 =  tran (s ++ [aop2])
		      t3 = tran (s++[bop1]++[bop2])
		      t4 = tran (xs++[x])

tranD f | isLiter f = [f]

tranD (x:xs) 
	    | isBetaForm x = t1++t2 
	    | isAlphaForm x = t3
	    | otherwise = t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  tranD (s ++ [bop1])
		      t2 =  tranD (s ++ [bop2])
		      t3 = tranD (s++[aop1]++[aop2])
		      t4 = tranD (xs++[x])

tranD2 [] = []
tranD2 f | isLiter f = [f]
tranD2 (x:xs) 
	    | isBetaForm x = tableau (t1++t2) 
	    | isAlphaForm x = tableau t3
	    | otherwise = tableau t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  tranD2 (s ++ [bop1])
		      t2 =  tranD2 (s ++ [bop2])
		      t3 = tranD2 (s++[aop1]++[aop2])
		      t4 = tranD2 (xs++[x])

isClosed ::[Formula]->[Formula]->Bool
isClosed [] _ = False
isClosed (x:xs) list = ((elem x list) && (elem ( F (Identity ((:~:) x)))) list) || isClosed xs list
isClosed2 ::[Formula]->Bool
isClosed2 [] = False
isClosed2 (x:xs) = (isFalse x) || (isClosed2 xs)
	

--closeTableaux :: [[Formula]]->[Formula]->[Formula]-> Bool
closeTableaux [] = True
closeTableaux [x] = isClosed x x || isClosed2 x
closeTableaux  (x:xs) = ((isClosed x x)||(isClosed2 x)) && (closeTableaux xs)

--closeTableaux2 [[]] = True
--closeTableaux2 [x]
--	| x == [] = True
--	| otherwise = False
--closeTableaux2 (x:xs) = (closeTableaux2 [x]) && (closeTableaux2 xs)

--tableau :: [[Formula]]->[Formula]
tableau x 
	| closeTableaux x = []
	| otherwise = x

isTheoremStr str = closeTableaux z
  where x = parse str
	r = removeComment x
	y = getFormula r
	z = tranD [y]

isTheoremFile file = closeTableaux z
  where x = parseFile file
	xx = unsafePerformIO x
	r = removeComment xx
	y = getFormula r
	z = tranD [y]

isTheoremFile2 file = (closeTableaux z)
  where x = parseFile file
	xx = unsafePerformIO x
	r = removeComment xx
	y = getFormula r
	z = tranD2 [y]
