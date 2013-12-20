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


--doubleNagHandle :: [Formula]->[Formula]
doubleNagHandle (F (Identity ((:~:) ( F (Identity ((:~:) formula)))))) = formula
doubleNagHandle (F (Identity ((:~:) formula))) = ( F (Identity ((:~:) formula)))
doubleNagHandle (F (Identity (BinOp op1 op op2))) = (F (Identity (BinOp op1 op op2)))
doubleNagHandle (F (Identity (PredApp aw t))) = (F (Identity (PredApp aw t)))
--doubleNagHandle [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ] = [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ]


--alpha form
alphaForm :: Formula -> [Formula]
alphaForm (F (Identity (BinOp op1 (:&:) op2))) = [doubleNagHandle(op1), doubleNagHandle(op2)]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2)))))) = [doubleNagHandle(F (Identity ((:~:) op1))),doubleNagHandle(F (Identity ((:~:) op2)))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2)))))) = [doubleNagHandle(op1), doubleNagHandle(F (Identity ((:~:) op2)))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))) = [doubleNagHandle(F (Identity ((:~:) op1))), doubleNagHandle(op2)]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~&:) op2)))))) = [doubleNagHandle(op1), doubleNagHandle(op2)]
alphaForm (F (Identity (BinOp op1 (:~|:) op2))) = [doubleNagHandle(F (Identity ((:~:) op1))),doubleNagHandle(F (Identity ((:~:) op2)))]
alphaForm (F (Identity (BinOp op1 (:<=>:) op2))) = [doubleNagHandle((F (Identity (BinOp op1 (:=>:) op2))) ), doubleNagHandle((F (Identity (BinOp op1 (:<=:) op2))) )]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<~>:) op2)))))) = [doubleNagHandle((F (Identity (BinOp op1 (:=>:) op2)))), doubleNagHandle((F (Identity (BinOp op1 (:<=:) op2))))]


--beta form
betaForm :: Formula -> [Formula]
betaForm (F (Identity (BinOp op1 (:|:) op2))) = [doubleNagHandle(op1), doubleNagHandle(op2)]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) = [doubleNagHandle(F (Identity ((:~:) op1))),doubleNagHandle(F (Identity ((:~:) op2)))]
betaForm (F (Identity (BinOp op1 (:=>:) op2))) = [doubleNagHandle(F (Identity ((:~:) op1))), doubleNagHandle(op2)]
betaForm (F (Identity (BinOp op1 (:<=:) op2))) = [doubleNagHandle(op1),doubleNagHandle(F (Identity ((:~:) op2)))]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) = [doubleNagHandle(op1), doubleNagHandle(op2)]
betaForm (F (Identity (BinOp op1 (:~&:) op2))) = [doubleNagHandle(F (Identity ((:~:) op1))),doubleNagHandle(F (Identity ((:~:) op2)))]
betaForm (F (Identity (BinOp op1 (:<~>:) op2))) = [doubleNagHandle((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2))))))), doubleNagHandle((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))))]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<=>:) op2)))))) = [doubleNagHandle((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2))))))), doubleNagHandle((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))))]


--delete element form list
--deleteFromList :: a->[a]->[a]
deleteFromList _ [] = []
deleteFromList x (y:ys) 
	    | x== y = deleteFromList x ys
	    | otherwise = y : deleteFromList x ys


isLiter :: [Formula] -> Bool
isLiter [] = True
isLiter (x:xs) | not(isAlphaForm x) && not(isBetaForm x) && isLiter xs = True
	       | otherwise = False

tableauxForm :: Formula -> Formula
tableauxForm formula = doubleNagHandle(F (Identity ((:~:) formula)))


tableauBranchBeta x list 
	| elem ( doubleNagHandle(F (Identity ((:~:) x))) ) list = []
	| otherwise = list ++ [x] 
tableauBranchAlpha x y list
	| elem ( doubleNagHandle(F (Identity ((:~:) x))) ) list = []
	| elem ( doubleNagHandle(F (Identity ((:~:) y))) ) list = []
	| doubleNagHandle(F (Identity ((:~:) x))) == y = []
	| otherwise = list ++ [x] ++ [y]

branchHandle list 
	| list == [] = []
	| otherwise = (tableaux list)

tableaux f | isLiter f = [f]
tableaux (x:xs) 
	    | isBetaForm x = t1++t2
	    | isAlphaForm x = t3
	    | otherwise = t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  branchHandle (tableauBranchBeta bop1 s)
		      t2 =  branchHandle (tableauBranchBeta bop2 s)
		      t3 = branchHandle (tableauBranchAlpha aop1 aop2 s)
		      t4 = branchHandle (xs++[x])


	

closeTableaux :: [[Formula]]-> Bool
closeTableaux list
	| list == [] = True
	| otherwise = False 



isTheoremStr str = closeTableaux z
  where x = parse str
	r = removeComment x
	y = getFormula r
	z = tableaux [y]

isTheoremFile file = closeTableaux z
  where x = parseFile file
	xx = unsafePerformIO x
	r = removeComment xx
	y = getFormula r
	z = tableaux [y]


testFile file = z
  where x = parseFile file
	xx = unsafePerformIO x
	r = removeComment xx
	y = getFormula r
	z = tableaux [y]

testStr str = z
  where x = parse str
	r = removeComment x
	y = getFormula r
	z = tableaux [y]
