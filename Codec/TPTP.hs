module Codec.TPTP(
                  module Codec.TPTP.Base
                 ,module Codec.TPTP.Import
                 ,module Codec.TPTP.Pretty
                 ,module Codec.TPTP.Export
                 ,module Codec.TPTP.Diff
                 )
    where

import Codec.TPTP.Base
import Codec.TPTP.Pretty
import Codec.TPTP.Import
import Codec.TPTP.Export
import Codec.TPTP.Diff

import Data.Functor.Identity

--test strings
t_a = parse "fof(test,axiom,~(a&b))."
t_b = parse "fof(test,axiom,(~a&b))."
t_negate =  parse "fof(test,axiom,a)."
t_negate2 = parse "fof(test,axiom,~a)."
t_eq = parse "fof(test,axiom,a<=>b)."
t_quant = parse "fof(test,axiom,? [A,Y] :(a|(a|b)))."
t_pred = parse "fof(test,axiom,fix(A,B))."
t_doublenegation = parse "fof(test,axiom,~(~(a)))."
t_scf1 = parse "fof(test,axiom,a&(b|c)&c)."
t_scf2 = parse "fof(test,axiom,a~&b)."
t_scf3 = parse "fof(test,axiom,~(a&b))."
t_scf4 = parse "fof(test,axiom,(a&~(x&y))=>d)."

--notes
-- <=> | <= | => | <~> | ~| | ~& | "|" | &
--(F (Identity (BinOp op1 op op2)))

-- ~
--(F (Identity ((:~:) op1))

-- atomicword
--(F (Identity (PredApp op1)))

-- ! | ?
--type = All | Exists
--cont = [V "A",...]
--(F (Identity (Quant type cont op1)))

-- part of predicate
--(T (Identity (Var (V x))))


--Misc

--Listof AFOrmula
get_list_element (x:xs)= x

--always used first
get_formula (AFormula a b c d) = c

enter_formula (F x) = x

enter_identity (Identity x) = x

enter_binop (BinOp a x b) =  a

step x = enter_binop(enter_identity(enter_formula(x)))

--walk though formula

walk_t [] = []
walk_t ((T (Identity ( Var v))):[]) = ((T (Identity( Var v))):[])
walk_t ((T (Identity ( Var v))):xs) = ((T (Identity( Var v))):walk_t(xs))

walk_f (F (Identity (Quant All cont op1)))		= (F (Identity (Quant All cont (walk_f(op1)))))
walk_f (F (Identity (Quant Exists cont op1)))	= (F (Identity (Quant Exists cont (walk_f(op1)))))
walk_f (F (Identity (PredApp aw t)))			= (F (Identity (PredApp aw (walk_t(t)))))
walk_f (F (Identity ((:~:) op1)))				= (F (Identity ((:~:) (walk_f(op1)))))
walk_f (F (Identity (BinOp op1 (:<=>:) op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<=>:) (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:<=:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<=:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:=>:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:=>:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:<~>:) op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<~>:) (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:~|:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:~|:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:~&:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:~&:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:&:)   op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:&:)   (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:|:)   op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:|:)   (walk_f(op2)))))









--SINGLE CLAUSE FORM

--utility

scf_formula (f,path)
	|path == []			= f
	|last path =="A" 	= scf_top(scf_trans_a_X(f,path))
	|otherwise 			= f

scf_path (f,path) = path

scf_merge ((f1,path1),(f2,path2),(F (Identity (BinOp op1 (:|:) op2))),path)
	|last path1 =="A"	= ((F (Identity (BinOp f1  (:|:) op2))),path1)
	|last path2 =="A"	= ((F (Identity (BinOp op1 (:|:) f2 ))),path2)
	|otherwise 			= ((F (Identity (BinOp op1 (:|:) op2))),path)

scf_negate x = (F (Identity ((:~:) x)))

--main (List of AFormula)
scf x = scf_top(get_formula(get_list_element(x)))

--top level (conjunctions)
scf_top (F (Identity (BinOp op1 (:&:) op2)))= (F (Identity (BinOp (scf_top(op1)) (:&:) (scf_top(op2)))))
scf_top (F (Identity (PredApp aw t))) = (F (Identity (PredApp aw t)))
scf_top (F (Identity ((:~:) (F (Identity (PredApp aw t)))))) = (F (Identity ((:~:) (F (Identity (PredApp aw t))))))
scf_top (F (Identity( (:~:) (F (Identity( ((:~:) op1))))))) = scf_top(op1)
scf_top x = scf_formula(scf_trans_b (x,[]))

--transformation level (disjunctions)

--anchor
scf_trans_b ((F (Identity (PredApp aw t))),path) 							= ((F (Identity (PredApp aw t))) 						,path)
scf_trans_b ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))),path) 	= ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))) ,path)

--beta formulas
scf_trans_b ((F (Identity (BinOp op1 (:|:) op2))) 							,path) = scf_merge(scf_trans_b(op1,path++["L"]),scf_trans_b(op2,path++["R"]),(F (Identity (BinOp op1 (:|:) op2))),path)
scf_trans_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) 	,path) = scf_merge(scf_trans_b(op1,path++["L"]),scf_trans_b(op2,path++["R"]),(F (Identity (BinOp op1 (:|:) op2))),path)
scf_trans_b ((F (Identity( (:~:) (F (Identity( ((:~:) op1))))))) 			,path) = scf_trans_b (op1,path)
scf_trans_b ((F (Identity (BinOp op1 (:=>:) op2))) 							,path) = scf_trans_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) op2))) 				,path)
scf_trans_b ((F (Identity (BinOp op1 (:<=:) op2))) 							,path) = scf_trans_b ((F (Identity (BinOp op1 			  (:|:) (scf_negate(op2))))),path)
scf_trans_b ((F (Identity (BinOp op1 (:~&:)  op2)))							,path) = scf_trans_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) (scf_negate(op2))))),path)
scf_trans_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) 	,path) = scf_trans_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) (scf_negate(op2))))),path)

--alpha formulas
scf_trans_b ((F (Identity (BinOp op1 (:&:) op2)))							,path) = ((F (Identity (BinOp op1 (:&:) op2)))							,path++["A"])
scf_trans_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2)))))) 	,path++["A"])
scf_trans_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2))))))	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))) ,path++["A"])
scf_trans_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2))))))	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))) ,path++["A"])
scf_trans_b ((F (Identity (BinOp op1 (:~|:)  op2)))							,path) = ((F (Identity (BinOp op1 (:~|:)  op2)))						,path++["A"])
scf_trans_b ((F (Identity (Quant q cont op1)))								,path) = ((F (Identity (Quant q cont (scf_formula(scf_trans_b(op1,path)))))),scf_path(scf_trans_b(op1,path)))


scf_trans_a_X (f,path) = (F (Identity (BinOp (scf_trans_a_L(f,path)) (:&:) (scf_trans_a_R(f,path)))))

scf_trans_a_L (f,[])=f
scf_trans_a_L ((F (Identity (BinOp op1 (:&:) op2)))							,["A"]) = op1
scf_trans_a_L ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	,["A"]) = scf_negate(op1)
scf_trans_a_L ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))),["A"]) = op1
scf_trans_a_L ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))),["A"]) = scf_negate(op1)
scf_trans_a_L ((F (Identity (BinOp op1 (:~|:)  op2)))						,["A"]) = scf_negate(op1)
scf_trans_a_L ((F (Identity (BinOp op1 op op2)))							,x:xs)
	|x=="L" = (F (Identity (BinOp (scf_trans_a_L(op1,xs)) op op2)))
	|x=="R" = (F (Identity (BinOp op1 op (scf_trans_a_L(op2,xs)))))

scf_trans_a_R (f,[])=f
scf_trans_a_R ((F (Identity (BinOp op1 (:&:) op2)))						 	,["A"]) = op2
scf_trans_a_R ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	,["A"]) = scf_negate(op2)
scf_trans_a_R ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))),["A"]) = scf_negate(op2)
scf_trans_a_R ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))),["A"]) = op2
scf_trans_a_R ((F (Identity (BinOp op1 (:~|:)  op2)))						,["A"]) = scf_negate(op2)
scf_trans_a_R ((F (Identity (BinOp op1 op op2)))							,x:xs)
	|x=="L" = (F (Identity (BinOp (scf_trans_a_R(op1,xs)) op op2)))		
	|x=="R" = (F (Identity (BinOp op1 op (scf_trans_a_R(op2,xs)))))








--DOUBLE CLAUSE FORM

dcf_formula (f,path)
	|path == []			= f
	|last path =="B" 	= dcf_top(dcf_trans_b_X(f,path))
	|otherwise 			= f

dcf_path (f,path) = path

dcf_merge ((f1,path1),(f2,path2),(F (Identity (BinOp op1 (:|:) op2))),path)
	|last path1 =="B"	= ((F (Identity (BinOp f1  (:|:) op2))),path1)
	|last path2 =="B"	= ((F (Identity (BinOp op1 (:|:) f2 ))),path2)
	|otherwise 			= ((F (Identity (BinOp op1 (:|:) op2))),path)

dcf_negate x = (F (Identity ((:~:) x)))

--main
dcf x = dcf_top(get_formula(get_list_element(x)))

--top level (disjunctions)
dcf_top (F (Identity (BinOp op1 (:|:) op2)))= (F (Identity (BinOp (dcf_top(op1)) (:|:) (dcf_top(op2)))))
dcf_top (F (Identity (PredApp aw t))) = (F (Identity (PredApp aw t)))
dcf_top (F (Identity ((:~:) (F (Identity (PredApp aw t)))))) = (F (Identity ((:~:) (F (Identity (PredApp aw t))))))
dcf_top (F (Identity( (:~:) (F (Identity( ((:~:) op1))))))) = dcf_top(op1)
dcf_top x = dcf_formula(dcf_trans_a (x,[]))

--transformation level (conjunctions)

--anchor
dcf_trans_a ((F (Identity (PredApp aw t))),path) 							= ((F (Identity (PredApp aw t))) 						,path)
dcf_trans_a ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))),path) 	= ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))) ,path)

--beta formulas
dcf_trans_a ((F (Identity (BinOp op1 (:|:) op2))) 							,path) = ((F (Identity (BinOp op1 						(:|:)  op2))) 		,path++["B"])
dcf_trans_a ((F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) 	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 	(:~|:) op2))))))	,path++["B"])
dcf_trans_a ((F (Identity (BinOp op1 (:=>:) op2))) 							,path) = ((F (Identity (BinOp op1 						(:=>:) op2))) 		,path++["B"])
dcf_trans_a ((F (Identity (BinOp op1 (:<=:) op2))) 							,path) = ((F (Identity (BinOp op1 						(:<=:) op2))) 		,path++["B"])
dcf_trans_a ((F (Identity (BinOp op1 (:~&:)  op2)))							,path) = ((F (Identity (BinOp op1 						(:~&:) op2)))		,path++["B"])
dcf_trans_a ((F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) 	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 	(:&:)  op2)))))) 	,path++["B"])

--alpha formulas
dcf_trans_a ((F (Identity (BinOp op1 (:&:) op2)))							,path) = dcf_trans_a((F (Identity (BinOp op1 		(:|:)  op2)))				,path)
dcf_trans_a ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	,path) = dcf_trans_a((F (Identity (BinOp (dcf_negate(op1)) (:|:)  (dcf_negate(op2)))))	,path)
dcf_trans_a ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2))))))	,path) = dcf_trans_a((F (Identity (BinOp op1 				(:=>:) (dcf_negate(op2)))))	,path)
dcf_trans_a ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2))))))	,path) = dcf_trans_a((F (Identity (BinOp (dcf_negate(op1)) (:<=:) op2))) 				,path)
dcf_trans_a ((F (Identity (BinOp op1 (:~|:)  op2)))							,path) = dcf_trans_a((F (Identity (BinOp op1 				(:|:)  op2)))				,path)
dcf_trans_a ((F (Identity (Quant q cont op1)))								,path) = ((F (Identity (Quant q cont (dcf_formula(dcf_trans_a(op1,path)))))),dcf_path(dcf_trans_a(op1,path)))

dcf_trans_b_X (f,path) = (F (Identity (BinOp (dcf_trans_b_L(f,path)) (:|:) (dcf_trans_b_R(f,path)))))

dcf_trans_b_L (f,[])=f
dcf_trans_b_L ((F (Identity (BinOp op1 (:|:) op2))) 						,["B"]) = op1
dcf_trans_b_L ((F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2))))))	,["B"]) = op1
dcf_trans_b_L ((F (Identity (BinOp op1 (:=>:) op2))) 						,["B"]) = dcf_negate(op1)
dcf_trans_b_L ((F (Identity (BinOp op1 (:<=:) op2))) 						,["B"]) = op1
dcf_trans_b_L ((F (Identity (BinOp op1 (:~&:)  op2)))						,["B"]) = dcf_negate(op1)
dcf_trans_b_L ((F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) 	,["B"]) = dcf_negate(op1)
dcf_trans_b_L ((F (Identity (BinOp op1 op op2)))							,x:xs)
	|x=="L" = (F (Identity (BinOp (dcf_trans_b_L(op1,xs)) op op2)))
	|x=="R" = (F (Identity (BinOp op1 op (dcf_trans_b_L(op2,xs)))))


dcf_trans_b_R (f,[])=f
dcf_trans_b_R ((F (Identity (BinOp op1 (:|:) op2))) 						,["B"]) = op2
dcf_trans_b_R ((F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2))))))	,["B"]) = op2
dcf_trans_b_R ((F (Identity (BinOp op1 (:=>:) op2))) 						,["B"]) = op2
dcf_trans_b_R ((F (Identity (BinOp op1 (:<=:) op2))) 						,["B"]) = dcf_negate(op2)
dcf_trans_b_R ((F (Identity (BinOp op1 (:~&:)  op2)))						,["B"]) = dcf_negate(op2)
dcf_trans_b_R ((F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) 	,["B"]) = dcf_negate(op2)
dcf_trans_b_R ((F (Identity (BinOp op1 op op2)))							,x:xs)
	|x=="L" = (F (Identity (BinOp (dcf_trans_b_R(op1,xs)) op op2)))
	|x=="R" = (F (Identity (BinOp op1 op (dcf_trans_b_R(op2,xs)))))