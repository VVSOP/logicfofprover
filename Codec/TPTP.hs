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

t_a = parse "fof(test,axiom,~(a&b))."
t_b = parse "fof(test,axiom,(~a&b))."
t_negate =  parse "fof(test,axiom,a)."
t_negate2 = parse "fof(test,axiom,~a)."
t_eq = parse "fof(test,axiom,a<=>b)."
t_quant = parse "fof(test,axiom,? [A,Y] :fix(A))."
t_pred = parse "fof(test,axiom,fix(A,B))."

--Listof AFOrmula
get_list_element (x:xs)= x

--always used first
get_formula (AFormula a b c d) = c

enter_formula (F x) = x

enter_identity (Identity x) = x

enter_binop (BinOp a x b) = x

-- <=> | <= | => | <~> | ~| | ~& | "|" | &
--(F (Identity (BinOp op1 op op2)))

walk_t [] = []
walk_t ((T (Identity( Var v))):[]) = ((T (Identity( Var v))):[])
walk_t ((T (Identity( Var v))):xs) = ((T (Identity( Var v))):walk_t(xs))

walk_f (F (Identity( Quant All cont op1)))		= (F (Identity( Quant All cont (walk_f(op1)))))
walk_f (F (Identity( Quant Exists cont op1)))	= (F (Identity( Quant Exists cont (walk_f(op1)))))
walk_f (F (Identity( PredApp aw t)))			= (F (Identity( PredApp aw (walk_t(t)))))
walk_f (F (Identity( (:~:) op1)))				= (F (Identity( (:~:) (walk_f(op1)))))
walk_f (F (Identity( BinOp op1 (:<=>:) op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:<=>:) (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:<=:)  op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:<=:)  (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:=>:)  op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:=>:)  (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:<~>:) op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:<~>:) (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:~|:)  op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:~|:)  (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:~&:)  op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:~&:)  (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:&:)   op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:&:)   (walk_f(op2)))))
walk_f (F (Identity( BinOp op1 (:|:)   op2))) 	= (F (Identity( BinOp (walk_f(op1)) (:|:)   (walk_f(op2)))))

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

tb_negate_binop (BinOp op1 (:&:) op2) = (BinOp op1 (:|:) op2)
tb_negate_binop (BinOp op1 (:|:) op2) = (BinOp op1 (:&:) op2)
