{-#LANGUAGE TypeOperators#-}

module Task2 where

-- Author: Radosław Rowicki 386088

import Data.Map
import Data.Function


-- |I am using Map for representing all "mutable" functions. Map will be noted as long arrow.
-- Application of map is done by (!) operator, eg. `mapfunc ! argument`.
-- Modification of map is done by `insert` function, eg. `insert key value map`.
-- Union of two maps resolves collisions by taking bindings from first map,
-- eg `union (insert 1 21 empty) (insert 1 37 empty) ! 1 == 21`
type (-->) = Map

type VarName = String
type ProcName = String
type Loc = Int
type Store = Loc --> Integer
type VarEnv = VarName --> Loc
type ProcEnv = ProcName --> Proc
type Proc = Loc -> Cont -> Cont

type Cont = Store -> Store
type ContE = Integer -> Cont
type ContB = Bool -> Cont
type ContD = VarEnv -> ProcEnv -> Cont

data Expr = LitInt Integer | Var VarName | Plus Expr Expr | Minus Expr Expr | Mult Expr Expr
data BExpr = LitBool Bool | Con BExpr BExpr | Eq Expr Expr | Lt Expr Expr | Neg BExpr

data Decl = VarDecl VarName Expr | ProcDecl ProcName VarName Instr | EmptyDecl | ConsDecl Decl Decl
data Instr = Skip | Assign VarName Expr | Semicolon Instr Instr | If BExpr Instr Instr |
  While BExpr Instr | Begin Decl Instr | Call ProcName VarName


type EXP = VarEnv -> ContE -> Cont
type BEXP = VarEnv -> ContB -> Cont
type STMT = VarEnv -> ProcEnv -> Cont -> Cont
type DECL = VarEnv -> ProcEnv -> ContD -> Cont

type E = Expr -> EXP
type B = BExpr -> BEXP
type I = Instr -> STMT
type D = Decl -> DECL


expr :: E
expr e pv k = case e of
  LitInt i -> k i
  Var v -> \s -> k (s ! (pv ! v)) s
  Plus a b -> expr a pv (\aa -> expr b pv (\bb -> k (aa + bb)))
  Minus a b -> expr a pv (\aa -> expr b pv (\bb -> k (aa - bb)))
  Mult a b -> expr a pv (\aa -> expr b pv (\bb -> k (aa * bb)))


bexpr :: B
bexpr be pv k = case be of
  LitBool b -> k b
  Con a b -> bexpr a pv (\aa -> bexpr b pv (\bb -> k (aa && bb)))
  Eq a b -> expr a pv (\aa -> expr b pv (\bb -> k (aa == bb)))
  Lt a b -> expr a pv (\aa -> expr b pv (\bb -> k (aa < bb)))
  Neg b -> bexpr b pv (\bb -> k (not bb))


decl :: D
decl dcl pv pp k = case dcl of
  EmptyDecl -> k pv pp
  ConsDecl d1 d2 ->
    decl d1 pv pp (\pv1 pp1 ->
                      decl d2 pv1 pp1 (\pv2 pp2 ->
                                          k (union pv2 pv1) (union pp2 pp1)))
  ProcDecl pname aname body -> k pv (insert pname prc pp) where
    prc = fix phi
    phi recprc argloc kp =
      let newpv = insert aname argloc pv -- register argument on given loc
          newpp = insert pname recprc pp -- register myself
      in instr body newpv newpp kp -- run body
  VarDecl name e ->
    expr e pv (\val s -> -- first eval expression
                 let (i, news) = alloc val s -- allocate memory
                 in k (insert name i pv) pp news) -- update var env


instr :: I
instr i pv pp k = case i of
  Skip -> k
  Assign x e -> expr e pv (\n s -> k (insert (pv ! x) n s))
  Semicolon i1 i2 -> instr i1 pv pp (instr i2 pv pp k)
  If cond th el ->
    bexpr cond pv (\b -> if b then instr th pv pp k else instr el pv pp k)
  While cond ii -> fix phi where
    phi while =
      bexpr cond pv (\b -> if b then instr ii pv pp while else k)
  Begin ds ii -> decl ds pv pp (\dpv dpp -> instr ii dpv dpp k)
  Call proc arg -> \s ->
    let argloc = pv ! arg
        (i, news) = alloc (s ! argloc) s -- backup of value under arg
    -- run procedure on location of copy of arg,
    -- then move modified value to original position
    in move i argloc (((pp ! proc) i k) news)


-- |Moves data from one place to another
move :: Loc -> Loc -> Store -> Store
move from to s = delete from (insert to (s ! from) s)


-- |Allocates new data in store
alloc :: Integer -> Store -> (Loc, Store)
alloc dat store =
  let newId = maximum (-1:(keys store)) + 1 -- get new index as "greater by one than maximum of indices"
  in (newId, insert newId dat store) -- insert data beneath new index and return


-- sample :: Instr
-- sample = Begin (ConsDecl
--                 (VarDecl "x" (LitInt 0))
--                 (ProcDecl "p" "y"
--                  (Semicolon
--                   (Assign "y" (LitInt 3))
--                   (If (Eq (Var "x") (LitInt 3))
--                    (Assign "y" (LitInt 4))
--                    Skip
--                  )
--                 )
--                ))
--          (Call "p" "x")

-- sample = Begin (ConsDecl (VarDecl "x" (LitInt 100)) (VarDecl "x" (LitInt 0)))
--   (
--    (While (Lt (Var "x") (LitInt 10))
--     (Assign "x"
--      (Plus (Var "x") (LitInt 1))
--     )
--    )
--   )
