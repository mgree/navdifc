{-# OPTIONS_GHC -itarget #-}
{-# LANGUAGE StandaloneDeriving #-}
module Testing where

import FourPoints
import Basic
import Terms
import qualified LBracketSyntax as LB
import qualified LBracketBigStep as LB
import qualified LBracketSmallStep as LB
import qualified LThrowBigStep as LT
import qualified LThrowSmallStep as LT
import qualified LNaVSyntax as LN
import qualified LNaVSmallStep as LN
import qualified LThrowDBigStep as LD
import qualified LThrowDSmallStep as LD
import qualified EncodeLNaVintoLThrow as EN2T
import qualified EncodeLThrowIntoLNaV as ET2N
import qualified EncodeLThrowIntoLNaVTakeTwo as ET2Np
import qualified EncodeLNaVintoLBracket as EN2B
import qualified EncodeLThrowDIntoLThrow as ED2T
import qualified EncodeLThrowIntoLThrowD as ET2D

import Prelude
-- More info about QuickCheck here:
-- http://www.cse.chalmers.se/~rjmh/QuickCheck/
-- http://book.realworldhaskell.org/read/testing-and-quality-assurance.html
import Test.QuickCheck
-- More info about HUnit here:
-- http://hunit.sourceforge.net/HUnit-1.0/Guide.html
-- http://leiffrenzel.de/papers/getting-started-with-hunit.html
import Test.HUnit
import List
import Data.List
import Debug.Trace

deriving instance Show FP
deriving instance Show Tag
deriving instance Show Const
deriving instance Show BOp
deriving instance Show Dir
deriving instance Show Tm
deriving instance Show LN.Box
deriving instance Show LN.Val
deriving instance Show LB.Val
deriving instance Show LT.Result
deriving instance Show LT.Frame
deriving instance Show LD.Result
deriving instance Show LD.Frame

deriving instance Eq FP
deriving instance Eq Tag
deriving instance Eq Const
deriving instance Eq BOp
deriving instance Eq Dir
deriving instance Eq LN.Box
deriving instance Eq LT.Result
deriving instance Eq LD.Result

-- Equality up to alpha

eq_var_m :: [(Var, Var)] -> Var -> Var -> Bool
eq_var_m m x1 x2 =
  case get m x1 of
    Just x2' -> x2 == x2'
    Nothing -> x1 == x2

eq_tm_m :: [(Var, Var)] -> Tm -> Tm -> Bool
eq_tm_m m t1 t2 =
  case (t1, t2) of
    (TVar x1, TVar x2) ->
      eq_var_m m x1 x2
    (TConst c1, TConst c2) ->
      c1 == c2
    (TLet x1 t1' t1'', TLet x2 t2' t2'') ->
      eq_tm_m m t1' t2' && eq_tm_m ((x1,x2):m) t1'' t2''
    (TAbs x1 t1', TAbs x2 t2') ->
      eq_tm_m ((x1,x2):m) t1' t2'
    (TApp x1 x1', TApp x2 x2') -> 
      (eq_var_m m x1 x2) && (eq_var_m m x1' x2')
    (TInx d1 x1, TInx d2 x2) ->
      d1 == d2 && eq_var_m m x1 x2
    (TMatch x1 x1' t1' t1'', TMatch x2 x2' t2' t2'') ->
      eq_var_m m x1 x2 && eq_tm_m ((x1',x2'):m) t1' t2'
                       && eq_tm_m ((x1',x2'):m) t1'' t2''
    (TTag x1, TTag x2) ->
      eq_var_m m x1 x2
    (TBOp bo1 x1 x1', TBOp bo2 x2 x2') ->
      (bo1 == bo2) && (eq_var_m m x1 x2) && (eq_var_m m x1' x2')
    (TBracket x1 t1', TBracket x2 t2') -> 
      (eq_var_m m x1 x2) && (eq_tm_m m t1' t2')
    (TLabelOf x1, TLabelOf x2) ->
      eq_var_m m x1 x2;
    (TGetPc, TGetPc) -> True
    (TMkNav x1, TMkNav x2) ->
      eq_var_m m x1 x2
    (TToSum x1, TToSum x2) ->
      eq_var_m m x1 x2;
    (TThrow x1, TThrow x2) ->
      eq_var_m m x1 x2;
    (TCatch t1' x1 t1'', TCatch t2' x2 t2'') ->
      eq_tm_m m t1' t2' && eq_tm_m ((x1,x2):m) t1'' t2''
    (_, _) -> False

instance Eq Tm where
  (==) = eq_tm_m []

eq_varLN_mr :: [(Var, Var)] -> LN.Env -> LN.Env -> Var -> Var -> Bool
eq_varLN_mr m r1 r2 x1 x2 =
   (case get m x1 of
     Just x2' -> x2 == x2'
     Nothing ->
       case (get r1 x1, get r2 x2) of
         (Just a1, Just a2) -> eq_atomLN_mr [] a1 a2
         (_, _) -> False)

eq_tmLN_mr :: [(Var, Var)] -> LN.Env -> LN.Env -> Tm -> Tm -> Bool
eq_tmLN_mr m r1 r2 t1 t2 =
  case (t1, t2) of
    (TVar x1, TVar x2) ->
      eq_varLN_mr m r1 r2 x1 x2
    (TConst c1, TConst c2) ->
      c1 == c2
    (TLet x1 t1' t1'', TLet x2 t2' t2'') ->
      eq_tmLN_mr m r1 r2 t1' t2' && eq_tmLN_mr ((x1,x2):m) r1 r2 t1'' t2''
    (TAbs x1 t1', TAbs x2 t2') ->
      eq_tmLN_mr ((x1,x2):m) r1 r2 t1' t2'
    (TApp x1 x1', TApp x2 x2') -> 
      (eq_varLN_mr m r1 r2 x1 x2) && (eq_varLN_mr m r1 r2 x1' x2')
    (TInx d1 x1, TInx d2 x2) ->
      d1 == d2 && eq_varLN_mr m r1 r2 x1 x2
    (TMatch x1 x1' t1' t1'', TMatch x2 x2' t2' t2'') ->
      eq_varLN_mr m r1 r2 x1 x2 && eq_tmLN_mr ((x1',x2'):m) r1 r2 t1' t2'
                              && eq_tmLN_mr ((x1',x2'):m) r1 r2 t1'' t2''
    (TTag x1, TTag x2) ->
      eq_varLN_mr m r1 r2 x1 x2
    (TBOp bo1 x1 x1', TBOp bo2 x2 x2') ->
      (bo1 == bo2) && (eq_varLN_mr m r1 r2 x1 x2) && (eq_varLN_mr m r1 r2 x1' x2')
    (TBracket x1 t1', TBracket x2 t2') -> 
      (eq_varLN_mr m r1 r2 x1 x2) && (eq_tmLN_mr m r1 r2 t1' t2')
    (TLabelOf x1, TLabelOf x2) ->
      eq_varLN_mr m r1 r2 x1 x2;
    (TGetPc, TGetPc) -> True
    (TMkNav x1, TMkNav x2) ->
      eq_varLN_mr m r1 r2 x1 x2
    (TToSum x1, TToSum x2) ->
      eq_varLN_mr m r1 r2 x1 x2;
    (TThrow x1, TThrow x2) ->
      eq_varLN_mr m r1 r2 x1 x2;
    (TCatch t1' x1 t1'', TCatch t2' x2 t2'') ->
      eq_tmLN_mr m r1 r2 t1' t2' && eq_tmLN_mr ((x1,x2):m) r1 r2 t1'' t2''
    (_, _) -> False

eq_boxLN_mr :: [(Var, Var)] -> LN.Box -> LN.Box -> Bool
eq_boxLN_mr m b1 b2 =
  case (b1, b2) of
    (LN.V v1, LN.V v2) -> eq_valLN_mr [] v1 v2
    (LN.D e1, LN.D e2) -> e1 == e2
    (_, _) -> False

eq_atomLN_mr :: [(Var, Var)] -> LN.Atom -> LN.Atom -> Bool
eq_atomLN_mr m a1 a2 =
  eq_boxLN_mr m (fst a1) (fst a2)
  && (snd a1) == (snd a2)
  
eq_valLN_mr :: [(Var, Var)] -> LN.Val -> LN.Val -> Bool
eq_valLN_mr m v1 v2 =
  case (v1, v2) of
  (LN.VConst c1, LN.VConst c2) ->
    c1 == c2
  (LN.VInx d1 a1, LN.VInx d2 a2) ->
    d1 == d2 && eq_atomLN_mr m a1 a2
  (LN.VClos r1' x1 t1, LN.VClos r2' x2 t2) ->
    eq_tmLN_mr ((x1, x2):m) r1' r2' t1 t2
  (_, _) -> False

instance Eq LN.Val where
  (==) = eq_valLN_mr []

-- boring repetition

eq_varLB_mr :: [(Var, Var)] -> LB.Env -> LB.Env -> Var -> Var -> Bool
eq_varLB_mr m r1 r2 x1 x2 =
   (case get m x1 of
     Just x2' -> x2 == x2'
     Nothing ->
       case (get r1 x1, get r2 x2) of
         (Just a1, Just a2) -> eq_atomLB_mr [] r1 r2 a1 a2
         (_, _) -> False)

eq_tmLB_mr :: [(Var, Var)] -> LB.Env -> LB.Env -> Tm -> Tm -> Bool
eq_tmLB_mr m r1 r2 t1 t2 =
  case (t1, t2) of
    (TVar x1, TVar x2) ->
      eq_varLB_mr m r1 r2 x1 x2
    (TConst c1, TConst c2) ->
      c1 == c2
    (TLet x1 t1' t1'', TLet x2 t2' t2'') ->
      eq_tmLB_mr m r1 r2 t1' t2' && eq_tmLB_mr ((x1,x2):m) r1 r2 t1'' t2''
    (TAbs x1 t1', TAbs x2 t2') ->
      eq_tmLB_mr ((x1,x2):m) r1 r2 t1' t2'
    (TApp x1 x1', TApp x2 x2') -> 
      (eq_varLB_mr m r1 r2 x1 x2) && (eq_varLB_mr m r1 r2 x1' x2')
    (TInx d1 x1, TInx d2 x2) ->
      d1 == d2 && eq_varLB_mr m r1 r2 x1 x2
    (TMatch x1 x1' t1' t1'', TMatch x2 x2' t2' t2'') ->
      eq_varLB_mr m r1 r2 x1 x2 && eq_tmLB_mr ((x1',x2'):m) r1 r2 t1' t2'
                              && eq_tmLB_mr ((x1',x2'):m) r1 r2 t1'' t2''
    (TTag x1, TTag x2) ->
      eq_varLB_mr m r1 r2 x1 x2
    (TBOp bo1 x1 x1', TBOp bo2 x2 x2') ->
      (bo1 == bo2) && (eq_varLB_mr m r1 r2 x1 x2) && (eq_varLB_mr m r1 r2 x1' x2')
    (TBracket x1 t1', TBracket x2 t2') -> 
      (eq_varLB_mr m r1 r2 x1 x2) && (eq_tmLB_mr m r1 r2 t1' t2')
    (TLabelOf x1, TLabelOf x2) ->
      eq_varLB_mr m r1 r2 x1 x2;
    (TGetPc, TGetPc) -> True
    (TMkNav x1, TMkNav x2) ->
      eq_varLB_mr m r1 r2 x1 x2
    (TToSum x1, TToSum x2) ->
      eq_varLB_mr m r1 r2 x1 x2;
    (TThrow x1, TThrow x2) ->
      eq_varLB_mr m r1 r2 x1 x2;
    (TCatch t1' x1 t1'', TCatch t2' x2 t2'') ->
      eq_tmLB_mr m r1 r2 t1' t2' && eq_tmLB_mr ((x1,x2):m) r1 r2 t1'' t2''
    (_, _) -> False

eq_atomLB_mr :: [(Var, Var)] -> LB.Env -> LB.Env -> LB.Atom -> LB.Atom -> Bool
eq_atomLB_mr m r1 r2 a1 a2 =
  eq_valLB_mr m r1 r2 (fst a1) (fst a2)
  && (snd a1) == (snd a2)
  
eq_valLB_mr :: [(Var, Var)] -> LB.Env -> LB.Env -> LB.Val -> LB.Val -> Bool
eq_valLB_mr m r1 r2 v1 v2 =
  case (v1, v2) of
  (LB.VConst c1, LB.VConst c2) ->
    c1 == c2
  (LB.VInx d1 a1, LB.VInx d2 a2) ->
    d1 == d2 && eq_atomLB_mr m r1 r2 a1 a2
  (LB.VClos r1 x1 t1, LB.VClos r2 x2 t2) ->
    eq_tmLB_mr ((x1, x2):m) r1 r2 t1 t2
  (_, _) -> False

instance Eq LB.Val where
  (==) = eq_valLB_mr [] [] []


-- Unit testing the step function for LNaV

-- Redefining nstep/mstep/tstep without the index
-- that was giving us termination guarantees in Coq

nstep' :: LN.Cfg -> LN.Cfg
nstep' c = if LN.final c then c else nstep' (LN.step c)

mstep' :: Tm -> LN.Cfg
mstep' t = nstep' (((Low, []), []), LN.CR t)

tstep' :: Tm -> LN.Atom
tstep' t = 
  case mstep' t of
  (((pc, rho), []), LN.CA a) -> a

test_eq_tm_m1 = TestCase $ assertEqual "eq_tm_m1"
                  (TAbs 0 (TVar 0))
                  (TAbs 42 (TVar 42))

test_eq_tm_m2 = TestCase $ assertBool "eq_tm_m2" $
                  not ((TAbs 0 (TVar 0)) ==
                       (TAbs 0 (TVar 42)))

test_eq_val_mr1 = TestCase $ assertEqual "eq_val_mr1"
                    (LN.VClos [] 0 (TVar 0))
                    (LN.VClos [] 2 (TVar 2))

test_eq_val_mr2 = TestCase $ assertEqual "eq_val_mr2"
                    (LN.VClos [] 0 (TVar 0))
                    (LN.VClos [(1,(LN.V LN.vUnit,Low))] 2 (TVar 2))

test_eq_val_mr3 = TestCase $ assertBool "eq_val_mr3" $
                    not $ (LN.VClos [] 0 (TVar 1)) ==
                          (LN.VClos [(1,(LN.V LN.vUnit,Low))] 2 (TVar 2))

test_ex0 = TestCase $ assertEqual "step unit"
             (LN.V LN.vUnit, Low)
             (tstep' tCUnit) 

test_ex0' = TestCase $ assertEqual "step true"
              (LN.V LN.vTrue, Low)
              (tstep' tTrue)

vId = LN.VClos [] 0 (TVar 0)

test_ex1 = TestCase $ assertEqual "step (id id)"
             (LN.V vId, Low)
             (tstep' (tApp tId tId))

prog2 = tIf tTrue tTrue tFalse

test_ex2 = TestCase $ assertEqual "step prog2"
             (LN.V LN.vTrue, Low)
             (tstep' prog2)

prog3 = tIf tTrue (TConst (CExcp eType)) (TConst (CExcp eBracket))
res3 =  (LN.V (LN.VConst (CExcp eType)), Low)

test_ex3 = TestCase $ assertEqual "step prog3 = res3"
             res3 (tstep' prog3)

-- Properties of FP label algebra
-- These properties are easy to prove in Coq
-- I'm QuickChecking them only to get familiar with QuickCheck


instance Arbitrary FP where
  arbitrary = elements [Low, Med1, Med2, High]

(<:) = fp_flows
(\/) = fp_join

prop_flows_top l = l <: High

prop_flows_bottom l = Low <: l

prop_flows_trans l1 l2 l3 =
  l1 <: l2 ==> l2 <: l3 ==> l1 <: l3

prop_join_commutes l1 l2 = l1 \/ l2 == l2 \/ l1

prop_join_Low l = l \/ Low == l

prop_join_High l = l \/ High == High

prop_join_upper_bound l1 l2 = (l1 <: (l1 \/ l2)) && (l2 <: (l1 \/ l2))

prop_join_minimal l1 l2 l =
  l1 <: l ==> l2 <: l ==> l1 \/ l2 <: l


-- Generating random programs

instance Arbitrary Tag where
  arbitrary = elements [TagFun, TagLab, TagTag, TagExcp]

arbitraryExcp = elements [eType, eBracket, 42]

instance Arbitrary Const where
  arbitrary = oneof $ [arbitrary >>= return . CLab] ++
                      [arbitrary >>= return . CTag] ++
                      [arbitraryExcp >>= return . CExcp]

instance Arbitrary BOp where
  arbitrary = elements [BEq, BCmp, BJoin]
    
arbitraryLBracketTm' :: ([Var] -> Int -> Gen Tm) -> [Var] -> Int -> Gen Tm
arbitraryLBracketTm' frec vars size = 
  frequency $
    (if size>0 then
       [(size `div` 3, do
            s <- choose (0,size-1)
            let x = fresh vars
            t1 <- frec vars s
            t2 <- frec (x:vars) (size-s-1)
            return $ TLet x t1 t2)]
     else [])
    ++
    [(1, oneof $ 
        (if length vars > 0
         then [elements vars >>= return . TVar]
         else [])
        ++
        [arbitrary >>= return . TConst]
        ++
        (if size>0 then
           [do
               let x = fresh vars
               t <- frec (x:vars) (size-1)
               return $ TAbs x t]
        else [])
        ++
        (if length vars > 0
         then [do 
                  x1 <- elements vars 
                  x2 <- elements vars
                  return $ TApp x1 x2]
         else [])
        ++
        (if length vars > 0
         then [do 
                  x <- elements vars
                  let x1 = fresh vars
                  s <- choose (0,size-1)
                  t1 <- frec vars s
                  t2 <- frec (x:vars) (size-s-1)
                  return $ TMatch x x1 t1 t2]
         else [])
        ++
        (if length vars > 0
         then [elements vars >>= return . TTag]
         else [])
        ++
        (if length vars > 0
         then [do 
                  b <- arbitrary
                  x1 <- elements vars 
                  x2 <- elements vars
                  return $ TBOp b x1 x2]
         else [])
        ++
        (if length vars > 0 && size > 0
         then [do 
                  x <- elements vars 
                  t <- frec (x:vars) (size-1)
                  return $ TBracket x t]
         else [])
        ++
        (if length vars > 0
         then [elements vars >>= return . TLabelOf]
         else [])
        ++
        [return TGetPc]
    )]

-- tying the recursive knot
arbitraryLBracketTm'' = arbitraryLBracketTm' arbitraryLBracketTm''
arbitraryLBracketTm = sized $ \size -> arbitraryLBracketTm'' [] size

arbitraryLNaVTm' :: [Var] -> Int -> Gen Tm
arbitraryLNaVTm' vars size = 
    frequency $
    (if length vars > 0 then
       [(1, do
            x <- elements vars 
            return $ TMkNav x)]
       ++
       [(1, do
            x <- elements vars 
            return $ TToSum x)]
     else [])
    ++
    [(10, arbitraryLBracketTm' arbitraryLNaVTm' vars size)]

arbitraryLNaVTm = sized $ \size -> arbitraryLNaVTm' [] size

arbitraryLThrowTm' :: [Var] -> Int -> Gen Tm
arbitraryLThrowTm' vars size = 
    frequency $
    (if length vars > 0 then
       [(1, do
            x <- elements vars 
            return $ TThrow x)]
     else [])
    ++
    (if size>0 then
       [(1 + size `div` 5, do
            s <- choose (0,size-1)
            let x = fresh vars
            t1 <- arbitraryLThrowTm' vars s
            t2 <- arbitraryLThrowTm' (x:vars) (size-s-1)
            return $ TCatch t1 x t2)]
     else [])    
    ++
    [(10, arbitraryLBracketTm' arbitraryLThrowTm' vars size)]

arbitraryLThrowTm = sized $ \size -> arbitraryLThrowTm' [] size

arbitraryLThrowDTm' :: [Var] -> Int -> Gen Tm
arbitraryLThrowDTm' vars size = 
    frequency $
    (if length vars > 0 then
       [(1, do
            x <- elements vars 
            return $ TThrow x)]
     else [])
    ++
    (if size>0 then
       [(1 + size `div` 5, do
            s <- choose (0,size-1)
            let x = fresh vars
            t1 <- arbitraryLThrowDTm' vars s
            t2 <- arbitraryLThrowDTm' (x:vars) (size-s-1)
            return $ TCatch t1 x t2)]
     else [])    
    ++
    (if length vars > 0 then
       [(1, do
            x <- elements vars 
            return $ TToSum x)]
     else [])
    ++
    [(10, arbitraryLBracketTm' arbitraryLThrowDTm' vars size)]

arbitraryLThrowDTm = sized $ \size -> arbitraryLThrowDTm' [] size

-- testing that the generators above stay in the corresponding
-- sublanguages

in_lthrow :: Tm -> Bool
in_lthrow (TMkNav _) = False
in_lthrow (TToSum _) = False
in_lthrow (TLet _ t1 t2) = in_lthrow t1 && in_lthrow t2
in_lthrow (TAbs _ t) = in_lthrow t
in_lthrow (TMatch _ _ t1 t2) = in_lthrow t1 && in_lthrow t2
in_lthrow (TBracket _ t) = in_lthrow t
in_lthrow (TCatch t1 _ t2) = in_lthrow t1 && in_lthrow t2
in_lthrow _ = True

in_lthrowd :: Tm -> Bool
in_lthrowd (TMkNav _) = False
in_lthrowd (TLet _ t1 t2) = in_lthrowd t1 && in_lthrowd t2
in_lthrowd (TAbs _ t) = in_lthrowd t
in_lthrowd (TMatch _ _ t1 t2) = in_lthrowd t1 && in_lthrowd t2
in_lthrowd (TBracket _ t) = in_lthrowd t
in_lthrowd (TCatch t1 _ t2) = in_lthrowd t1 && in_lthrowd t2
in_lthrowd _ = True

in_lnav :: Tm -> Bool
in_lnav (TThrow _) = False
in_lnav (TCatch _ _ _) = False
in_lnav (TLet _ t1 t2) = in_lnav t1 && in_lnav t2
in_lnav (TAbs _ t) = in_lnav t
in_lnav (TMatch _ _ t1 t2) = in_lnav t1 && in_lnav t2
in_lnav (TBracket _ t) = in_lnav t
in_lnav _ = True

in_lbracket :: Tm -> Bool
in_lbracket t = in_lnav t && in_lthrow t

prop_arbitraryLBracketTm_in_lbracket =
  forAll arbitraryLBracketTm $ \t -> in_lbracket t

prop_arbitraryLNaVTm_in_lnav =
  forAll arbitraryLNaVTm $ \t -> in_lnav t

prop_arbitraryLThrowTm_in_lthrow =
  forAll arbitraryLThrowTm $ \t -> in_lthrow t

prop_arbitraryLThrowDTm_in_lthrowd =
  forAll arbitraryLThrowDTm $ \t -> in_lthrowd t

-- this seems useful for "collect"-ing statistics
tm_kind :: Tm -> String
tm_kind (TVar _) = "var"
tm_kind (TConst _) = "const"
tm_kind (TLet _ _ _) = "let"
tm_kind (TAbs _ _) = "abs"
tm_kind (TApp _ _) = "app"
tm_kind (TTag _) = "tag"
tm_kind (TBOp _ _ _) = "bop"
tm_kind (TBracket _ _) = "bracket"
tm_kind (TLabelOf _) = "label_of"
tm_kind (TGetPc) = "get_pc"
tm_kind (TMkNav _) = "mk_nav"
tm_kind (TToSum _) = "to_sum"
tm_kind (TThrow _) = "throw"
tm_kind (TCatch _ _ _) = "catch"

-- test that all generated programs are closed

prop_generate_closed_LBracket t =
  forAll arbitraryLBracketTm $ \t -> collect (tm_kind t) $ null (fv_tm t)

prop_generate_closed_LNaV t =
  forAll arbitraryLNaVTm $ \t -> collect (size_tm t) $ null (fv_tm t)

prop_generate_closed_LThrow t =
  forAll arbitraryLThrowTm $ \t -> collect (size_tm t) $ null (fv_tm t)

prop_generate_closed_LThrowD t =
  forAll arbitraryLThrowDTm $ \t -> collect (size_tm t) $ null (fv_tm t)

-- equality on terms is an equivalence relation

prop_eq_tm_refl t = t == t

-- the next two properties have very bad coverage,
-- but only when adding collect?
prop_eq_tm_sym t1 t2 =
  -- collect (t1 == t2, tm_kind t1, size_tm t1) $
  (t1 == t2) ==> (t2 == t1)

prop_eq_tm_trans t1 t2 t3 =
  (t1 == t2 && t2 == t3) ==> (t1 == t3)

-- the small-step semantics of LambdaNaV never produces "bad" exceptions

bad_excp :: Excp -> Bool
bad_excp e = e >= 2 && e < 42

atom_bad_excp :: LN.Atom -> Bool
atom_bad_excp (LN.D e, _) = bad_excp e
atom_bad_excp _ = False

matom_bad_excp :: Maybe ((LN.Atom, FP),Integer) -> Bool
matom_bad_excp (Just ((a,_pc),_)) = atom_bad_excp a
matom_bad_excp Nothing = False

box_kind :: LN.Box -> String
box_kind (LN.V (LN.VConst _)) = "constant"
box_kind (LN.V (LN.VInx _ _)) = "sum"
box_kind (LN.V (LN.VClos _ _ _)) = "function"
box_kind (LN.D e) = "NaV"

-- we only run for sn steps to get rid of out of memory errors
sn = 1000

step_inteval :: Integer -> String
step_inteval n =
  let middle = div sn 2 in
  if n < middle then "[0," ++ show middle ++ ")"
  else "[" ++ show middle ++ "," ++ show sn ++ "]"

ln_finished :: Maybe ((LN.Atom,FP),Integer) -> String
ln_finished (Just (((b, _pc), _), n)) =
  "Finished with " ++ box_kind b ++ " after " ++ step_inteval n ++ " steps"
ln_finished Nothing = "Not finished after " ++ show sn ++ " steps"

prop_ln_no_bad_excp t =
  forAll arbitraryLNaVTm $ \t -> 
  let mapcs = LN.sstep sn t in
      collect (ln_finished mapcs) $
        not $ matom_bad_excp mapcs

-- the small-step semantics of LambdaThrow never produces "bad" exceptions

result_bad_excp :: LT.Result -> Bool
result_bad_excp (LT.Throw e) = bad_excp e
result_bad_excp _ = False

mres_bad_excp :: Maybe ((LT.Result,FP),Integer) -> Bool
mres_bad_excp (Just ((r,_pc),_step)) = result_bad_excp r
mres_bad_excp Nothing = False

res_kind :: LT.Result -> String
res_kind (LT.Suc (LB.VConst _, _)) = "constant"
res_kind (LT.Suc (LB.VInx _ _, _)) = "sum"
res_kind (LT.Suc (LB.VClos _ _ _, _)) = "function"
res_kind (LT.Throw e) = "exception"

lt_finished :: Maybe ((LT.Result,FP),Integer) -> String
lt_finished (Just ((res,_pc), n)) =
  "Finished with " ++ res_kind res ++ " after " ++ step_inteval n ++ " steps"
lt_finished Nothing = "Not finished after " ++ show sn ++ " steps"

prop_lt_no_bad_excp t = 
  forAll arbitraryLThrowTm $ \t -> 
  let mrs = LT.sstep sn t in
      collect (lt_finished mrs) $
        not $ mres_bad_excp mrs

-- the small-step semantics of LambdaThrowD never produces "bad" exceptions

result_bad_excp_d :: LD.Result -> Bool
result_bad_excp_d (LD.Throw e) = bad_excp e
result_bad_excp_d _ = False

mres_bad_excp_d :: Maybe ((LD.Result,FP),Integer) -> Bool
mres_bad_excp_d (Just ((r,_pc),_step)) = result_bad_excp_d r
mres_bad_excp_d Nothing = False

res_kind_d :: LD.Result -> String
res_kind_d (LD.Suc (LN.V (LN.VConst _), _)) = "constant"
res_kind_d (LD.Suc (LN.V (LN.VInx _ _), _)) = "sum"
res_kind_d (LD.Suc (LN.V (LN.VClos _ _ _), _)) = "function"
res_kind_d (LD.Suc (LN.D _, _)) = "delayed-excp"
res_kind_d (LD.Throw e) = "exception"

lt_finished_d :: Maybe ((LD.Result,FP),Integer) -> String
lt_finished_d (Just ((res,_pc), n)) =
  "Finished with " ++ res_kind_d res ++ " after " ++ step_inteval n ++ " steps"
lt_finished_d Nothing = "Not finished after " ++ show sn ++ " steps"

prop_ltd_no_bad_excp t = 
  forAll arbitraryLThrowDTm $ \t -> 
  let mrs = LD.sstep sn t in
      collect (lt_finished_d mrs) $
        not $ mres_bad_excp_d mrs

-- testing the translation from LNaV into LThrow

-- encoded program in LThrow always produces a sum result (or loops forever)
-- in particular, encoded program causes no fatal errors (uncaught exceptions)

prop_EN2T_sum =
  forAll arbitraryLNaVTm $ \t ->
  let mrs = LT.sstep sn (EN2T.encode t) in
  collect (lt_finished mrs) $
  case mrs of
    Just ((LT.Suc (LB.VInx _ _, _), _), _) -> True
    Just _ -> False
    Nothing -> True

-- some helpers that are useful for debugging

minimize_env :: [Var] -> LB.Env -> LB.Env
minimize_env vars rho = Prelude.map (\x -> (x, case get rho x of { Just a -> a ; Nothing -> (LB.vUnit, Low)})) vars

show_cfg :: LT.Cfg -> String
show_cfg (((_pc, rho), _k), LT.CR t) =
  "\n\nCR ( " ++ show t ++ 
--  "\nwhere rho (minimized) = "++ show (minimize_env (nub (fv_tm t)) rho) ++ " )"
  "\nwhere rho = "++ show rho ++ " )"
show_cfg (((_pc, rho), k), LT.CA a) =
  "\n\nCA with "
  ++ (if null k then "empty k" else "head k=" ++ show (head k))
  ++ "\nwhere a = " ++ show a
  ++ "\nand with rho = " ++ show rho
show_cfg (_, LT.CT e) = "\n\nCT" ++ show e

-- debugging stuff 
encN2T_no_excp_instance = 
  let t = TLet 1001 (TLet 1001 (TConst (CLab Med1)) (TToSum 1001)) (TLet 1002 (TLet 1002 (TLet 1002 (TLet 1002 (TVar 1001) (TTag 1002)) (TApp 1001 1001)) (TLet 1003 (TLet 1003 (TApp 1001 1002) (TLet 1004 (TAbs 1004 (TTag 1001)) TGetPc)) (TApp 1002 1001))) (TToSum 1001)) in
  let t' = EN2T.encode t in
  let tr = List.rev $ snd $ LT.lmstep sn t' in
  let tr' = Prelude.map show_cfg tr in
  (t', drop (length tr' - 10) tr', length tr') -- drop (length tr' - 10) tr'

-- mapping function between LambdaNaV values and LThrow values
-- note: it has to go in this direction
-- (the other direction is not functional / deterministic)

valEN2T :: LN.Val -> LB.Val
valEN2T (LN.VConst c) = LB.vInl $ (LB.VConst c, Low)
valEN2T (LN.VInx d aLN) = LB.vInl (LB.VInx d $ atomEN2T aLN, Low)
valEN2T (LN.VClos rho x t) =
  let rho' = List.map (\(x,a) -> (x, atomEN2T a)) rho in
  let t' = EN2T.encode t in
  LB.vInl (LB.VClos rho' x t' , Low)

atomEN2T :: LN.Atom -> LB.Atom
atomEN2T (LN.V v,l) = (valEN2T v, l)
atomEN2T (LN.D e,l) = (LB.vInr (LB.vExcp e, Low), l)

prop_EN2T_correct =
  forAll arbitraryLNaVTm $ \tLN ->
  let tLT = EN2T.encode tLN in
  let mrs = LT.sstep sn tLT in
  collect (lt_finished mrs) $
  case mrs of
    Just ((LT.Throw e, _pc), _) -> False -- checked by prop_EN2T_no_excp
    Just ((LT.Suc aLT, pcLT), _) -> 
      case LN.sstep sn tLN of
        Just ((aLN, pcLN),_) ->
          pcLT == pcLN && atomEN2T aLN == aLT
        Nothing -> True -- this won't happen anyway
    Nothing -> True

test_EN2T_instance =
  let t = TLet 1 TGetPc (TLet 2 (TCatch (TMatch 1 2 (TBOp BJoin 1 1) (TConst (CTag TagExcp))) 2 (TLabelOf 1)) (TLet 3 (TTag 2) TGetPc)) in
  let t' = EN2T.encode t in
  let Just ((LT.Suc a', pcLT),_s) = LT.sstep sn t' in
  let Just ((a, pcLN),_s) = LN.sstep sn t in
  TestCase $ assertBool "test_encLNintoLT_instance" $
  atomEN2T a == a'

vBox :: LN.Atom -> LN.Val
vBox a = LN.vInl a

resEncT2N :: LT.Result -> LN.Atom
resEncT2N (LT.Throw e) = (LN.D e, Low)
resEncT2N (LT.Suc a) = (LN.V (vBox (atomEncT2N a)), Low)

valEncT2N :: LB.Val -> LN.Val
valEncT2N (LB.VConst c) = (LN.VConst c)
valEncT2N (LB.VInx d a) = (LN.VInx d (atomEncT2N a))
valEncT2N (LB.VClos rho x t) =
  let rho' = List.map (\(x,a) -> (x, atomEncT2N a)) rho in
  let t' = ET2N.encode t in
  (LN.VClos rho' x t')

atomEncT2N :: LB.Atom -> LN.Atom
atomEncT2N (v,l) = (LN.V (valEncT2N v), l)

prop_ET2N_correct =
  forAll arbitraryLThrowTm $ \t ->
  let t' = ET2N.encode t in
  let mas = LN.sstep sn t' in
  collect (ln_finished mas) $
  case mas of
    Just ((aLN,pcLN),_) ->
      case LT.sstep sn t of
        Just ((resLT, pcLT), _) -> 
          resEncT2N resLT == aLN
        Nothing -> True -- this won't happen anyway
    Nothing -> True


-- encoded program in LThrow always produces a sum result (or loops
-- forever) in particular, encoded program causes no NaVs

prop_ET2Np_sum =
  forAll arbitraryLThrowTm $ \t ->
  let mas = LN.sstep sn (ET2Np.encode t) in
  collect (ln_finished mas) $
  case mas of
    Just (((LN.V (LN.VInx _ _), _), _), _) -> True
    Just _ -> False
    Nothing -> True

resEncT2Np :: LT.Result -> LN.Atom
resEncT2Np (LT.Suc a) = (LN.V (LN.vInl (atomEncT2Np a)), Low)
resEncT2Np (LT.Throw e) = (LN.V (LN.vInr (LN.V (LN.VConst (CExcp e)), Low)), Low)

valEncT2Np :: LB.Val -> LN.Val
valEncT2Np (LB.VConst c) = (LN.VConst c)
valEncT2Np (LB.VInx d a) = (LN.VInx d (atomEncT2Np a))
valEncT2Np (LB.VClos rho x t) =
  let rho' = List.map (\(x,a) -> (x, atomEncT2Np a)) rho in
  let t' = ET2Np.encode t in
  (LN.VClos rho' x t')

atomEncT2Np :: LB.Atom -> LN.Atom
atomEncT2Np (v,l) = (LN.V (valEncT2Np v), l)

prop_ET2Np_correct =
  forAll arbitraryLThrowTm $ \t ->
  let t' = ET2Np.encode t in
  let mas = LN.sstep sn t' in
  collect (ln_finished mas) $
  case mas of
    Just ((aLN,pcLN),_) ->
      case LT.sstep sn t of
        Just ((resLT, pcLT), _) -> 
          resEncT2Np resLT == aLN
        Nothing -> True -- this won't happen anyway
    Nothing -> True

some_ET2Np_instance =
  let t = TLet 1 (TLet 1 (TConst (CLab High)) (TLet 2 (TCatch (TLet 2 (TMatch 1 2 (TApp 1 1) (TConst (CLab High))) (TApp 1 2)) 2 (TBracket 1 (TBOp BCmp 2 2))) (TTag 2))) (TBOp BEq 1 1) in
  let t' = ET2Np.encode t in
  let Just ((aLN, pcLN), _s) = LN.sstep sn t' in
  let Just ((resLT, pcLT), _s) = LT.sstep sn t in
  putStr $
  "t'=" ++ show  t' ++ 
  "\naLN (got after translation) = " ++ show aLN ++ 
  "\nresLT = " ++ show resLT ++
  "\nresEncT2N resLT (expected) = " ++ show (resEncT2Np resLT) ++
  "\ncorrect = " ++ show (resEncT2Np resLT == aLN) ++ "\n"


-- Programs encoded by EN2L always produce a double sum result (or
-- loop forever); in particular, encoded programs do not fatally fail

lbValKind :: LB.Val -> String
lbValKind (LB.VConst _) = "constant"
lbValKind (LB.VInx _ _) = "sum"
lbValKind (LB.VClos _ _ _) = "function"

lbFinished :: Maybe (Maybe (LB.Atom, FP), Integer) -> String
lbFinished (Just (Just ((v, _l), _pc), n)) =
  "Finished with " ++ lbValKind v ++ " after " ++ step_inteval n ++ " steps"
lbFinished (Just (Nothing, n)) =
  "Fatal error after " ++ step_inteval n ++ " steps"
lbFinished Nothing = "Not finished after " ++ show sn ++ " steps"

prop_EN2B_double_sum =
  forAll arbitraryLNaVTm $ prop_EN2B_double_sum'

prop_EN2B_double_sum' t =
  let mas = LB.sstep sn (EN2B.encode t) in
--  collect (lbFinished mas) $
  case mas of
    Just (Just ((LB.VInx _ (LB.VInx _ _, _l), Low), _pc), _n) -> True
    Just _ -> False
    Nothing -> True

resEncN2B :: LN.Atom -> LB.Atom
resEncN2B a = (LB.vInl (atomEncN2B a), Low)

-- TODO: this will need to be much more complicated because of clearance
valEncN2B :: LN.Val -> LB.Val
valEncN2B (LN.VConst c) = (LB.VConst c)
valEncN2B (LN.VInx d a) = (LB.VInx d (atomEncN2B a))
valEncN2B (LN.VClos rho x t) =
  let rho'' = List.map (\(x,a) -> (x, atomEncN2B a)) rho in
  let rho' = (100, (LB.VConst (CLab High), Low)) : rho'' in
  let t' = EN2B.encode' t 100 in {- TODO: what clearance? -}
  (LB.VClos rho' x t')

boxEncN2B :: LN.Box -> LB.Val
boxEncN2B (LN.V v) = LB.vInl (valEncN2B v, Low)
boxEncN2B (LN.D e) = LB.vInr (LB.vExcp e, Low)

atomEncN2B :: LN.Atom -> LB.Atom
atomEncN2B (b,l) = (boxEncN2B b, l)

-- hack: filtering out the results containing closures, since I can't
-- properly compare them in the presence of clearance

hasClos :: LB.Val -> Bool
hasClos (LB.VConst c) = False
hasClos (LB.VInx d a) = hasClosAtom a
hasClos (LB.VClos rho x t) = True
hasClosAtom (v,l) = hasClos v

prop_EN2B_correct =
  forAll arbitraryLNaVTm $ \tLN ->
  let tLB = EN2B.encode tLN in
  let rLB = LB.sstep sn tLB in
  collect (lbFinished rLB) $
  case rLB of
    Just (Just (aLB, pcLB), _) ->
      case LN.sstep sn tLN of
        Just ((aLN, pcLT), _) ->
          not (hasClosAtom aLB) ==> -- discards around 5% of the tests
          pcLB == pcLT && resEncN2B aLN == aLB
        Nothing -> property True -- this won't happen anyway
    Just (Nothing, _) -> property False
    Nothing -> property True

test_EN2B_instance =
  let tLN = TLet 1 
              (TConst (CLab High))
              (TLet 2
                (TBracket 1 (TLabelOf 1))
                (TBracket 2 (TMkNav 2))
              )
  in
  let tLB = EN2B.encode tLN in
  let Just (Just (aLB, pcLB), _) = LB.sstep sn tLB in
  let Just ((aLN, pcLT), _) = LN.sstep sn tLN in
  -- putStr $
  -- "tLB=" ++ show  tLB ++ 
  -- "\naLN (original) = " ++ show aLN ++
  -- "\naLB (encoding) = " ++ show aLB ++
  -- "\nresEncN2B aLN (expected) = " ++ show (resEncN2B aLN) ++
  -- "\ncorrect = " ++ show (pcLB == pcLT && resEncN2B aLN == aLB) ++ "\n"
  TestCase $ assertBool "test_EN2B_instance" $
  pcLB == pcLT && resEncN2B aLN == aLB


-- testing translation from LThrow into LThrowD

prop_ED2T_sum =
  forAll arbitraryLThrowDTm $ \t ->
  let mrs = LT.sstep sn (ED2T.encode t) in
  collect (lt_finished mrs) $
  case mrs of
    Just ((LT.Suc (LB.VInx _ _, _), _), _) -> True
    Just ((LT.Throw _, _), _) -> True
    Just _ -> False
    Nothing -> True

valED2T :: LN.Val -> LB.Val
valED2T (LN.VConst c) = LB.VConst c
valED2T (LN.VInx d aLD) = LB.VInx d $ atomED2T aLD
valED2T (LN.VClos rho x t) =
  let rho' = List.map (\(x,a) -> (x, atomED2T a)) rho in
  let t' = ED2T.encode t in
  LB.VClos rho' x t'

atomED2T :: LN.Atom -> LB.Atom
atomED2T (LN.V v,l) = (LB.vInl (valED2T v, Low), l)
atomED2T (LN.D e,l) = (LB.vInr (LB.vExcp e, Low), l)

resED2T :: LD.Result -> LT.Result
resED2T (LD.Suc a) = LT.Suc (atomED2T a)
resED2T (LD.Throw e) = LT.Throw e

prop_ED2T_correct =
  forAll arbitraryLThrowDTm $ \tLD ->
  let tLT = ED2T.encode tLD in
  let mrs = LT.sstep sn tLT in
  collect (lt_finished mrs) $
  case mrs of
    Just ((resLT, pcLT), _) ->
      case LD.sstep sn tLD of
        Just ((resLD, pcLD),_) ->
          pcLT == pcLD && resED2T resLD == resLT
        Nothing -> True -- this won't happen anyway
    Nothing -> True

test_ED2T_instance =
   let tLD = TLet 1 (TConst (CLab High)) (TLet 2 (TConst (CExcp 42)) (TLet 3 (TBracket 1 (TVar 2)) (TBOp BCmp 2 3))) in
  let tLT = ED2T.encode tLD in
  let Just ((resLD, pcLD), _) = LD.sstep sn tLD in
  let Just ((resLT, pcLT), _) = LT.sstep sn tLT in
  -- putStr $
  -- "tLT=" ++ show tLT ++ 
  -- "\nresLD (original) = " ++ show resLD ++
  -- "\npcLD (original) = " ++ show pcLD ++
  -- "\nresLT (encoding) = " ++ show resLT ++
  -- "\npcLT (encoding) = " ++ show pcLT ++
  -- "\nresED2T resLD (expected) = " ++ show (resED2T resLD) ++
  -- "\ncorrect = " ++ show (pcLT == pcLD && resED2T resLD == resLT) ++ "\n"
  TestCase $ assertBool "test_ED2T_instance" $
  pcLT == pcLD && resED2T resLD == resLT


-- testing (trivial) translation from LThrow into LThrowD

prop_ET2D_no_primitive_delayed =
  forAll arbitraryLThrowDTm $ \t ->
  let mrs = LD.sstep sn (ET2D.encode t) in
  collect (lt_finished_d mrs) $
  case mrs of
    Just ((LD.Suc (LN.V _, _), _), _) -> True
    Just ((LD.Throw _, _), _) -> True
    Just _ -> False
    Nothing -> True

-- this is basically just identity/injection

valET2D :: LB.Val -> LN.Val
valET2D (LB.VConst c) = LN.VConst c
valET2D (LB.VInx d aLT) = LN.VInx d $ atomET2D aLT
valET2D (LB.VClos rho x t) =
  let rho' = List.map (\(x,a) -> (x, atomET2D a)) rho in
  let t' = ET2D.encode t in
  LN.VClos rho' x t'

atomET2D :: LB.Atom -> LN.Atom
atomET2D (v,l) = (LN.V (valET2D v), l)

resET2D :: LT.Result -> LD.Result
resET2D (LT.Suc a) = LD.Suc (atomET2D a)
resET2D (LT.Throw e) = LD.Throw e

prop_ET2D_correct =
  forAll arbitraryLThrowTm $ \tLT ->
  let tLD = ET2D.encode tLT in
  let mrs = LD.sstep sn tLD in
  collect (lt_finished_d mrs) $
  case mrs of
    Just ((resLD, pcLD), _) ->
      case LT.sstep sn tLT of
        Just ((resLT, pcLT),_) ->
          pcLD == pcLT && resET2D resLT == resLD
        Nothing -> True -- this won't happen anyway
    Nothing -> True

test_ET2D_instance =
--  let tLT = TLet 1 (TLet 1 (TConst (CLab Med2)) (TBracket 1 (TLabelOf 1))) (TCatch (TThrow 1) 2 (TCatch (TTag 1) 3 (TLet 4 (TThrow 3) (TCatch (TLet 5 TGetPc (TThrow 1)) 5 (TThrow 3))))) in
  let tLT = TLet 1 (TLet 1 (TLet 1 (TConst (CLab Med2)) (TCatch (TThrow 1) 2 (TBracket 1 (TBOp BCmp 1 1)))) (TVar 1)) (TTag 1) in
  let tLD = ET2D.encode tLT in
  let Just ((resLT, pcLT), _) = LT.sstep sn tLT in
  let Just ((resLD, pcLD), _) = LD.sstep sn tLD in
  -- putStr $
  -- "tLT=" ++ show tLT ++ 
  -- "\nresLT (original) = " ++ show resLT ++
  -- "\npcLT (original) = " ++ show pcLT ++
  -- "\nresLD (encoding) = " ++ show resLD ++
  -- "\npcLD (encoding) = " ++ show pcLD ++
  -- "\nresET2D resLT (expected) = " ++ show (resET2D resLT) ++
  -- "\ncorrect = " ++ show (pcLD == pcLT && resET2D resLT == resLD) ++ "\n"
  TestCase $ assertBool "test_ET2D_instance" $
  pcLD == pcLT && resET2D resLT == resLD


main = runTestTT $ TestList
       [test_eq_tm_m1, test_eq_tm_m2,
        test_eq_val_mr1, test_eq_val_mr2, test_eq_val_mr3,
        test_ex0, test_ex0', test_ex1, test_ex2, test_ex3
       , test_EN2T_instance
       , test_EN2B_instance
       , test_ED2T_instance
       , test_ET2D_instance
       ]

-- To run 500,000 instances random tests use this:
runP p = quickCheckWith (stdArgs {maxSuccess = 500000}) p
-- More Args:
-- replay :: Maybe (StdGen, Int)
--     should we replay a previous test? 
-- maxSuccess :: Int
--     maximum number of successful tests before succeeding 
-- maxDiscard :: Int
--     maximum number of discarded tests before giving up 
-- maxSize :: Int
--     size to use for the biggest test cases 
-- chatty :: Bool
--     whether to print anything 

-- To test the correctness of all encodings use this:
runAll = do
  runP prop_EN2T_correct
  runP prop_ET2N_correct
  runP prop_ET2Np_correct
  runP prop_EN2B_correct
  runP prop_ED2T_correct
  runP prop_ET2D_correct

-- TODO: is an encoding from LT into LB that is similar to the one
-- from LT into LN possible? [Yes, this is possible, but we can also
-- get it by transitivity, by composing ET2N and EN2B]
-- It would have to use a fixed version of
-- the clearance idea, but otherwise why not?
-- Suc (v@l) --> (S (v@l))@bot
-- Throw e --> (T (e@bot))@bot
-- clearance failure -> C@bot
-- for an encoded datatype Data = S v | T e | C
-- (basically encoding "option (inl v)" would do)
-- Note that, as in ET2N, the variables in the environment will only
-- store real values.

-- TODO: how about a special term generator where more
-- classification/brackets is/are used

-- TODO: generate globally unique names
-- (bound list + keep bigger avoid list)

-- TODO: Check that step preserves the same set of free + bound names

-- TODO: check that step _preserves_ fv inluded in dom rho
-- Q: How to show that such _invariants_ are preserved by the semantics
-- the problem is that not all random configurations are "good"
-- starting configurations; so maybe the check needs to be done
-- part of the step iteration function

-- TODO: nstep and lnstep have
-- {- XXX if this appears you might want to optimize things -}

-- TODO: how about building another generator using the "t_..."
-- derived forms (then we don't need to bias generating lets and we
-- can maybe generate more meaningful programs)?

-- TODO: special generator for well-typed programs??
-- at least in LThrow ~70% of the programs terminate with exceptions
