-- Reeder and Giegerich Pseudoknot Class
module BioInf.CompareFold.CandC where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Text.Printf

import           ADP.Fusion.Subword
import           Data.PrimitiveArray as PA hiding (map)

import           FormalLanguage

-- | Define signature and grammar

[formalLanguage|
Verbose

Grammar: CandC
N: S
N: T
N: <U,2>
N: <V,2>
N: <W,2>
T: c
S: S

S     -> nil1  <<< e
S     -> unp1  <<< c S
S     -> pair1 <<< c S c S
S     -> psk   <<< U S V T U S V S
T     -> nil2  <<< e
T     -> unp2  <<< c T
<U,U> -> dum   <<< <V,V>
<V,V> -> pair2 <<< [c,-] [-,c]
<V,V> -> pk1   <<< [-,c] [-,T] <W,W> [c,-]
<W,W> -> stem1 <<< [c,-] [T,-] [-,c]
<W,W> -> stem2 <<< [-,c] [-,T] <W,W> [c,-] [T,-]
//
Emit: CandC
|]
makeAlgebraProduct ''SigCandC

bpmax :: Monad m => SigCandC m Int Int Char Char
bpmax = SigCandC
  { unp1   = \ c x               -> x
  , nil1   = \ ()                -> 0
  , pair1  = \ c x d y           -> if c `pairs` d then x + y + 1 else -999999
  , psk    = \ () s1 () t u s2 v s3 -> s1 + t + u + s2 + v + s3
  , nil2   = \ ()                -> 0
  , unp2   = \ c x               -> x
  , dum    = \ v                 -> v
  , pair2  = \ (Z:.a:.()) (Z:.():.b) -> if pairs a b then 1 else -987700
  , pk1    = \ (Z:.():.a) (Z:.():.t) w (Z:.b:.()) -> if pairs a b then t + w + 1 else -999999
  , stem1  = \ (Z:.a:.()) (Z:.t:.()) (Z:.():.b) -> if pairs a b then t + 1 else -989979
  , stem2  = \ (Z:.():.a) (Z:.():.t1) w (Z:.b:.()) (Z:.t2:.()) -> if pairs a b then t1 + t2 + w + 1 else -888888
  , h      = SM.foldl' max (-999999)
}
{-# INLINE bpmax #-}

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

pretty :: Monad m => SigCandC m [String] [[String]] Char Char
pretty = SigCandC
  { unp1   = \ c [x]       -> ["." ++ x]
  , nil1   = \ ()          -> [""]
  , pair1  = \ c [x] d [y] -> ["(" ++ x ++ ")" ++ y]
  , psk    = \ () [s1] () [t] [u1,u2] [s2] [v1,v2] [s3] -> [u1 ++ s1 ++ v1 ++ t ++ u2 ++ s2 ++ v2 ++ s3]
  , nil2   = \ ()    -> [""]
  , unp2   = \ c [x] -> [x ++ "."]
  , dum    = \ [v1, v2] -> [v1 ++ v2]
  , pair2  = \ (Z:.a:.()) (Z:.():.b) -> ["[" ++ "]"]
  , pk1    = \ (Z:.():.a) (Z:.():.[t]) [w1, w2] (Z:.b:.()) -> [w1 ++ "[", "]" ++ t ++ w2]
  , stem1  = \ (Z:.a:.()) (Z:.[t]:.()) (Z:.():.b) -> ["[" ++ t, "]"]
  , stem2  = \ (Z:.():.a) (Z:.():.[t1]) [w1, w2] (Z:.b:.()) (Z:.[t2]:.()) -> [w1 ++ "[" ++ t1, "]" ++ t2 ++ w2]
  , h     = SM.toList
}
{-# INLINE pretty #-}

candCPairMax :: Int -> String -> (Int, [[String]])
candCPairMax k inp =
  -- error "not implemented"
  (d, take k bs) where
   i = VU.fromList . Prelude.map toUpper $ inp
   n = VU.length i
   !(Z:.t:.u:.v:.w:.x) = runInsideForward i
   d = unId $ axiom u
   bs = runInsideBacktrack i (Z:.t:.u:.v:.w:.x)
{-# NOINLINE candCPairMax #-}


type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int


runInsideForward :: VU.Vector Char -> Z:.X:.X:.T:.T:.T
runInsideForward i =
  -- error "not implemented"
  mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gCandC bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-778999) []))
                        (chr i)
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

type X' = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type T' = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]


runInsideBacktrack :: VU.Vector Char -> Z:.X:.X:.T:.T:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v:.w:.x) =
  -- error "Not Implemented"
  unId $ axiom b
  where !(Z:.b:._:._:._:._) = gCandC (bpmax <|| pretty)
                          (toBacktrack t (undefined :: Id a -> Id a))
                          (toBacktrack u (undefined :: Id a -> Id a))
                          (toBacktrack v (undefined :: Id a -> Id a))
                          (toBacktrack w (undefined :: Id a -> Id a))
                          (toBacktrack x (undefined :: Id a -> Id a))
                          (chr i)
                          (chr i)
                          :: Z:.X':.X':.T':.T':.T'
{-# NoInline runInsideBacktrack #-}
