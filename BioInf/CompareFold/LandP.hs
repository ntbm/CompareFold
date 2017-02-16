-- Reeder and Giegerich Pseudoknot Class
module BioInf.CompareFold.LandP where

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

Grammar: LandP
N: S
N: T
N: <V,2>
N: <O,2>
T: c
S: S
S -> unp <<< c S
S -> nil <<< e
S -> jux <<< c T c T
T -> nil2 <<< e
T -> unp2 <<< c T
T -> jux2 <<< c T c T
S -> pse <<< T V O V O
<O,O> -> pk1 <<< [c,-] [T,-] <V,V> [-,c] [-,T]
<V,V> -> pk2 <<< [c,-] [T,-] <V,V> [-,c] [-,T]
<V,V> -> pair1 <<< [c,-] [T,-] [-,c] [-,T]
<O,O> -> pair2 <<< [c,-] [T,-] [-,c] [-,T]
//
Emit: LandP
|]
makeAlgebraProduct ''SigLandP

bpmax :: Monad m => SigLandP m Int Int Char Char
bpmax = SigLandP
  { unp    = \ c x               -> x
  , nil    = \ ()                -> 0
  , jux    = \ c x d y           -> if c `pairs` d then x + y + 1 else -999999
  , unp2   = \ c x               -> x
  , nil2   = \ ()                -> 0
  , jux2   = \ c x d y           -> if c `pairs` d then x + y + 1 else -999999
  , pse    = \ a () () u v -> a + u + v
  , pk1    = \ (Z:.a:.()) (Z:.t1:.()) y (Z:.():.b) (Z:.():.t2) -> if a `pairs` b then  t1 + t2 + y + 1 else -777777
  , pk2    = \ (Z:.a:.()) (Z:.t1:.()) y (Z:.():.b) (Z:.():.t2) -> if a `pairs` b then  t1 + t2 + y + 1 else -777777
  , pair1  = \ (Z:.c:.()) (Z:.t1:.()) (Z:.():.d) (Z:.():.t2)               -> if c `pairs` d then 1 + t1 + t2 else -888888
  , pair2  = \ (Z:.c:.()) (Z:.t1:.()) (Z:.():.d) (Z:.():.t2)               -> if c `pairs` d then 1 + t1 + t2 else -888888
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

pretty :: Monad m => SigLandP m [String] [[String]] Char Char
pretty = SigLandP
  { unp   = \ c [x] -> [x ++ "."]
  , jux   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , nil   = \ () -> [""]
  , unp2   = \ c [x] -> [x ++ "."]
  , jux2   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , nil2   = \ () -> [""]
  , pse   = \ [s1] () () [x1,x2] [y1,y2] -> [s1 ++ x1 ++ y1 ++ x2 ++ y2]
  , pk1 = \ (Z:.a:.()) (Z:.[t1]:.()) [y1,y2] (Z:.():.b) (Z:.():.[t2]) -> ["[" ++ t1 ++ y1 , y2 ++ "]" ++ t2]
  , pk2 = \ (Z:.a:.()) (Z:.[t1]:.()) [y1,y2] (Z:.():.b) (Z:.():.[t2]) -> ["[" ++ t1 ++ y1 , y2 ++ "]" ++ t2]
  , pair1 = \ (Z:.c1:.()) (Z:.[t1]:.()) (Z:.():.c2) (Z:.():.[t2]) -> ["[1"++ t1 , "]1" ++ t2]
  , pair2 = \ (Z:.c1:.()) (Z:.[t1]:.()) (Z:.():.c2) (Z:.():.[t2]) -> ["[2"++ t1 , "]2" ++ t2]
  , h     = SM.toList
}
{-# INLINE pretty #-}

landpPairMax :: Int -> String -> (Int, [[String]])
landpPairMax k inp =
  -- error "not implemented"
  (d, take k bs) where
   i = VU.fromList . Prelude.map toUpper $ inp
   n = VU.length i
   !(Z:.t:.u:.v:.w) = runInsideForward i
   d = unId $ axiom u
   bs = runInsideBacktrack i (Z:.t:.u:.v:.w)
{-# NOINLINE landpPairMax #-}


type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int


runInsideForward :: VU.Vector Char -> Z:.T:.X:.X:.T
runInsideForward i =
  -- error "not implemented"
  mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gLandP bpmax
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (chr i)
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

type X' = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type T' = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]


runInsideBacktrack :: VU.Vector Char -> Z:.T:.X:.X:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v:.w) =
  -- error "Not Implemented"
  unId $ axiom b
  where !(Z:._:.b:._:._) = gLandP (bpmax <|| pretty)
                          (toBacktrack t (undefined :: Id a -> Id a))
                          (toBacktrack u (undefined :: Id a -> Id a))
                          (toBacktrack v (undefined :: Id a -> Id a))
                          (toBacktrack w (undefined :: Id a -> Id a))
                          (chr i)
                          (chr i)
                          :: Z:.T':.X':.X':.T'
{-# NoInline runInsideBacktrack #-}
