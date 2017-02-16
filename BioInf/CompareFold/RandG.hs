-- Reeder and Giegerich Pseudoknot Class
module BioInf.CompareFold.RandG where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
--import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Text.Printf

import           ADP.Fusion.Subword
import           Data.PrimitiveArray as PA hiding (map)

import           FormalLanguage

-- | Define signature and grammar

[formalLanguage|
Verbose

Grammar: RandG
N: S
N: <V,2>
N: <O,2>
T: c
S: S
S -> unp <<< c S
S -> nil <<< e
S -> jux <<< c S c S
S -> pse <<< O S V S O S V S
<O,O> -> pk1 <<< [c,-] <V,V> [-,c]
<V,V> -> pk2 <<< [c,-] <V,V> [-,c]
<O,O> -> pair1 <<< [c,c]
<V,V> -> pair2 <<< [c,c]
//
Emit: RandG
|]
makeAlgebraProduct ''SigRandG

bpmax :: Monad m => SigRandG m Int Int Char Char
bpmax = SigRandG
  { unp   = \ c x                   -> x
  , nil   = \ ()                    -> 0
  , jux   = \ c x d y               -> if c `pairs` d then x + y + 1 else -999999
  , pse   = \ () a () b o c v d     -> a + b + c + d + o + v
  , pk1 = \ (Z:.a:.()) y (Z:.():.b) -> if a `pairs` b then  y + 1 else -777777
  , pk2 = \ (Z:.a:.()) y (Z:.():.b) -> if a `pairs` b then  y + 1 else -777777
  , pair1 = \ (Z:.c:.d)             -> if c `pairs` d then 1 else -888888 -- \ (Z:.():.()) -> 0
  , pair2 = \ (Z:.c:.d)             -> if c `pairs` d then 1 else -888888 -- \ (Z:.():.()) -> 0
  , h     = SM.foldl' max (-999999)
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

pretty :: Monad m => SigRandG m [String] [[String]] Char Char
pretty = SigRandG
  { unp   = \ c [x] -> [x ++ "."]
  , jux   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , pse   = \ () [s1] () [s2] [u1,u2] [s3] [v1,v2] [s4] -> [u1 ++ s1 ++ v1 ++ s2 ++ u2 ++ s3 ++ v2 ++ s4]
  , nil   = \ () -> [""]
  , pk1 = \ (Z:.a:.()) [y1,y2] (Z:.():.b) -> ["[" ++ y1 , y2 ++ "]"]
  , pk2 = \ (Z:.a:.()) [y1,y2] (Z:.():.b) -> ["{" ++ y1 , y2 ++ "}"]
  , pair1 = \ (Z:.c1:.c2) -> ["[1"++"]1"] -- \ (Z:.():.()) -> ["",""]
  , pair2 = \ (Z:.c1:.c2) -> ["[2"++"]2"] -- \ (Z:.():.()) -> ["",""]
  , h     = SM.toList
}
{-# INLINE pretty #-}

randgPairMax :: Int -> String -> (Int, [[String]])
randgPairMax k inp =
  (d, take k bs) where
   i = VU.fromList . Prelude.map toUpper $ inp
   n = VU.length i
   !(Z:.t:.u:.v) = runInsideForward i
   d = unId $ axiom u -- Start Symbol
   bs = runInsideBacktrack i (Z:.t:.u:.v)
{-# NOINLINE randgPairMax #-}


type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int


runInsideForward :: VU.Vector Char -> Z:.T:.X:.T
runInsideForward i =
  mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gRandG bpmax
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (chr i)
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

type X' = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type T' = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]

runInsideBacktrack :: VU.Vector Char -> Z:.T:.X:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v) =
  -- error "Not Implemented"
  unId $ axiom b -- StartSymbol
  where !(Z:._:.b:._) = gRandG (bpmax <|| pretty)
                          (toBacktrack t (undefined :: Id a -> Id a))
                          (toBacktrack u (undefined :: Id a -> Id a))
                          (toBacktrack v (undefined :: Id a -> Id a))
                          (chr i)
                          (chr i)
                          :: Z:.T':.X':.T'
{-# NoInline runInsideBacktrack #-}
