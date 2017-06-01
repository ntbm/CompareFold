-- Reidy and Nebel Pseudoknot Grammar Class
module BioInf.CompareFold.RandN where

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

Grammar: RandN
N: S
N: <T,2>
N: <U,2>
N: <V,2>
N: <W,2>
T: c
S: S
S -> unp <<< c S
S -> nil <<< e
S -> jux <<< c S c S
S -> pse <<< T U T U
S -> pse1 <<< T U T V U V
S -> pse2 <<< T U V T U V
S -> pse3 <<< T U V T W U V W
<U,U> -> dum <<< <T,T>
<V,V> -> dum2 <<< <T,T>
<W,W> -> dum3 <<< <T,T>
<T,T> -> nest <<< [-,c] [-,S] <T,T> [c,-] [S,-]
<T,T> -> jux2 <<< [c,-] [S,-] [-,c] [-,S]

//
Emit: RandN
|]
makeAlgebraProduct ''SigRandN

bpmax :: Monad m => SigRandN m Int Int Char Char
bpmax = SigRandN
  { unp   = \ c x                   -> x
  , nil   = \ ()                    -> 0
  , jux   = \ c x d y               -> if c `pairs` d then x + y + 1 else -999999
  , pse1    = \ () () t () u v     -> t + u + v
  , pse2   = \ () () () t u v     -> t + u + v
  , pse3   = \ () () () t () u v w     -> t + u + v + w
  , pse   = \ () () t u     -> t + u
  , dum   = \ y -> y
  , dum2   = \ y -> y
  , dum3   = \ y -> y
  , nest  = \ (Z:.():.a) (Z:.():.s1) t (Z:.b:.()) (Z:.s2:.()) -> if a `pairs` b then s1 + s2 + t + 1 else -888888
  , jux2  = \ (Z:.a:.()) (Z:.s1:.())   (Z:.():.b) (Z:.():.s2) -> if a `pairs` b then s1 + s2 + 1 else -777777
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

pretty :: Monad m => SigRandN m [String] [[String]] Char Char
pretty = SigRandN
  { unp   = \ c [x] -> ["." ++ x]
  , jux   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , pse   = \ () () [t1,t2] [u1,u2] -> [t1 ++ u1 ++ t2 ++ u2]
  , pse2   = \ () () () [t1,t2] [u1,u2] [v1,v2] -> [t1 ++ u1 ++ v1 ++ t2 ++ u2 ++ v2]
  , pse1   = \ () () [t1,t2] () [u1,u2] [v1,v2] -> [t1 ++ u1 ++ t2 ++ v1 ++ u2 ++ v2]
  , pse3   = \ () () () [t1,t2] () [u1,u2] [v1,v2] [w1,w2] -> [t1 ++ u1 ++ v1 ++ t2 ++ w1 ++ u2 ++ v2 ++ w2]
  , nil   = \ () -> [""]
  , dum   = \ [t1,t2] -> [t1, t2]
  , dum2   = \ [t1,t2] -> [t1, t2]
  , dum3   = \ [t1,t2] -> [t1, t2]
  , nest  = \ (Z:.():.a) (Z:.():.[s1]) [t1,t2] (Z:.b:.()) (Z:.[s2]:.()) ->  [ t1 ++ "{" ++ s1, "}" ++ s2 ++ t2]
  , jux2  = \ (Z:.a:.()) (Z:.[s1]:.()) (Z:.():.b) (Z:.():.[s2]) -> [ "(" ++ s1 , ")" ++ s1]
  , h     = SM.toList
}
{-# INLINE pretty #-}

randNPairMax :: Int -> String -> (Int, [[String]])
randNPairMax k inp =
  (d, take k bs) where
   i = VU.fromList . Prelude.map toUpper $ inp
   n = VU.length i
   !(Z:.t:.u:.v:.w:.x) = runInsideForward i
   d = unId $ axiom t -- Start Symbol
   bs = runInsideBacktrack i (Z:.t:.u:.v:.w:.x)
{-# NOINLINE randNPairMax #-}


type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int


runInsideForward :: VU.Vector Char -> Z:.X:.T:.T:.T:.T
runInsideForward i =
  mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gRandN bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (chr i)
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

type X' = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type T' = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]

runInsideBacktrack :: VU.Vector Char -> Z:.X:.T:.T:.T:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v:.w:.x) =
  -- error "Not Implemented"
  unId $ axiom b -- StartSymbol
  where !(Z:.b:._:._:._:._) = gRandN (bpmax <|| pretty)
                          (toBacktrack t (undefined :: Id a -> Id a))
                          (toBacktrack u (undefined :: Id a -> Id a))
                          (toBacktrack v (undefined :: Id a -> Id a))
                          (toBacktrack w (undefined :: Id a -> Id a))
                          (toBacktrack x (undefined :: Id a -> Id a))
                          (chr i)
                          (chr i)
                          :: Z:.X':.T':.T':.T':.T'
{-# NoInline runInsideBacktrack #-}
