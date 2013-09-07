import Prelude ()
import PreludePlus
import qualified Control.Monad.Random as Rand
import Control.Monad (replicateM)
import Control.Concurrent (threadDelay)
import qualified System.IO as IO
import qualified Data.Map as Map
import Data.List (sortBy)
import Data.Ord (comparing, Down(Down))
import System.Environment (getArgs)
import Text.Parsec as P

data Term
    = S | K | I | B | C
    | Term :$ Term
    | Var Char
    deriving (Eq, Ord)

showTerm :: Bool -> Term -> String
showTerm ap (a :$ b)
    | ap = "(" ++ t ++ ")"
    | otherwise = t
    where
    t = showTerm False a ++ showTerm True b
showTerm _ S = "S"
showTerm _ K = "K"
showTerm _ I = "I"
showTerm _ B = "B"
showTerm _ C = "C"
showTerm _ (Var c) = [c]

instance Show Term where
    show = showTerm False

type Parser = P.Parsec String ()

termParser :: Parser Term
termParser = foldl1 (:$) <$> P.many1 atom
    where
    atom = P.choice [
        P.char 'S' *> pure S,
        P.char 'K' *> pure K,
        P.char 'I' *> pure I,
        P.char 'B' *> pure B,
        P.char 'C' *> pure C,
        P.char '(' *> termParser <* P.char ')',
        Var <$> P.oneOf ['a'..'z']
      ]

parseTerm :: String -> Either P.ParseError Term
parseTerm = P.parse (termParser <* P.eof) "<input>"


colorize :: String -> String
colorize = concatMap colorize1
    where
    colorize1 'S' = "\o33[31mS\o33[0m"
    colorize1 'K' = "\o33[32mK\o33[0m"
    colorize1 'I' = "\o33[33mI\o33[0m"
    colorize1 'B' = "\o33[34mB\o33[0m"
    colorize1 'C' = "\o33[35mC\o33[0m"
    colorize1 x = [x]

size :: Term -> Int
size = length . show

infixl 9 :$

eval1 :: Term -> Maybe Term
eval1 (I :$ x) = Just x
eval1 (K :$ x :$ y) = Just x
eval1 (S :$ x :$ y :$ z) = Just (x :$ z :$ (y :$ z))
eval1 (B :$ x :$ y :$ z) = Just (x :$ (y :$ z))
eval1 (C :$ x :$ y :$ z) = Just (x :$ z :$ y)
eval1 (a :$ b) = 
    case eval1 a of
        Just a' -> Just (a' :$ b)
        _ -> (a :$) <$> eval1 b
eval1 _ = Nothing



type Pool = [Term]
type Cloud = Rand.Rand Rand.StdGen

select :: [a] -> Cloud a
select xs = Rand.fromList [ (x, l') | x <- xs ]
    where
    l' = 1 / fromIntegral (length xs)

delete :: Int -> [a] -> [a]
delete n xs = take n xs ++ drop (n+1) xs


termSize, poolSize :: Int
termSize = 100
poolSize = 38

evo1 :: [Term] -> Cloud [Term]
evo1 pool = do
    action <- if length pool < poolSize then select [ birth, fuck, eval ] else return eval
    action
    where
    birth = do
        e <- select [ S, K, I, B, C ]
        return (e : pool)
    fuck = do
        x1 <- select pool
        x2 <- select pool
        let term = x1 :$ x2
        if size term <= termSize then
            return ((x1 :$ x2):pool)
        else
            return pool
    eval = do
        ix <- select [0..length pool-1]
        let term = pool !! ix
        case eval1 term of
                Nothing -> return (delete ix pool)
                Just term' 
                    | size term' <= termSize -> return (take ix pool ++ [term'] ++ drop (ix+1) pool)
                    | otherwise -> return (delete ix pool)

initialPool :: Int -> Cloud [Term]
initialPool n = replicateM n (select [S,K,I,B,C])

countSubterms :: Term -> Map.Map Term Int -> Map.Map Term Int
countSubterms t = Map.insertWith (+) t 1 . go t
    where
    go (a :$ b) = countSubterms a . countSubterms b
    go _ = id


popularTerms :: [Term] -> [(Term,Integer)]
popularTerms = sortBy (comparing (Down . snd))
             . map (\(t,pop) -> (t, fromIntegral pop * fromIntegral (size t)))
             . Map.toList 
             . foldr countSubterms Map.empty 
    where

printLn :: (Show a) => a -> IO ()
printLn x = print x >> putStrLn ""

main = do
    args <- getArgs
    case args of
        [] -> runSim
        [t] -> case parseTerm t of
                   Left err -> fail . show $ err
                   Right t' -> traceEval t'

traceEval :: Term -> IO ()
traceEval term = do
    putStrLn . colorize . show $ term
    case eval1 term of
        Just term' -> traceEval term'
        Nothing    -> return ()

runSim = do
    IO.hSetBuffering IO.stdout IO.LineBuffering
    pool <- Rand.evalRandIO (initialPool poolSize)
    go pool
    where
    go pool = do
        putStrLn "\o33[2J"
        mapM_ (putStrLn . colorize . show) pool
        putStrLn "----------------- POPULAR --------------------"
        mapM_ (putStrLn . colorize . show . fst) (take 5 (popularTerms pool))
        putStrLn "=============================================="
        threadDelay 100000
        go =<< Rand.evalRandIO (evo1 pool)
