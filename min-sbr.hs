module MIN_SBR where


import Data.List ((\\),elemIndex)
import Data.Maybe (fromJust)
import Test.QuickCheck

import Data.Foldable (find)
import Data.Maybe (isJust)
import Control.Monad (join)

firstJust = join . find isJust


type Element = Int
newtype Permutation = Permutation [Element] deriving (Show, Eq)

-- Reversal leftRedEdge rightRedEdge blueEdge
data Reversal = Reversal (Element,Element) (Element,Element) (Element,Element) deriving (Show, Eq)

-- BreakpointGraph vertices redEdges blueEdges
type BreakpointGraphEdge = (Element,Element)
data BreakpointGraph = BreakpointGraph [Element] [BreakpointGraphEdge] [BreakpointGraphEdge] deriving (Show, Eq)
data CycleDecomposition = CycleDecomposition [[BreakpointGraphEdge]] deriving (Show, Eq)

-- ReversalGraph vertices edges
type ReversalGraphEdge = (BreakpointGraphEdge,BreakpointGraphEdge)
data ReversalGraph = ReversalGraph [BreakpointGraphEdge] [ReversalGraphEdge] deriving (Show, Eq)

sorted :: (Element,Element) -> (Element,Element)
sorted (a,b)
  | a <= b    = (a,b)
  | otherwise = (b,a)

isId :: Permutation -> Bool
isId (Permutation xs) = xs == [0..(length xs) - 1]

isIdR :: ReversalGraph -> Bool
isIdR (ReversalGraph _ xs) = null xs

isAdjacency :: Element -> Element -> Bool
isAdjacency x y = abs (x - y) == 1

isBreakpoint :: Element -> Element -> Bool
isBreakpoint x y = not (isAdjacency x y)

neighbors :: [Element] -> [(Element,Element)]
neighbors xs = map (\x -> (x,x+1)) [0..(length xs) - 2]

breakpoints :: [Element] -> [(Element,Element)]
breakpoints [x] = []
breakpoints (x:y:zs)
  | isBreakpoint x y = sorted (x,y) : breakpoints (y:zs)
  | otherwise        = breakpoints (y:zs)

adjacencies :: [Element] -> [(Element,Element)]
adjacencies [x] = []
adjacencies (x:y:zs)
  | isAdjacency x y = sorted (x,y) : adjacencies (y:zs)
  | otherwise       = adjacencies (y:zs)

missingAdjacencies :: [Element] -> [(Element,Element)]
missingAdjacencies xs = (neighbors xs) \\ (adjacencies xs)

buildBreakpointGraph :: Permutation -> BreakpointGraph
buildBreakpointGraph (Permutation elements) =
  let redEdges  = breakpoints elements
      blueEdges = missingAdjacencies elements
  in BreakpointGraph elements redEdges blueEdges

pos :: [Element] -> Element -> Int
pos elements x = fromJust $ x `elemIndex` elements

incidentEdges :: CycleDecomposition -> (Element,Element) -> Maybe ((Element,Element),(Element,Element))
incidentEdges (CycleDecomposition []) e = Nothing
incidentEdges (CycleDecomposition (cycle:cycles)) e =
  case e `elemIndex` cycle of
    Nothing -> incidentEdges (CycleDecomposition cycles) e
    Just i  ->
      if i == 0 then
        Just (last cycle, cycle !! (i + 1))
      else if i == (length cycle) - 1 then
        Just (cycle !! (i - 1), head cycle)
      else
        Just (cycle !! (i - 1), cycle !! (i + 1))


incidentEdge :: Bool -> CycleDecomposition -> [Element] -> (Element,Element) -> (Element,Element)
incidentEdge isLeft cd elements (a,b) = aux $ firstJust [incidentEdges cd (a,b), incidentEdges cd (b,a)]
  where
    aux Nothing = error $ "edge " ++ show (a,b) ++ " missing from cycle decomposition!"
    aux (Just (c@(x,_),d@(y,_)))
      | pos elements x < pos elements y = if isLeft then c else d
      | otherwise                       = if isLeft then d else c

buildReversalGraph :: BreakpointGraph -> CycleDecomposition -> ReversalGraph
buildReversalGraph (BreakpointGraph elements redEdges blueEdges) c =
  let vertices = neighbors elements
      edges    = buildEdges vertices
  in ReversalGraph vertices edges
    where
      buildEdges xs = aux xs xs
        where
          aux [] _ = []
          aux (y:ys) [] = aux ys xs
          aux (y:ys) (z:zs)
            | y <= z && (sorted y) `elem` missingAdjacencies elements && (sorted z) `elem` missingAdjacencies elements && hasEdge y z = (y,z) : aux (y:ys) zs
            | otherwise             = aux (y:ys) zs
      hasEdge x y = isStrictlyLess [lb x, lb y, rb x, rb y] || isStrictlyLess [lb y, lb x, rb y, rb x] || isStrictlyLess [lr x, lr y, rr x, rr y] || isStrictlyLess [lr y, lr x, rr y, rr x]
      isStrictlyLess [x] = True
      isStrictlyLess (x:y:zs) = x < y && isStrictlyLess (y:zs)
      lb (x,y) = min (pos elements x) (pos elements y)
      rb (y,x) = max (pos elements x) (pos elements y)
      lr x = let (y,z) = incidentEdge True c elements x in min (pos elements y) (pos elements z)
      rr x = let (y,z) = incidentEdge False c elements x in min (pos elements y) (pos elements z)

-- builds reversal from blue edge of breakpoint graph given cycle decomposition
buildReversal :: BreakpointGraph -> CycleDecomposition -> (Element,Element) -> Reversal
buildReversal (BreakpointGraph elements redEdges blueEdges) c u = Reversal (incidentEdge True c elements u) (incidentEdge False c elements u) u

applyBlueNode :: ReversalGraph -> (Element,Element) -> ReversalGraph
applyBlueNode (ReversalGraph vertices edges) u =
  let adjacentVertices     = filter (\v -> (sorted u,v) `elem` edges || (v,sorted u) `elem` edges) vertices
      adjacentVerticePairs = buildAdjacentVerticePairs adjacentVertices
      edges'               = (adjacentVerticePairs \\ edges) ++ (edges \\ adjacentVerticePairs)
  in ReversalGraph vertices edges'
    where
      buildAdjacentVerticePairs vs = [(x,y) | x <- vs, y <- vs, x < y]

applyRedNode :: ReversalGraph -> (Element,Element) -> ReversalGraph
applyRedNode r u = turnIntoIsolatedVertex (applyBlueNode r u)
  where
    turnIntoIsolatedVertex (ReversalGraph vertices edges) =
      let edges' = filter (\(v,w) -> v /= sorted u && w /= sorted u) edges
      in ReversalGraph vertices edges'

applyReversal :: Permutation -> Reversal -> Permutation
applyReversal (Permutation xs) (Reversal (a,b) (c,d) _) =
  let (ls,ys) = span (/=b) xs
      (ms,rs) = span (/=d) ys
  in Permutation $ ls ++ reverse ms ++ rs

applyReversalToCycleDecomposition :: CycleDecomposition -> Reversal -> CycleDecomposition
applyReversalToCycleDecomposition (CycleDecomposition cycles) (Reversal (a,b) (c,d) (e,f)) =
  CycleDecomposition $ map updateCycle cycles
    where
      updateCycle [] = []
      updateCycle (x:xs)
        | (a,b) == x = edge : updateCycle xs
        | (c,d) == x = updateCycle xs
        | (e,f) == x = updateCycle xs
        | otherwise  = x : updateCycle xs
      edge =
        let l = if a == e || a == f then b else a
            r = if c == e || c == f then d else c
        in (l,r)

test :: IO ()
test = do
  putStr "permutation> "
  inp <- getLine
  let p = Permutation $ read inp
      g = buildBreakpointGraph p
  putStrLn $ "p = " ++ show p
  putStrLn $ "g = " ++ show g
  putStr "cycle decomposition> "
  inp <- getLine
  let c = CycleDecomposition $ read inp
      r = buildReversalGraph g c
  putStrLn $ "c = " ++ show c
  putStrLn $ "r = " ++ show r
  putStr "u (must be red)> "
  inp <- getLine
  let u = read inp
      rev = buildReversal g c u
      p' = applyReversal p rev
      g' = buildBreakpointGraph p'
      c' = applyReversalToCycleDecomposition c rev
      r' = buildReversalGraph g' c'
      r'' = applyRedNode r u
  putStrLn $ "u = " ++ show u
  putStrLn $ "rev = " ++ show rev
  putStrLn $ "p' = " ++ show p'
  putStrLn $ "g' = " ++ show g'
  putStrLn $ "c' = " ++ show c'
  putStrLn $ "r' = " ++ show r'
  putStrLn $ "r'' = " ++ show r''


main :: IO Integer
main = do
  putStr "permutation> "
  inp <- getLine
  let p = Permutation $ read inp
      g = buildBreakpointGraph p
  putStrLn $ "p = " ++ show p
  putStrLn $ "g = " ++ show g
  putStr "cycle decomposition> "
  inp <- getLine
  let c = CycleDecomposition $ read inp
      r = buildReversalGraph g c
  putStrLn $ "c = " ++ show c
  putStrLn $ "r = " ++ show r
  aux 1 r
    where
      aux :: Integer -> ReversalGraph -> IO Integer
      aux cnt r = do
        putStr $ "[" ++ show cnt ++ "] u (must be red)> "
        inp <- getLine
        let u = read inp
            r' = applyRedNode r u
        putStrLn $ "u = " ++ show u
        putStrLn $ "r' = " ++ show r'
        if isIdR r' then
          return cnt
        else
          aux (cnt+1) r'
