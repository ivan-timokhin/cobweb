import Data.Either (partitionEithers)
import Data.Functor.Identity (Identity(Identity, runIdentity))
import Data.List (foldl', group, groupBy, intercalate, partition)
import Test.QuickCheck.Modifiers
       (NonEmptyList(NonEmpty), Positive(Positive))
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)

import qualified Cobweb as W
import qualified Cobweb.Fold as WF
import qualified Cobweb.Group as WG
import qualified Cobweb.Link as WL
import qualified Cobweb.Zip as WZ

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [folds, groups, pipes, zips, unzips]

folds :: TestTree
folds =
  testGroup
    "Fold"
    [ testProperty "toListN_ . each" $ \lst ->
        runIdentity (WF.toListN_ $ W.each (lst :: [Int])) == lst
    , testProperty "toListM" $ \lst ->
        runIdentity
          (WF.foldMNode_
             (\diff a -> Identity (diff . (a :)))
             (Identity id)
             (Identity . ($ [])) $
           W.each (lst :: [Int])) ==
        lst
    , testProperty "sum" $ \lst ->
        runIdentity (WF.foldNode_ (+) 0 id $ W.each (lst :: [Int])) ==
        foldl' (+) 0 lst
    , testProperty "scan" $ \lst n ->
        runIdentity
          (WF.toListN_ $ WF.scanOn W.i0 (+) n (+ 3) $ W.each (lst :: [Int])) ==
        map (+ 3) (scanl (+) n lst)
    , testProperty "scanM" $ \lst n ->
        runIdentity
          (WF.toListN_ $
           WF.scanOnM
             W.i0
             (\a b -> Identity (a + b))
             (Identity n)
             (Identity . show) $
           W.each (lst :: [Int])) ==
        map show (scanl (+) n lst)
    ]

groups :: TestTree
groups =
  testGroup
    "Group"
    [ testProperty "group" $ \lst ->
        runIdentity
          (WF.toListN_ $
           WG.foldChunks WF.toListN $ WG.group $ W.each (lst :: [Bool])) ==
        group lst
      -- This one is technically illegal, but I'll enforce consistency
      -- either way
    , testProperty "groupBy (<)" $ \lst ->
        runIdentity
          (WF.toListN_ $
           WG.foldChunks WF.toListN $ WG.groupBy (<) $ W.each (lst :: [Int])) ==
        groupBy (<) lst
    , testProperty "intercalate" $ \lst sep ->
        runIdentity
          (WF.toListN_ $ WG.intercalate (W.each sep) $ WG.group $ W.each lst) ==
        (intercalate sep (group lst) :: [Bool])
    , testProperty "concat" $ \lst ->
        runIdentity (WF.toListN_ $ WG.concat $ WG.chunkBy 2 $ W.each lst) ==
        (lst :: [Int])
    , testProperty "chunkBy lengths" $ \(Positive n) (NonEmpty lst) ->
        all ((== n) . length) $
        init $
        runIdentity $
        WF.toListN_ $
        WG.foldChunks WF.toListN $ WG.chunkBy n $ W.each (lst :: [()])
    ]

pipes :: TestTree
pipes =
  testGroup
    "Pipe"
    [ testProperty "cat" $ \lst ->
        runIdentity (WF.toListN_ $ W.each (lst :: [Int]) W.>-> W.cat) == lst
    , testProperty "mapping" $ \lst ->
        runIdentity (WF.toListN_ $ W.each (lst :: [Int]) W.>-> W.mapping (+ 10)) ==
        map (+ 10) lst
    , testProperty "taking" $ \n lst ->
        runIdentity (WF.toListN_ $ W.each (lst :: [Int]) W.>-> W.taking n) ==
        take n lst
    , testProperty "dropping" $ \n lst ->
        runIdentity (WF.toListN_ $ W.each (lst :: [Int]) W.>-> W.dropping n) ==
        drop n lst
    ]

zips :: TestTree
zips =
  testGroup
    "Zip"
    [ testProperty "zipping" $ \lst1 lst2 ->
        runIdentity
          (WF.toListN_ $
           WL.linkOn
             W.i0
             W.i0
             (W.each lst1)
             (WL.linkOn W.i0 W.i1 (W.each lst2) W.zipping)) ==
        (zip lst1 lst2 :: [(Char, Int)])
    , testProperty "zipping3" $ \lst1 lst2 lst3 ->
        runIdentity
          (WF.toListN_ $
           WL.linkOn
             W.i0
             W.i0
             (W.each lst1)
             (WL.linkOn
                W.i0
                W.i1
                (W.each lst2)
                (WL.linkOn W.i0 W.i2 (W.each lst3) W.zipping3))) ==
        (zip3 lst1 lst2 lst3 :: [(Char, Int, Bool)])
    , testProperty "zips" $ \lst1 lst2 ->
        runIdentity
          (WF.toListN_ $
           WZ.zipsWith
             (\(a, x) (b, y) -> ((a, b), (x, y)))
             W.i0
             W.i0
             (W.each lst1)
             (W.each lst2)) ==
        (zip lst1 lst2 :: [(Char, Int)])
    ]

unzips :: TestTree
unzips =
  testGroup
    "Unzip"
    [ testProperty "unzipping" $ \lst ->
        runIdentity
          (WF.toListN $
           WF.foldOn_ W.i1 (\diff a -> diff . (a :)) id ($ []) $
           W.each lst W.>-> W.unzipping) ==
        (unzip lst :: (String, [Int]))
    , testProperty "unzipping3" $ \lst ->
        runIdentity
          (WF.toListN $
           WF.foldOn W.i1 (\diff a -> diff . (a :)) id ($ []) $
           WF.foldOn_ W.i2 (\diff a -> diff . (a :)) id ($ []) $
           W.each lst W.>-> W.unzipping3) ==
        let (l1, l2, l3) = (unzip3 lst :: (String, [Int], [Bool]))
        in (l1, (l2, l3))
    , testProperty "partitioning" $ \lst ->
        runIdentity
          (WF.toListN $
           WF.foldOn_ W.i1 (\diff a -> diff . (a :)) id ($ []) $
           W.each lst W.>-> W.partitioning (> 0)) ==
        (partition (> 0) lst :: ([Int], [Int]))
    , testProperty "partitioningEither" $ \lst ->
        runIdentity
          (WF.toListN $
           WF.foldOn_ W.i1 (\diff a -> diff . (a :)) id ($ []) $
           W.each lst W.>-> W.partitioningEither) ==
        (partitionEithers lst :: ([Bool], [Int]))
    ]
