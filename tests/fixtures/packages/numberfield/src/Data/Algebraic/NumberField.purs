module Data.Algebraic.NumberField
    (module Data.Algebraic.NumberField) where
        
import Prelude

import Data.Array 
  ( init
  , last
  , (..)
  , (:)
  , uncons
  , zipWith
  , concat
  , zip
  , scanl
  , filter
  , length
  , any
  , all
  , reverse
  , elem
  , elemIndex
  , (!!)
  , difference
  , sort
  , group
  , groupBy
  , sortBy
  , replicate
  )
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty (toArray) as NonEmpty
import Data.Int (even)
import Data.Foldable (class Foldable, foldr, product, sum, maximum)
import Data.Group (class Group, power)
import Data.Maybe (Maybe (..), fromMaybe)
import Data.Map (fromFoldable, lookup)
import Data.Ord (abs)
import Data.Ratio (Ratio)
import Data.Reflectable 
  ( class Reflectable
  , class Reifiable
  , reflectType
  )
import Data.Set (map, filter, fromFoldable) as Set
import Data.Set (Set, insert, empty, toUnfoldable, unions, size, singleton, member, findMin, toggle)
import Data.Hashable (class Hashable, hash)
import Data.Int (pow) as Int
import Data.Sparse.Matrix 
    ( Matrix (..)
    , height
    , ringDeterminant
    )
import Data.Sparse.Polynomial 
    ( class Arity
    , class Axed
    , class Divisible
    , class Full
    , class GoSwap
    , class IntLiftable
    , class Leadable
    , class Nest
    , class Pad
    , class Peel
    , class Set
    , class Unpad
    , Polynomial
    , (^)
    , (!)
    , (:.)
    , arity'
    , axes
    , diff
    , divisors
    , dominantMonom
    , fill
    , _fill
    , full
    , goSwap
    , nest
    , _nest
    , _pad
    , pow
    , prevAxis
    , set
    , _set
    , _unpad
    )
import Data.Traversable (sequence)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested ((/\), type (/\))
import Prim.Int (class Add)
import Type.Proxy (Proxy (..))

-- | Builds the https://en.wikipedia.org/wiki/Sylvester_matrix
-- | of two univariate polynomials with coefficients in a commutative ring
sylvester :: forall a. 
  CommutativeRing a => 
  Divisible a => 
  Eq a =>  
  Leadable a => 
  Polynomial a -> Polynomial a -> Matrix a
sylvester p p' =
  let d = degree p
      d' = degree p'
      q = p^0
      q' = p'^0
      dim = d + d'
  in 
    Matrix 
      { height: dim
      , width: dim
      , coefficients:
        foldr 
          (\n acc -> acc + q * pow (one^1^1) n) 
          zero 
          (0..(d'-1)) +
        foldr 
          (\n acc -> acc + q' * pow (one^0^1) (d'+n) * pow (one^1^0) n) 
          zero 
          (0..(d-1))
      }

-- | Builds the minimal polynomial whose root(s)
-- | is (are) the sum of the roots of each of
-- | the polynomials listed in the array
extensionBySum :: forall a. 
  CommutativeRing a =>
    Divisible a => 
    Eq a => 
    Leadable a => 
    Ord a =>
    Ring a => 
    Array (Polynomial a) -> Polynomial a

extensionBySum arr = 
  let extensionBySum2 p1 p2 =
        let up = nest @1
        in ringDeterminant $ 
          sylvester (up p1) ((one^1^0 - one^0^1) `fill @0` (up p2))
      extensionBySums ps = 
        case uncons ps of
            Just { head: h1, tail } ->
                case uncons tail of
                     Just { head: h2, tail: ts } -> 
                        extensionBySums (extensionBySum2 h1 h2 : ts)
                     _ -> h1
            _ -> zero
    in extensionBySums arr

-- | Computes the reciprocal of the second polynomial
-- | with the help of the previously computed 
-- | https://en.wikipedia.org/wiki/Resultant between
-- | that polynomial and the minimal polynomial 
-- | of the extension
cayley :: forall a.
  Divisible a => 
  Eq a => 
  EuclideanRing a => 
  Leadable a => 
  Peel a a => 
  Polynomial a -> Polynomial a -> Polynomial a

cayley r qa =
  let r0 = (r ! 0) ^ 0
  in - (qa `fill @0` ((r - r0) / (one ^ 1))) / r0

-- | Computes the reciprocal of the first polynomial
-- | in the extension whose minimal polynomial 
-- | is provided by the second polynomial
reciprocal ::  forall n n1 n2 a r. 
  Add n2 1 n1 => 
  Add n1 1 n => 
  Arity a n => 
  Divisible r => 
  Eq r => 
  EuclideanRing r => 
  Leadable r => 
  Ord r =>
  Pad n2 (Polynomial r) a => 
  Peel r r => 
  Unpad n2 (Polynomial r) a => 
  a -> a -> a
  
reciprocal _m _mu =
  let m' = arity' _m
      m = _unpad (prevAxis $ prevAxis m') _m
      mu = _unpad (prevAxis $ prevAxis m') _mu
      up = nest @1
  in _pad (prevAxis $ prevAxis m') $ 
    cayley (ringDeterminant (sylvester (up mu) (one^1^0 - up m))) m

newtype Framework a = Framework
  { primitiveExpressions :: Array (Polynomial a)
  , minimal :: Polynomial a
  , primitiveSubstitution :: Polynomial a -> Polynomial a
  , lift :: a -> Polynomial a
  , unlift :: Polynomial a -> a
  , rawModuli :: Array (Polynomial a)
  , value :: a
  }
  
-- | Computes the required quantities needed to 
-- | perform computations with algebraic extensions 
-- | in the field of rational numbers
framework :: forall r a n1 n2 n3. 
  Add n3 1 n2 =>
  Add n2 1 n1 =>
  Arity (Polynomial (Polynomial a)) n1 => 
  Axed a r => 
  CommutativeRing a =>
  CommutativeRing r =>
  Divisible a => 
  Divisible r =>
  DivisionRing r =>
  Full n2 (Polynomial a) => 
  GoSwap 0 n1 (Polynomial a) =>
  Leadable a => 
  Leadable r  =>
  Nest n2 (Polynomial a) =>
  Ord a => 
  Ord r =>
  Pad n3 (Polynomial r) (Polynomial (Polynomial a)) =>
  Pad n2 (Polynomial r) (Polynomial (Polynomial (Polynomial a))) =>
  Peel a r => 
  Set n2 r (Polynomial a) =>
  Unpad n3 (Polynomial r) (Polynomial (Polynomial a)) =>
  Polynomial a -> Array (Polynomial r) -> Framework (Polynomial a)
    
framework uno arr =
  let _ /\ axs' = axes (uno^0)
      axs = fromMaybe [] $ init axs'
      var = fromMaybe (uno^0) $ last axs'
      var' = arity' var
      ready = (goSwap (Proxy :: _ 0) var' <<< _pad (prevAxis var')) <$> arr
      ms = zipWith (:.) ready axs
      ds = degree <$> ready
      d = product $ ds
      s = sum axs
      powers = (\n -> pow s n) <$> 0..(d-1)
      coefs = 
        zip 
          ((\p -> foldr (\m acc -> acc `mod` m) p ms) <$> powers) 
          (0..(d-1))
      scale = fromFoldable $ zip axs $ scanl (*) 1 (1:ds)
      convert (pol /\ x) = 
        let new = (\axe -> pow var (fromMaybe 0 $ lookup axe scale)) <$> axs
        in (_ ^ x) $ _unpad (prevAxis $ prevAxis var') $ 
            new `full` pol
      
      base =
        recip $ 
          Matrix 
            { height: d
            , width: d
            , coefficients: sum (convert <$> coefs) 
            }

      primitiveExpressions = (\ icol -> 
          let Matrix column = 
                base * 
                  Matrix
                    { height: height base
                    , width: 1
                    , coefficients: one^icol^0
                    }
          in _pad (prevAxis $ prevAxis var') $ 
              zero `set @0` column.coefficients ) <$> 
                (fromMaybe [] $ init $ scanl (*) 1 (1:ds))

      minimal = _pad (prevAxis $ prevAxis var') $ extensionBySum arr
      primitiveSubstitution = _fill (prevAxis var') s
      lift = _nest (prevAxis var')
      unlift = _set (prevAxis var') zero
      rawModuli = ms
      value = zero
        
  in Framework
    { primitiveExpressions
    , minimal
    , primitiveSubstitution
    , lift
    , unlift
    , rawModuli
    , value
    }

instance Reifiable (Framework (Polynomial (Ratio a)))
else instance 
  ( Reifiable (Framework a)
  ) => Reifiable (Framework (Polynomial a))

run :: forall a. Framework (Polynomial a) -> Polynomial a
run (Framework a) = a.value

newtype Extension :: forall k. k -> Type -> Type
newtype Extension f a = Extension a

element :: forall f a. 
  Eq a => Semiring a => a -> Extension f (Framework a)
element v = Extension $ Framework
    { primitiveExpressions: []
    , minimal: zero
    , primitiveSubstitution: identity
    , lift: (_ ^ 0)
    , unlift: (_ ! 0)
    , rawModuli: []
    , value: v
    }
    
build :: forall proxy a f. (proxy -> Extension f a) -> proxy -> a
build x = (\ (Extension a) -> a) <<< x

minimalPolynomial :: forall a. Framework a -> Polynomial a
minimalPolynomial (Framework f) = f.minimal

toPrimitive :: forall a. Framework a -> Array (Polynomial a)
toPrimitive (Framework f) = f.primitiveExpressions

type Expression :: forall k. k -> Type -> Type
type Expression f a = Reflectable f (Framework a) =>
  Proxy f -> Extension (Proxy f) (Framework a)

normalize :: forall f a n n1.
  Add n1 1 n =>
  Arity (Polynomial (Polynomial a)) n =>
  Divisible a =>
  Eq a =>
  EuclideanRing a =>
  Full n1 (Polynomial a) =>
  Leadable a =>
  Reflectable f (Framework (Polynomial a)) =>
  Polynomial a -> Extension (Proxy f) (Framework (Polynomial a))
normalize a = 
  Extension
    ( let Framework fw = reflectType (Proxy :: _ f)
      in 
        Framework fw 
          { value = 
            fw.unlift $ foldr (\m acc -> acc `mod` m) 
              (fw.primitiveSubstitution $ 
              (fw.primitiveExpressions `full` fw.lift a) 
                `mod` fw.minimal
                )  fw.rawModuli
          }
    )

instance
  ( Add n1 1 n
  , Arity (Polynomial (Polynomial a)) n
  , Divisible a
  , Eq a
  , EuclideanRing a
  , Full n1 (Polynomial a)
  , Leadable a
  , Reflectable f (Framework (Polynomial a))
  ) => Semiring (Extension (Proxy f) (Framework (Polynomial a))) where
  add (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value + b.value)
  mul (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value * b.value)
  one = normalize one
  zero = normalize zero

instance 
  ( Add n1 1 n
  , Arity (Polynomial (Polynomial a)) n
  , Divisible a
  , Eq a
  , EuclideanRing a
  , Full n1 (Polynomial a)
  , Leadable a
  , Reflectable f (Framework (Polynomial a))
  ) => Ring (Extension (Proxy f) (Framework (Polynomial a))) where
  sub (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value - b.value)

instance 
  ( Add n 1 m1
  , Add m1 1 m
  , Arity (Polynomial (Polynomial a)) m 
  , Divisible a
  , Divisible r
  , Eq a
  , Eq r
  , EuclideanRing a
  , EuclideanRing r
  , Full m1 (Polynomial a)
  , Leadable a
  , Leadable r
  , Ord r
  , Pad n (Polynomial r) (Polynomial (Polynomial a))
  , Peel r r
  , Reflectable f (Framework (Polynomial a))
  , Unpad n (Polynomial r) (Polynomial (Polynomial a))
  ) => DivisionRing (Extension (Proxy f) (Framework (Polynomial a))) where
  recip (Extension (Framework a)) = 
    Extension
    ( let Framework fw = reflectType (Proxy :: _ f)
      in 
        Framework fw 
          { value = 
              fw.unlift $ foldr (\m acc -> acc `mod` m) 
                (fw.primitiveSubstitution $ 
                  (reciprocal 
                      ((fw.primitiveExpressions `full` fw.lift a.value) 
                        `mod` fw.minimal)
                      fw.minimal
                  ) `mod` fw.minimal
                ) fw.rawModuli
          }
    )

-- | Discriminant of a univariate polynomial
discriminant :: forall a. 
  Eq a => 
  Semiring a => 
  Ring a => 
  EuclideanRing a => 
  Ord a => 
  Divisible a => 
  Leadable a => 
  IntLiftable a => 
  Polynomial a -> a

discriminant p =
  let n /\ an = dominantMonom p
      nn = (n * (n-1)) / 2
      sign = if even nn then one else negate one
  in sign * ringDeterminant (sylvester p $ diff p) / an

-- | Euler Totient Function
totient :: Int -> Int 
totient n = length $ filter ((_ == 1) <<< gcd n) $ 1..(n-1)

-- | `cyclotomic n` returns the (irreductible) 
-- | univariate minimal polynomial of degree `totient n`
-- | whose roots are all the `totient n` primitive roots of unity
cyclotomic ::  forall a. 
  Eq a => 
  Ring a => 
  Divisible a => 
  Leadable a => 
  CommutativeRing a => 
  Int -> Polynomial a
 
cyclotomic 1 = one ^ 1 - one ^ 0
cyclotomic n = 
    let ds = filter (\ d -> d > 0 && d < n) $ divisors n
    in (one ^ n - one ^ 0) / product (cyclotomic <$> ds)

newtype Cycle = Cycle (Array Int)

instance Show Cycle where
  show (Cycle xs) = "Cycle " <> show xs

-- | Circular permutation of a cycle
nextRepresentation :: Array Int -> Array Int
nextRepresentation xs =
  case uncons xs of
    Just { head, tail } -> tail <> [head]
    _ -> []
        
instance Eq Cycle where
  eq (Cycle a) (Cycle b) =
    length a == length b &&
      (any (_ == a) $ scanl (\ acc _ -> nextRepresentation acc) b $ 1..length a)

-- | Safe (defaulted) index
peek :: (Int -> Int) -> Int -> Array Int -> Int
peek f i xs =
  case xs !! (f i `mod` length xs) of
       Just x -> x
       _ -> -1

-- | Where does an element land after a cycle
destination :: Cycle -> Int -> Int
destination (Cycle a) x = 
  case elemIndex x a of
       Just n -> peek (_ + 1) n a
       _ -> x

{-
origin (Cycle a) x = 
  case elemIndex x a of
       Just n -> peek (_ - 1) n a
       _ -> x
-}

-- | Where do elements land after a cycle
cycle :: Cycle -> Array Int -> Array Int
cycle c xs =
  (\ n -> peek identity (destination c n) xs) <$> 0..(length xs - 1)
    
newtype Permutation = Product (Array Cycle)

instance Show Permutation where
  show (Product xs) = "Product " <> show xs

-- | Where do elements land after a permutation
permute :: Permutation -> Array Int -> Array Int
permute (Product cs) xs =
  foldr (\ c acc -> cycle c acc) xs cs

-- | Deduces the disjoint cycles between a base and one of its permutations
play :: Array Int -> Array Int -> Array Cycle
play base perm =
  let at = flip $ peek identity 
      go n i b path acc =
        case uncons b of
            Just { head, tail } ->
              if i == n
                     then go head (perm `at` head) tail [head] (Cycle path : acc)
                     else go n (perm `at` i)  (difference b [i]) (path <> [i]) acc
            _ -> Cycle path : acc
  in go 0 (perm `at` 0) (difference base [0]) [0] []
  
-- | Transforms a permutation into a product of disjoint cycles
abelize :: Permutation -> Permutation
abelize p@(Product cs) = 
  let hasContent = maximum (foldr (\(Cycle c) arr -> arr <> c ) [] cs) 
  in 
    case hasContent of
      Just n -> 
        let base = 0..n
            perm = permute p base
        in Product (play base perm)
      _ -> Product []
      
instance Semigroup Permutation where
  append (Product xs) (Product ys) =
    abelize $ Product $ xs <> ys

instance Monoid Permutation where
  mempty = Product []
  
-- | Assumes disjoint cycles
instance Group Permutation where
  ginverse (Product p) = Product (reverse $ (\(Cycle c) -> Cycle (reverse c)) <$> p)

-- | Assumes disjoint cycles
instance Eq Permutation where
  eq (Product p) (Product q) =
    let p' = filter (\(Cycle c) -> length c > 1) p
        q' = filter (\(Cycle c) -> length c > 1) q
    in length p' == length q'
      && all (_ `elem` q') p'

instance Hashable Permutation where
  hash p@(Product cs) =
    let hasContent = maximum 
          ( foldr 
            ( \(Cycle c) arr -> 
              if length c > 1 
                 then arr <> c 
                 else arr
            ) [] cs
          ) 
    in 
      case hasContent of
         Just n -> 
          let base = 0..n
              perm = permute p base
              nth i xs = 
                case xs !! i of
                     Just x -> x
                     _ -> 0
              ash h = foldr (\i acc -> acc + (i `nth` h) * Int.pow (n+1) i) 0 $ 0..n 
          in ash perm - ash base
         _ -> 0

instance Ord Permutation where
  compare p1 p2 = compare (hash p1) (hash p2)
         
-- | Returns 1 if p = id, or k>1 s.t. p^(k-1) /= id and p^k = id  
-- | Assumes product disjoint cycles
order :: Permutation -> Int 
order (Product cs) =
  case uncons cs of
    Just _ -> foldr lcm 1 $ (\(Cycle c) -> length c) <$> cs
    _ -> 1

-- | Returns the type of a permutation, i.e. the list of orders 
-- | of one of its expected representation as a product of disjoint cycles.
-- | This type is notably the characteritic shared by every conjuate of the permutation,
-- | in other words, the set of permutations sharing the same type
ptype :: Permutation -> Array Int
ptype (Product bs) =
  let cs = filter (\(Cycle c) -> length c > 1) bs
  in sort $ (\(Cycle c) -> length c) <$> cs

-- | Returns the set of elements generated by an set of permutations. 
-- | Assumes set of products of disjoint cycles.
generate :: Set Permutation -> Set Permutation
generate arr =
  let atomize p = foldr (\i acc -> insert (power p i) acc) empty $ Set.fromFoldable $ 1..order p
      atoms = unions $ Set.map atomize arr
      nth i xs = 
        case xs !! i of
              Just x -> x
              _ -> Product []
      go acc =
        let new = foldr 
              (\ (pair :: Array _) prev -> 
                insert (0 `nth` pair <> 1 `nth` pair) (prev :: Set _)
              ) acc
              $ (sequence [toUnfoldable acc, toUnfoldable atoms] :: Array (Array _))
        in if size acc == size new
              then acc
              else go new
    in go $ singleton mempty  

trim :: Permutation -> Permutation
trim (Product xs) = Product $ filter (\(Cycle cs) -> length cs > 1) xs

-- |
-- | Presentation of the Symmetric Group of order n
-- | as an array of product of disjoint cycles.
-- |
symmetric :: Int -> Array Permutation
symmetric n = 
  trim <$>
  abelize <$> 
    toUnfoldable 
      ( generate $ 
          Set.fromFoldable 
            [ Product [Cycle [0,1]]
            , Product [Cycle $ 0..(n-1)]
            ]
      )

-- | Returns the number of permutations 
-- | compound of products of exactly k disjoint cycles
-- | over n elements.
-- | For instance, stirling1 5 3 = 35 for
-- | * 20 for cardinality of type (abc)(d)(e) and
-- | * 15 for cardinality of type (ab)(cd)(e)
stirling1 :: Int -> Int -> Int
stirling1 n k = 
  let x = 1 ^ 1
  in abs $ (_ ! k) $ product $ (\i -> x - i^0) <$> 0..(n - 1)

filterM :: forall a. Ord a => (a -> Set Boolean) -> Set a -> Set (Set a)
filterM p xs =
  case findMin xs of
    Just head ->
      let 
        bs = p head
        rest = filterM p (toggle head xs)
      in unions $ Set.map (\b -> if b then Set.map (insert head) rest else rest ) bs 
    _ -> insert empty empty

subsets :: forall a. Ord a => Set a -> Set (Set a)
subsets = filterM (const $ insert true $ insert false empty)

histogram :: Array Int -> Array (Int /\ Int)
histogram = 
  let defaultHead xs =
        case uncons xs of
             Just { head } -> head
             _ -> 0
  in map (\x -> defaultHead x /\ length x) <<< map NonEmpty.toArray <<< group <<< sort

factorial :: Int -> Int
factorial 1 = 1
factorial n = n * factorial (n-1)

-- | Returns the number of permutations of whole elements
-- | satisfying the provided type given by an array of cycle lengths.
-- | For instance cardinality [2,2] 5 = cardinality [2,2,1] 5 = 15
-- | for all permutations of type (ab)(cd)(e).
cardinality :: Array Int -> Int -> Int
cardinality ptyp whole =
  if whole < sum ptyp
     then 0
     else factorial whole / (foldr (\ (v /\ m) acc -> acc * Int.pow v m * factorial m) 1 hist)
  where
    complete =
      if whole == sum ptyp
         then ptyp
         else ptyp <> (foldr (\ _ acc -> 1 : acc) [] $ 1..(whole - sum ptyp))
    hist = histogram complete

cardinality' :: Array Int -> Int -> Int
cardinality' ptyp whole =
  if whole < sum ptyp
     then 0
     else factorial whole / (foldr (\ (v /\ m) acc -> acc * Int.pow (factorial v) m * factorial m) 1 hist)
  where
    complete =
      if whole == sum ptyp
         then ptyp
         else ptyp <> (foldr (\ _ acc -> 1 : acc) [] $ 1..(whole - sum ptyp))
    hist = histogram complete

-- | bell 5 = 1+5+10+10+15+10+1
-- | for 5 = 5     :             {{a,b,c,d,e}}
-- |       = 4 + 1 :             {{a,b,c,d},{e}},{{a,b,c,e},{d}},{{a,b,d,e},{c}},{{a,c,d,e},{b}},{{b,c,d,e},{a}}
-- |       = 3 + 2 :             {{a,b,c},{d,e}},{{a,b,d},{c,e}},{{a,c,d},{b,e}},{{b,c,d},{a,e}},{{a,b,e},{c,d}}
-- |                            ,{{a,c,e},{b,d}},{{a,d,e},{b,c}},{{b,c,e},{a,d}},{{c,d,e},{a,b}},{{b,d,e},{a,c}}
-- |       = 3 + 1 + 1 :         {{a,b,c},{d},{e}},{{a,b,d},{c},{e}}
-- |                            ,{{a,c,d},{b},{e}},{{b,c,d},{a},{e}}
-- |                            ,{{a,b,e},{c},{d}},{{a,c,e},{b},{d}}
-- |                            ,{{a,d,e},{b},{c}},{{b,c,e},{a},{d}}
-- |                            ,{{c,d,e},{a},{b}},{{b,d,e},{a},{c}}
-- |                            ,a+a*a,a+aa*,aa+*a,aa+a*,aaa+*
-- |       = 2 + 2 + 1 :         ++**a,++*a*,++a**,+a+**,a++**
-- |                            ,+*+*a,+*+a*,+*a+*,+a*+*,a+*+*
-- |                            ,+**+a,+**a+,+*a*+,+a**+,a+**+
-- |       = 2 + 1 + 1 + 1 :     {{a},{b},{c},{d,e}},{{a},{b},{d},{c,e}}
-- |                            ,{{a},{c},{d},{b,e}},{{b},{c},{d},{a,e}}
-- |                            ,{{a},{b},{e},{c,d}},{{a},{c},{e},{b,d}}
-- |                            ,{{a},{d},{e},{b,c}},{{b},{c},{e},{a,d}}
-- |                            ,{{c},{d},{e},{a,b}},{{b},{d},{e},{a,c}}
-- |       = 1 + 1 + 1 + 1 + 1 : {{a},{b},{c},{d},{e}}
bell :: Int -> Int
bell n = sum $ flip cardinality' n <$> makePartitions n


-- | Tests if the set of given elements is closed under group operation 
isGroup :: Set Permutation -> Boolean
isGroup s =
  all (\ a -> all (\ b -> (a <> b) `member` s) $ toUnfoldable s) $ toUnfoldable s

-- | Tests if the set of elements of given types is closed under group operation 
isGroupType :: Set (Array Int) -> Int -> Boolean
isGroupType s whole =
  let symm = generate $ Set.fromFoldable [Product [Cycle [0,1]], Product [Cycle $ 0..(whole-1)]]
      es   = Set.filter (\p -> ptype p `member` s) symm
  in all (\ a -> all (\ b -> (a <> b) `member` es) $ toUnfoldable es) $ toUnfoldable es

normalSubgroupTypes :: Int -> Set (Set (Array Int))
normalSubgroupTypes whole =
  let symm = generate $ Set.fromFoldable [Product [Cycle [0,1]], Product [Cycle $ 0..(whole-1)]]
      unionOfDistinctTypes = subsets $ Set.map ptype symm
      containsIdentity = Set.filter (\s -> [] `member` s)
      cardinalityCompatible = \s -> factorial whole `mod` sum (flip cardinality whole <$> (toUnfoldable s :: Array _)) == 0
      candidateTypes = Set.filter cardinalityCompatible $ containsIdentity unionOfDistinctTypes
  in Set.filter (flip isGroupType whole) candidateTypes

makePartitions ::  Int -> Array (Array Int)
makePartitions m = parts (m /\ m) where
  parts (n /\ maxx)
    | n > 0     = 
        do
          x <- (min n maxx)..1
          p <- parts ((n - x) /\ x)
          pure $ x : p
    | n == 0    = [[]]
    | otherwise = []

partitions :: Int -> Int
partitions = length <<< makePartitions

sumDivisors :: Int -> Int
sumDivisors 1 = 1
sumDivisors n = n * partitions n - sum ((\i -> sumDivisors i * partitions (n-i)) <$> (1..(n-1)))

ramanujanTau :: Int -> Int
ramanujanTau 1 = 1
ramanujanTau n = (-24 * sum ((\i -> sumDivisors i * ramanujanTau (n-i)) <$> (1..(n-1)))) `div` (n-1)

subgroups :: Set Permutation -> Set (Set Permutation)
subgroups gg =
  let ns = subsets gg
  in Set.filter (\n -> all (_ `member` n) $ toUnfoldable $ generate n) ns
  
-- | Construit la liste des listes obtenues successivement 
-- | par insertion de l'élément fourni après chacun des éléments de la liste fournie 
-- | et ce tant que l'élément en question n'est pas rencontré 
-- | (fonction auxiliaire de permutationsR) :

insycleR :: forall a. Eq a => a -> Array a -> Array (Array a)
insycleR x ys = insycleR' x ys [] where
  insycleR' z end zs = 
    case uncons end of
      Just { head, tail } -> (:) (zs <> [z] <> end) $
        if head == z
          then []
          else insycleR' z tail (zs <> [head])
      _ -> [zs <> [z]]
      
-- | Etablit la liste complète des permutations distinctes d'une liste 
-- | même en cas d'éléments redondants :
permutationsR :: forall f a. Foldable f => Eq a => f a -> Array (Array a)
permutationsR xs = foldr (\x nss -> nss >>= insycleR x) [[]] xs 

-- | Partitions d'un ensemble en sous-ensembles :
makeBells :: forall a. Array a -> Array (Array (Array (NonEmptyArray a)))
makeBells str = map (bells str) ((makePartitions $ length str) >>= permutationsR) where
  bells st part = map (finalize st) $ filter (rG <<< (\arr -> case uncons arr of 
                                                                   Just { tail } -> tail
                                                                   _ -> [])) $ permutationsR ex where
    rG arr = 
      case uncons arr of
        Just { head: p0, tail: p0s } -> 
          case uncons p0s of
            Just { head: p1, tail } ->
              p1 <= 1 + (fromMaybe 0 $ maximum tail) && rG tail
            _ -> p0 == 0
        _ -> true
    ex = expand part
    expand p = concat $ ex' p 0
    ex' arr n = 
      case uncons arr of
        Just { head, tail } -> (replicate head n) : ex' tail (n+1)
        _ -> []
    finalize s p = map (map fst) $ groupBy g $ sortBy f $ zip s p where
      f a b = if snd a < snd b then LT else GT
      g a b = snd a == snd b


leftCosets :: Set Permutation -> Set Permutation -> Set (Set Permutation)
leftCosets g h =
  Set.map (\x -> Set.map (trim <<< (x <> _)) h) g
  
rightCosets :: Set Permutation -> Set Permutation -> Set (Set Permutation)
rightCosets g h =
  Set.map (\x -> Set.map (trim <<< (_ <> x)) h) g

normalSubgroups :: Set Permutation -> Set (Set Permutation)
normalSubgroups g =
  Set.filter (\h -> leftCosets g h == rightCosets g h) $ Set.map (Set.map trim) $ subgroups g

{-
A subgroup N of a group G is called a normal subgroup of G if aN = Na for all a in G.

Equivalently, a subgroup N of the group G is normal in G if and only if g n g^{ −1 } ∈ N for all g ∈ G and n ∈ N. 
(the _conjugation_ of an element of N by an element of G is always in N.) 

The usual notation for this relation is N ◃ G.
-}

{-
There exists a group on the set of left cosets of N where multiplication of any two left cosets gN and hN yields the left coset (gh)N. This group is called the quotient group of G modulo N, denoted G/N.
-}

{-
The index of a subgroup N in a group G is the number of left cosets of N in G, or equivalently, the number of right cosets of N in G (since for m!=n, either bm=bn and mb=nb, or bm!=bn and mb!=nb). The index is denoted |G:N|=|G|/|N|, and if N◃G, it is equal to the order of the quotient group G/N.
-}

{-
Sn has n! elements
-}

{-
Every subgroup H of index 2 is normal :
either x ∈ G is in H, 
then xH=H=Hx

or x in G-H,
then xH/=H but xH=G-H
and Hx/=H but Hx=G-H


-}

{-
Normal subgroups are either:
* trivial (identity or group itself)
* An
* V = ({1,3,5,7}, × mod 8) when n=4
* 
-}

{-
The conjugacy class of an element a ∈ G:
Cl(a) = { g a g^{ -1 } | g ∈ G}
-}

{- for instance, the center Z(G) of a group G,
Z(G) = {z ∈ G | ∀g ∈ G, zg = gz},
or equivalently, Z(G) = {z ∈ G | Cl(z) = {z}}
satisfies Z(G) ◃ G.
Prop:
* trivial for Sn, n>=3
* trivial for An, n>=4
* G abelian <=> Z(G) = G <=> Cl(a) = {a} ∀a ∈ G
-}

{-
A group homomorphism θ: (G,∗) → (G',⋄) is a function  satisfying

θ(Id_G) = Id_G'
θ(x∗y) = θ(x)⋄θ(y)
-}

{-
If H◃G, then the function π:G→G/H defined by π(a)=aH is a group homomorphism. π(G) is isomorphic to G/ker π.
-}

{-
In other words, the normal subgroups of G are the kernels of group homomorphisms with domain G.
-}

{-
Pour tout g ∈ G, l'application ι_g : x ↦ gxg^{− 1} est un automorphisme de G. L'application ι : g ↦ ι_g  est alors un morphisme de groupes de G vers Aut(G). Son noyau est le centre de G. Son image, notée Int(G), est un sous-groupe normal de Aut(G), dont les éléments (les ι_g) sont appelés les automorphismes intérieurs de G. Le quotient de Aut(G) par Int(G) est noté Out(G) ; ses éléments sont appelés les automorphismes extérieurs de G. 
-}

{-
Inner Automorphisms : defined by conjugation (induced by x: g |-> x^{ -1 }gx)
Outer Automorphisms : defined otherwise

For instance, S5 has a normal subgroup H of order 6 (and cardinality 20=5!/(3^1.2^1.1!.1!) ) 
composed of permutations of type [2,3]:

> s5 = Set.map trim $ generate $ Set.fromFoldable [Product [Cycle [0,1]], Product [Cycle $ 0..4]]
> Set.map order s5                              
(fromFoldable [1,2,3,4,5,6])

> Set.size $ Set.filter ((_ == 6) <<< order) s5                
20

> Set.map ptype $ Set.filter ((_ == 6) <<< order) s5
(fromFoldable [[2,3]])

So there is an homomorphism phi: S5 -> S6. 
But, since S5 is trivially a normal subgroup of S6 (by fixing an element), 
there also is an homomorphism psi: S6 -> S5.
The composition phi.psi : S6 -> S6 defines an automorphism of S6 which can't be described
by conjugation: this is an outer automorphism.
                           ------------------
Indeed, by looking at the different cycle structures:

> flip cardinality 6 <$> [[],[2],[2,2],[2,2,2],[3],[2,3],[3,3],[4],[2,4],[5],[6]]      
[1,15,45,15,40,120,40,90,90,144,120]

In fact, as one way to define it, we start with the generators of S6: (01), (12), (23), (34) and (45).
We need 5 other transpositions : 
(24)=(23)(34)(23)
(14)=(12)(24)(12)
(25)=(24)(45)(24)
(35)=(34)(45)(34)
(05)=(01)(14)(45)(14)(01)

Then the following maps give possible definitions for θ:
(01) |-> (01)(23)(45) *
(12) |-> (12)(34)(05) ** all distinct from *
(23) |-> (01)(24)(35) *** all distinct from **, 1 in common with *
(34) |-> (23)(05)(14) **** all distinct from ***, 1 in common with * and **
(45) |-> (01)(34)(25) similarly
θ(24)=θ(23)θ(34)θ(23)=(45)(13)(02)
θ(25)=θ(24)θ(45)θ(24)=(23)(15)(04)
θ(35)=θ(34)θ(45)θ(34)=(45)(12)(03)
θ(14)=θ(12)θ(24)θ(12)=(24)(15)(03)
θ(05)=θ(04)θ(45)θ(04)=(24)(13)(05)

θ(15)=θ(12)θ(25)θ(12)=(35)(14)(02)
θ(04)=θ(01)θ(14)θ(01)=(35)(12)(04)
θ(13)=θ(12)θ(23)θ(12)=(25)(13)(04)
θ(02)=θ(01)θ(12)θ(01)=(25)(14)(03)
θ(03)=θ(01)θ(13)θ(01)=(34)(15)(02)

and its inverse θ⁻¹:
(01) |-> θ(01)
(12) |-> θ(04)
(23) |-> θ(45)
(34) |-> θ(35)
(45) |-> θ(23)

θ⁻¹(24)=θ(34)
θ⁻¹(25)=θ(24)
θ⁻¹(35)=θ(25)
θ⁻¹(14)=θ(03)
θ⁻¹(05)=θ(12)

θ⁻¹(15)=θ(02)
θ⁻¹(04)=θ(13)
θ⁻¹(02)=θ(14)
θ⁻¹(03)=θ(15)
θ⁻¹(13)=θ(05)


θ ∈ Aut(S6)

Let T: S6 -> Aut(S6)
       s |-> θ_s

s ∈ ker T
T(s) = Id_Aut(S6)
θ_s  = Id_Aut(S6)
θ_s(x) = x

-}

f0 = Product [Cycle [0,1], Cycle [2,3], Cycle [4,5]] :: Permutation
f1 = Product [Cycle [1,2], Cycle [3,4], Cycle [0,5]] :: Permutation
f2 = Product [Cycle [0,1], Cycle [2,4], Cycle [3,5]] :: Permutation
f3 = Product [Cycle [2,3], Cycle [0,5], Cycle [1,4]] :: Permutation
f4 = Product [Cycle [0,1], Cycle [3,4], Cycle [2,5]] :: Permutation
f5 = f2<>f3<>f2 :: Permutation
f6 = f5<>f4<>f5 :: Permutation
f7 = f3<>f4<>f3 :: Permutation
f8 = f1<>f5<>f1 :: Permutation
f9 = f1<>f6<>f1 :: Permutation
f10= f0<>f8<>f0 :: Permutation
f11= f1<>f2<>f1 :: Permutation
f12= f0<>f1<>f0 :: Permutation
f13= f10<>f4<>f10 :: Permutation
f14= f0<>f11<>f0 :: Permutation


{-
why if [Sn:An]=2, then N=An or N=Sn ? – xyz Oct 2, 2020 at 2:07

@xyz In general, if p is a prime, H<G with |G:H|=p, then for H⊂K⊂G, 
we have H=K or G=K. This follows from the fact that indices are multiplicative: 
|G:H|=|G:K|⋅|K:H|, and the factorization of a prime
-}

{-
For n≥5, An is the only proper nontrivial normal subgroup of Sn.
-}


{-
A cycle of length L = k · m, taken to the kth power, will decompose into k cycles of length m.
-}

  

{-
If N is a normal subgroup, we can define a multiplication on cosets as follows:
(a1 N) (a2 N) := (a1 a2) N.
This relation defines a mapping G / N × G / N → G / N. 
To show that this mapping is well-defined, one needs to prove that the choice of representative elements a1, a2 
does not affect the result. To this end, consider some other representative elements a1′ ∈ a1 N, a2′ ∈ a2 N.
Then there are n1, n2 ∈ N such that a1′ = a1 n1, a2′ = a2 n2.
It follows that a1′ a2′ N = a1 n1 a2 n2 N = a1 a2 n1' n2 N = a1 a2 N,
where we also used the fact that N is a normal subgroup, and therefore there is n1′ ∈ N
such that n1 a2 = a2 n1′.
This proves that this product is a well-defined mapping between cosets.

With this operation, the set of cosets is itself a group, called the quotient group and denoted with G / N .
There is a natural homomorphism, f : G → G / N, given by f(a) = a N.
This homomorphism maps N into the identity element of G / N, which is the coset e N = N, that is, ker(f) = N. 
-}
  
{-
Lemma: Let p be a prime number, and let f ∈ Q[t] be an irreducible
polynomial of degree p with exactly p − 2 real roots. Then GalQ(f) ~ Sp.
-}

{-
Proof: Since char Q = 0 and f is irreducible, f is separable and therefore has p
distinct roots in C. The action of GalQ(f)=Aut(SF_Q(f)/Q) (the set of bijections 
from the quotiented splitting field SF_Q(f)/Q to itself) on the roots of f in C defines an isomorphism 
between GalQ(f) and a subgroup H of Sp. Since f is irreducible, 
p divides |GalQ(f)| = |H| (|GalQ(f)|=[SF_Q(f):Q] by the fundamental theorem of Galois theory, 
then [SF_Q(f):Q]=[SF_Q(f):Q(α)][Q(α):Q] for each α of f's roots since [Q(α):Q]=p). 
So by Cauchy’s theorem, H has an element σ of order p. Then σ is a p-cycle, since these are the
only elements of Sp of order p.
The complex conjugate of any root of f is also a root of f, so complex
conjugation h restricts to an automorphism of the splitting field SF_Q(f) over Q, 
since for every g ∈ Sp, and all h, k ∈ H, 

g⋅(h*k) = (g⋅h)∗(g⋅k) where . is SF_Q(f)'s composition and * is H's composition

so the permutation h ↦ g⋅h de SF_Q(f)/Q is an automorphism of H. 
Exactly two of the roots of f are non-real; complex conjugation transposes them and fixes the rest.
So H contains a transposition τ.
Without loss of generality, τ = (12). Since σ is a p-cycle, σ^r(1) = 2 for
some r ∈ {1, ... , p − 1}. Since p is prime, σ^r also has order p, so it is a p-cycle.
Now without loss of generality, σ^r = (123 ··· p). So (12), (12 ··· p) ∈ H, forcing
H = Sp. Hence GalQ(f) ~ Sp.
-}

{-
Some reductible polynomials can have some radical roots and some non radical roots.
Irreducible polynomials can't: either all radical or all non radical roots.
-}
