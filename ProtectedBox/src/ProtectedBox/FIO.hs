{-# LANGUAGE GADTs #-}
module ProtectedBox.FIO where

import qualified Data.ByteString as BS
import Control.Monad
import qualified OBDD as B

{- DC Labels -}
type Atom = String

data Form = Atomic Atom
          | And Form Form
          | Or Form Form
          | T
          | F
          deriving (Show, Read)

cnf :: Form -> B.OBDD String
cnf T          = B.true
cnf F          = B.false
cnf (Or l r)   = cnf l B.|| cnf r
cnf (And l r)  = cnf l B.&& cnf r
cnf (Atomic a) = B.variable a

data DCLabel = DCLabel Form Form deriving (Show, Read)

lub :: DCLabel -> DCLabel -> DCLabel
lub (DCLabel c0 i0) (DCLabel c1 i1) = DCLabel 
  (And c0 c1) (Or i0 i1)

type PC = [Branch]

pos :: PC -> [DCLabel]
pos pc = [ l | Private l <- pc ]

neg :: PC -> [DCLabel]
neg pc = [ l | Public l <- pc ]

sat :: B.OBDD String -> Bool
sat = B.satisfiable

tautology :: B.OBDD String -> Bool
tautology = not . B.satisfiable . B.not

bot :: DCLabel
bot = DCLabel T F

isEmptyViews :: PC -> Bool
isEmptyViews pc =
  let lc = foldr lub bot (pos pc) in
  not $ and [ not $ canFlowTo k lc | k <- neg pc ]

canFlowTo :: DCLabel -> DCLabel -> Bool 
canFlowTo (DCLabel c0 i0) (DCLabel c1 i1) = tautology ((cnf c1 B.==> cnf c0) B.&& (cnf i0 B.==> cnf i1))

-- Should we take the public branch when we have
-- pc and < l ? ... : ... >
takePublic :: PC -> DCLabel -> Bool
takePublic pc l = isEmptyViews (Private l : pc)

-- Should we take the private branch when we have
-- pc and < l ? ... : ... >
takePrivate :: PC -> DCLabel -> Bool
takePrivate pc l = isEmptyViews (Public l : pc)

inViewsOf :: DCLabel -> PC -> Bool
inViewsOf l pc =
  and [ canFlowTo k l | k <- pos pc ] &&
  and [ not $ canFlowTo k l | k <- neg pc ]

{-
 -------------------------------------------------------
                      Faceted values
 -------------------------------------------------------
-}

data Faceted a where
  Raw     :: a -> Faceted a
  Faceted :: DCLabel -> Faceted a -> Faceted a -> Faceted a

{- Faceted -}
instance Functor (Faceted) where
  fmap f (Raw v)              = Raw (f v)
  fmap f (Faceted k priv pub) = Faceted k (fmap f priv)
                                          (fmap f pub)

instance Applicative (Faceted) where
  pure           = Raw
  (Raw f) <*> x  =  fmap f x
  (Faceted k priv pub) <*> x = Faceted k (priv <*> x)
                                         (pub <*> x)

instance Monad (Faceted) where
  return = Raw
  (Raw x) >>= f = f x
  (Faceted k priv pub) >>= f  = Faceted k (priv >>= f)
                                          (pub >>= f)

raw :: a -> Faceted a
raw = Raw

facet :: DCLabel -> Faceted a -> Faceted a -> Faceted a
facet = Faceted

-- Debug only!
printFaceted :: Show a => Faceted a -> String
printFaceted (Raw a)              = "< " ++ show a ++ " >"
printFaceted (Faceted l priv pub) = "< " ++ show l ++ " : " ++ printFaceted priv ++ " , " ++ printFaceted pub ++ " >"

-- TODO: Change to continuation monad + trace
data FIO a where
  -- Branching
  -- TODO: Consider adding "I'm asking for this much of a timeout"
  --       for the sake of the hybrid semantics
  Branch ::  Faceted (FIO a) -> (Faceted a -> FIO b) -> FIO b
  -- Finishing
  Done   :: a -> FIO a
  -- File storage API
  Read       :: String -> (Faceted (Maybe BS.ByteString) -> FIO b) -> FIO b
  ReadMeta   :: String -> String -> (Faceted (Maybe BS.ByteString) -> FIO b) -> FIO b
  Write      :: String -> BS.ByteString -> FIO b -> FIO b
  WriteMeta  :: String -> String -> BS.ByteString -> FIO b -> FIO b
  Create     :: DCLabel -> String -> BS.ByteString -> FIO b -> FIO b
  CreateMeta :: DCLabel -> String -> BS.ByteString -> FIO b -> FIO b
  -- Output API
  Output :: String -> FIO b -> FIO b

instance Functor (FIO) where
    fmap = liftM

instance Applicative (FIO) where
    pure  = return
    (<*>) = ap

instance Monad (FIO) where
    return = Done

    Branch fac k       >>= k' = Branch fac ((>>= k') . k)
    Done a             >>= k' = k' a
    Read n k           >>= k' = Read n ((>>= k') . k)
    Write n c k        >>= k' = Write n c (k >>= k')
    CreateMeta l n c k >>= k' = CreateMeta l n c (k >>= k')
    Create l n c k     >>= k' = Create l n c (k >>= k')
    Output s k         >>= k' = Output s (k >>= k')
    ReadMeta n l k     >>= k' = ReadMeta n l ((>>= k') . k)
    WriteMeta n l c k  >>= k' = WriteMeta n l c (k >>= k')

data Branch = Private DCLabel
            | Public DCLabel
            deriving Show

{- Interface -}
branch :: Faceted (FIO a) -> FIO (Faceted a)
branch fac = Branch fac return

readFile :: String -> FIO (Faceted (Maybe BS.ByteString))
readFile n = Read n return

writeFile :: String -> BS.ByteString -> FIO ()
writeFile n c = Write n c (return ())

createFile :: DCLabel -> String -> BS.ByteString -> FIO ()
createFile l n c = Create l n c (return ())

output :: String -> FIO ()
output s = Output s (return ())

{- Derived combinators -}
branchOn ::  Faceted a -> (a -> FIO b) -> FIO (Faceted b)
branchOn fac op = branch (fmap op fac)
