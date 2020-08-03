module Data.Semigroup.Involutive
  ( Involutive(..)
  ) where

import GHC.Generics

import Data.Ord
import Data.Semigroup

import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity

import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as List.NonEmpty
import Data.Proxy

import qualified Data.ByteString as Strict
import qualified Data.ByteString as Strict.ByteString
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.ByteString.Lazy as Lazy.ByteString
import Data.Void

import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Data.Text as Strict
import qualified Data.Text as Strict.Text
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy as Lazy.Text

import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Vector.Unboxed (Unbox)
import qualified Data.Vector.Unboxed as Unboxed
import qualified Data.Vector.Unboxed as Unboxed.Vector
import Data.Vector.Storable (Storable)
import qualified Data.Vector.Storable as Storable
import qualified Data.Vector.Storable as Storable.Vector
import Data.Vector.Primitive (Prim)
import qualified Data.Vector.Primitive as Primitive
import qualified Data.Vector.Primitive as Primitive.Vector

-- | 'Involutive' lies between 'Semigroup' and @Group@, orthogonally to
-- 'Monoid'. Instances should satisfy the following:
--
-- [Involution] @'rev' ('rev' x) = x@
-- [Reversal]   @'rev' (x '<>' y) = 'rev' y '<>' 'rev' x@
--
-- An 'Involutive' 'Monoid' should additionally satisfy:
--
-- [Identity] @'rev' 'mempty' = 'mempty'@
--
-- Note that, in a commutative 'Semigroup', we could lawfully take @'rev' =
-- 'id'@ if all else failed. This would be bad, so we have not done so here.
class (Semigroup a) => Involutive a where
  -- | An "inverse-like" unary operation. Suggestively named 'rev' because the
  -- best example (that isn't just a group inverse) is the reverse operation on
  -- a sequence type.
  rev :: a -> a

-- For several instances, we appeal to the following general principle: if @f@
-- is a commutative applicative functor with @(<>) = liftA2 (<>)@, then @fmap
-- rev@ is a lawful definition for @rev@ at @f a@ (for any @a@).
--
-- The fact that this principle does not work for non-commutative applicative
-- functors explains some of the missing instances (e.g.: @Ap@, @IO@, @ST@).

instance Involutive () where
  rev = const ()
  {-# INLINE rev #-}

instance Involutive Void where
  rev = id
  {-# INLINE rev #-}

instance (Involutive a, Involutive b) => Involutive (a, b) where
  rev (a, b) = (rev a, rev b)
  {-# INLINE rev #-}

instance (Involutive a, Involutive b, Involutive c) => Involutive (a, b, c) where
  rev (a, b, c) = (rev a, rev b, rev c)
  {-# INLINE rev #-}

instance (Involutive a, Involutive b, Involutive c, Involutive d) => Involutive (a, b, c, d) where
  rev (a, b, c, d) = (rev a, rev b, rev c, rev d)
  {-# INLINE rev #-}

instance (Involutive a, Involutive b, Involutive c, Involutive d, Involutive e) => Involutive (a, b, c, d, e) where
  rev (a, b, c, d, e) = (rev a, rev b, rev c, rev d, rev e)
  {-# INLINE rev #-}

-- Proof of reversal for tuples:
--
-- rev ((a, b, ..., z) <> (a', b', ..., z'))
-- rev (a <> a', b <> b', ..., z <> z')
-- (rev (a <> a'), rev (b <> b'), ..., rev (z <> z'))
-- (rev a' <> rev a, rev b' <> rev b, ..., rev z' <> rev z)
-- (rev a', rev b', ..., rev z') <> (rev a, rev b, ..., rev z)
-- rev (a', b', ..., z') <> rev (a, b, ..., z)

instance (Involutive a) => Involutive (Dual a) where
  rev = fmap rev
  {-# INLINE rev #-}

-- Proof of reversal for @Dual@:
--
-- rev (Dual a <> Dual b)
-- rev (Dual (b <> a))
-- Dual (rev (b <> a))
-- Dual (rev a <> rev b)
-- Dual (rev b) <> Dual (rev a)
-- rev (Dual b) <> rev (Dual a)

instance (Involutive a) => Involutive (Identity a) where
  rev = fmap rev
  {-# INLINE rev #-}

instance (Involutive a) => Involutive (Const a b) where
  rev = Const . rev . getConst
  {-# INLINE rev #-}

-- @a -> b@ is a commutative applicative functor with @(<>) = liftA2 (<>)@.
instance (Involutive b) => Involutive (a -> b) where
  rev = fmap rev
  {-# INLINE rev #-}

instance (Involutive a) => Involutive (Op a b) where
  rev = Op . rev . getOp
  {-# INLINE rev #-}

instance (Involutive a) => Involutive (Maybe a) where
  rev = fmap rev
  {-# INLINE rev #-}

-- Proof of reversal for Maybe:
--
-- rev (Nothing <> b)
-- rev b
-- rev b <> Nothing
-- rev b <> rev Nothing
--
-- rev (a <> Nothing)
-- rev a
-- Nothing <> rev a
-- rev Nothing <> rev b
--
-- rev (Just a <> Just b)
-- rev (Just (a <> b))
-- Just (rev (a <> b))
-- Just (rev b <> rev a)
-- Just (rev b) <> Just (rev a)
-- rev (Just b) <> rev (Just a)

instance Involutive [a] where
  rev = List.reverse
  {-# INLINE rev #-}

instance Involutive (NonEmpty a) where
  rev = List.NonEmpty.reverse
  {-# INLINE rev #-}

instance (Num a) => Involutive (Sum a) where
  rev = negate
  {-# INLINE rev #-}

-- @Down@ is a commutative applicative functor with @(<>) = liftA2 (<>)@.
instance (Involutive a) => Involutive (Down a) where
  rev (Down a) = Down (rev a)
  {-# INLINE rev #-}

-- @Proxy s@ is isomorphic to @()@.
instance Involutive (Proxy s) where
  rev = const Proxy
  {-# INLINE rev #-}

-- @V1 p@ is isomorphic to @Void@.
instance Involutive (V1 p) where
  rev = id
  {-# INLINE rev #-}

-- @U1 p@ is isomorphic to @()@.
instance Involutive (U1 p) where
  rev = const U1
  {-# INLINE rev #-}

-- @Par1 p@ is isomorphic to @p@.
instance (Involutive p) => Involutive (Par1 p) where
  rev = Par1 . rev . unPar1
  {-# INLINE rev #-}

-- @Rec1 f p@ is isomorphic to @f p@.
instance (Involutive (f p)) => Involutive (Rec1 f p) where
  rev = Rec1 . rev . unRec1
  {-# INLINE rev #-}

-- @K1 i c p@ is isomorphic to @c@.
instance (Involutive c) => Involutive (K1 i c p) where
  rev = K1 . rev . unK1
  {-# INLINE rev #-}

-- @M1 i c f p@ is isomorphic to @f p@.
instance (Involutive (f p)) => Involutive (M1 i c f p) where
  rev = M1 . rev . unM1
  {-# INLINE rev #-}

-- @(f :*: g) p@ is isomorphic to @(f p, g p)@.
instance (Involutive (f p), Involutive (g p)) => Involutive ((f :*: g) p) where
  rev (x :*: y) = rev x :*: rev y
  {-# INLINE rev #-}

-- @(f :.: g) p@ is isomorphic to @f (g p)@.
instance (Involutive (f (g p))) => Involutive ((f :.: g) p) where
  rev = Comp1 . rev . unComp1
  {-# INLINE rev #-}

instance Involutive Strict.ByteString where
  rev = Strict.ByteString.reverse
  {-# INLINE rev #-}

instance Involutive Lazy.ByteString where
  rev = Lazy.ByteString.reverse
  {-# INLINE rev #-}

instance Involutive (Seq a) where
  rev = Seq.reverse
  {-# INLINE rev #-}

instance Involutive Strict.Text where
  rev = Strict.Text.reverse
  {-# INLINE rev #-}

instance Involutive Lazy.Text where
  rev = Lazy.Text.reverse
  {-# INLINE rev #-}

instance Involutive (Vector a) where
  rev = Vector.reverse
  {-# INLINE rev #-}

instance (Unbox a) => Involutive (Unboxed.Vector a) where
  rev = Unboxed.Vector.reverse
  {-# INLINE rev #-}

instance (Storable a) => Involutive (Storable.Vector a) where
  rev = Storable.Vector.reverse
  {-# INLINE rev #-}

instance (Prim a) => Involutive (Primitive.Vector a) where
  rev = Primitive.Vector.reverse
  {-# INLINE rev #-}
