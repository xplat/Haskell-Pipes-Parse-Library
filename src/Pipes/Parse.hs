{-| Element-agnostic parsing utilities for @pipes@

    @pipes-parse@ provides two ways to parse and transform streams in constant
    space:

    * The \"list-like\" approach, using the split \/ transform \/ join paradigm

    * The monadic approach, using parser combinators

    The top half of this module provides the list-like approach.  The key idea
    is that:
    
> -- '~' means "is analogous to"
> Producer a m ()               ~   [a]
>
> FreeT (Producer a m ()) m ()  ~  [[a]]

    'FreeT' nests each subsequent 'Producer' within the return value of the
    previous 'Producer' so that you cannot access the next 'Producer' until you
    completely drain the current 'Producer'.  However, you rarely need to work
    with 'FreeT' directly.  Instead, you structure everything using
    \"splitters\", \"transformations\" and \"joiners\":

> -- A "splitter"
> Producer a m ()              -> FreeT (Producer a m ()) m ()  ~   [a]  -> [[a]]
>
> -- A "transformation"
> FreeT (Producer a m ()) m () -> FreeT (Producer a m ()) m ()  ~  [[a]] -> [[a]]
>
> -- A "joiner"
> FreeT (Producer a m ()) m () -> Producer a m ()               ~  [[a]] ->  [a]

    For example, if you wanted to group standard input by equal lines and take
    the first three groups, you would write:

> import Pipes
> import qualified Pipes.Parse as Parse
> import qualified Pipes.Prelude as Prelude
>
> threeGroups :: (Monad m, Eq a) => Producer a m () -> Producer a m ()
> threeGroups = Parse.concat . Parse.takeFree 3 . Parse.groupBy (==)
> --            ^ Joiner       ^ Transformation   ^ Splitter

    This then limits standard input to the first three consecutive groups of
    equal lines:

>>> run $ threeGroups Prelude.stdin >-> Prelude.stdout
Group1<Enter>
Group1
Group1<Enter>
Group1
Group2<Enter>
Group2
Group3<Enter>
Group3
Group3<Enter>
Group3
Group4<Enter>
>>> -- Done, because we began entering our fourth group

    The advantage of this style or programming is that you never bring more than
    a single element into memory.  This works because `FreeT` sub-divides the
    `Producer` without concatenating elements together, preserving the laziness
    of the underlying 'Producer'.

    The bottom half of this module contains the lower-level monadic parsing
    primitives.  These are more useful for `pipes` implementers, particularly
    for building splitters.  I recommend that application developers use the
    list-like style whenever possible.
-}

{-# LANGUAGE RankNTypes #-}

module Pipes.Parse (
    -- * Splitters
    groupBy,
    chunksOf,
    splitOn,

    -- * Transformations
    takeFree,

    -- * Joiners
    concat,
    intercalate,

    -- * Low-level Parsers
    -- $lowlevel
    draw,
    unDraw,
    peek,
    isEndOfInput,

    -- * High-level Parsers
    -- $highlevel
    input,

    -- * Utilities
    takeWhile,

    -- * Re-exports
    -- $reexports
    module Control.Monad.Trans.Free,
    module Control.Monad.Trans.State.Strict
    ) where

import Control.Monad (forever, liftM, unless, void)
import qualified Control.Monad.Trans.Free as F
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Free (FreeF(Free), FreeT(FreeT, runFreeT))
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.State.Strict (
    StateT(StateT, runStateT), evalStateT, execStateT )
import Data.Maybe (isNothing)
import Pipes (Producer, Pipe, Consumer, await, yield, next, (>->), run)
import Pipes.Core (Producer')
import Pipes.Internal (Proxy(..))
import Pipes.Lift (runStateP, execStateP)
import qualified Pipes.Prelude as P
import Prelude hiding (concat, takeWhile)

{-| Split a 'Producer' into a `FreeT`-delimited stream of 'Producer's grouped by
    the supplied equality predicate
-}
groupBy
    :: (Monad m)
    => (a -> a -> Bool) -> FreeT (Pipe a a m) (Consumer a m) r
groupBy equal = lift await >>= loop
  where
    loop a = do
        x <- F.liftF $ do
            yield a
            takeWhile' (equal a)
        loop x
{-# INLINABLE groupBy #-}

{-| Split a 'Producer' into a `FreeT`-delimited stream of 'Producer's of the
    given chunk size
-}
chunksOf :: (Monad m) => Int -> FreeT (Pipe a a m) (Consumer a m) () 
-- chunksOf n = forever $ F.liftF $ P.take n
-- can't be that easy if you don't want an empty last chunk :(
chunksOf 0 = forever $ F.liftF $ return ()
chunksOf n = forever $ do
    x <- lift await
    F.liftF $ do
        yield x
        P.take m
  where
    m = n - 1
{-# INLINABLE chunksOf #-}

{-| Split a 'Producer' into a `FreeT`-delimited stream of 'Producer's separated
    by elements that satisfy the given predicate
-}
splitOn
    :: (Monad m) => (a -> Bool) -> FreeT (Pipe a a m) (Consumer a m) ()
splitOn predicate = loop
  where
    loop = forever $ F.liftF $ P.takeWhile (not . predicate)
{-# INLINABLE splitOn #-}

{-| (p >>~* fl) pairs each 'respond' in @p@ with a 'request' in @fl@.
 -}
(>>~*)
    :: (Monad m)
    =>       Proxy a' a b' b m r
    -> (b -> FreeT (Proxy b' b c' c m) (Proxy b' b d' d m) r)
    ->       FreeT (Proxy a' a c' c m) (Proxy a' a d' d m) r
p >>~* flb = case p of
    Request a' fa  -> FreeT (Request a' (\a -> runFreeT (fa a >>~* flb)))
    Respond b  fb' -> fb' +>>* flb b
    M          m   -> FreeT (M (m >>= \p' -> return (runFreeT (p' >>~* flb))))
    Pure       r   -> FreeT (Pure (F.Pure r))
{-# INLINABLE (>>~*) #-}

(>>~?)
    :: (Monad m)
    =>       Proxy a' a b' b m r
    -> (b -> Proxy b' b c' c m (FreeT (Proxy b' b d' d m) (Proxy b' b e' e m) r))
    ->       Proxy a' a c' c m (FreeT (Proxy a' a d' d m) (Proxy a' a e' e m) r)
p >>~? fplb = case p of
    Request a' fa  -> Request a' (\a -> fa a >>~? fplb)
    Respond b  fb' -> fb' +>>? fplb b
    M          m   -> M (m >>= \p' -> return (p' >>~? fplb))
    Pure       r   -> Pure (FreeT (Pure (F.Pure r)))
{-# INLINABLE (>>~?) #-}

{-| (f +>>* lp) pairs each 'request' in @lp@ with a 'respond' in @f@.
 -}
(+>>*)
    :: (Monad m)
    => (b' -> Proxy a' a b' b m r)
    -> FreeT (Proxy b' b c' c m) (Proxy b' b d' d m) r
    -> FreeT (Proxy a' a c' c m) (Proxy a' a d' d m) r
fb' +>>* lp = case runFreeT lp of
    Request b'  fb  -> fb' b' >>~* (\b -> FreeT (fb b))
    Respond c   fc' -> FreeT (Respond c (\c' -> runFreeT (fb' +>>* FreeT (fc' c'))))
    M           m   -> FreeT (M (m >>= \lp' -> return (runFreeT (fb' +>>* FreeT lp'))))
    Pure        s   -> case s of
        F.Pure  r   -> FreeT (Pure (F.Pure r))
        Free    f   -> FreeT (Pure (Free (fb' +>>? f)))
{-# INLINABLE (+>>*) #-}

(+>>?)
    :: (Monad m)
    => (b' -> Proxy a' a b' b m r)
    -> Proxy b' b c' c m (FreeT (Proxy b' b d' d m) (Proxy b' b e' e m) r)
    -> Proxy a' a c' c m (FreeT (Proxy a' a d' d m) (Proxy a' a e' e m) r)
fb' +>>? plp = case plp of
    Request b'  fb  -> fb' b' >>~? fb
    Respond c   fc' -> Respond c (\c' -> (fb' +>>? fc' c'))
    M           m   -> M (m >>= \plp' -> return (fb' +>>? plp'))
    Pure        lp  -> Pure (fb' +>>* lp)
{-# INLINABLE (+>>?) #-}

(>->*)
    :: (Monad m)
    => Proxy a' a () b m r
    -> FreeT (Proxy () b c' c m) (Proxy () b d' d m) r
    -> FreeT (Proxy a' a c' c m) (Proxy a' a d' d m) r
p >->* lp = (\() -> p) +>>* lp
{-# INLINABLE (>->*) #-}

-- | Join a 'FreeT'-delimited stream of 'Producer's into a single 'Producer'
concat :: (Monad m) => FreeT (Producer a m) m () -> Producer a m ()
concat = loop
  where
    loop f = do
        x <- lift (runFreeT f)
        case x of
            F.Pure r -> return r
            Free   p -> do
                f' <- p
                concat f'
{-# INLINABLE concat #-}

{-| Join a 'FreeT'-delimited stream of 'Producer's into a single 'Producer' by
    intercalating a 'Producer' in between them
-}
intercalate
    :: (Monad m)
    => Producer a m () -> FreeT (Producer a m) m () -> Producer a m ()
intercalate sep = go0
  where
    go0 f = do
        x <- lift (runFreeT f)
        case x of
            F.Pure r -> return r
            Free   p -> do
                f' <- p
                go1 f'
    go1 f = do
        x <- lift (runFreeT f)
        case x of
            F.Pure r -> return r
            Free   p -> do
                sep
                f' <- p
                go1 f'
{-# INLINABLE intercalate #-}

-- | @(take n)@ only keeps the first @n@ functor layers of a 'FreeT'
takeFree :: (Functor f, Monad m) => Int -> FreeT f m r -> FreeT f m ()
takeFree n = void . splitAtFree n
{-# INLINABLE takeFree #-}

splitAtFree :: (Functor f, Monad m) => Int -> FreeT f m r -> FreeT f m (FreeT f m r)
splitAtFree = go
  where
    go n f =
        if (n > 0)
        then FreeT $ do
            x <- runFreeT f
            case x of
                F.Pure r -> return (F.Pure (return r))
                Free   w -> return (Free   (fmap (go $! n - 1) w))
        else return f
{-# INLINABLE splitAtFree #-}

test1 :: IO ()
test1 = run $ concat (takeFree 3 (F.hoistFreeT run (P.stdin >->* groupBy (==)))) >-> P.stdout

{- $lowlevel
    @pipes-parse@ handles end-of-input and pushback by storing a 'Producer' in
    a 'StateT' layer.
-}

{-| Draw one element from the underlying 'Producer', returning 'Nothing' if the
    'Producer' is empty
-}
draw :: (Monad m) => StateT (Producer a m r) m (Maybe a)
draw = do
    p <- S.get
    x <- lift (next p)
    case x of
        Left   r      -> do
            S.put (return r)
            return Nothing
        Right (a, p') -> do
            S.put p'
            return (Just a)
{-# INLINABLE draw #-}

-- | Push back an element onto the underlying 'Producer'
unDraw :: (Monad m) => a -> StateT (Producer a m r) m ()
unDraw a = S.modify (yield a >>)
{-# INLINABLE unDraw #-}

{-| 'peek' checks the first element of the stream, but uses 'unDraw' to push the
    element back so that it is available for the next 'draw' command.

> peek = do
>     ma <- draw
>     case ma of
>         Nothing -> return ()
>         Just a  -> unDraw a
>     return ma
-}
peek :: (Monad m) => StateT (Producer a m r) m (Maybe a)
peek = do
    ma <- draw
    case ma of
        Nothing -> return ()
        Just a  -> unDraw a
    return ma
{-# INLINABLE peek #-}

{-| Check if the underlying 'Producer' is empty

> isEndOfInput = liftM isNothing peek
-}
isEndOfInput :: (Monad m) => StateT (Producer a m r) m Bool
isEndOfInput = liftM isNothing peek
{-# INLINABLE isEndOfInput #-}

{- $highlevel
    'input' provides a 'Producer' that streams from the underlying 'Producer'.

    Streaming from 'input' differs from streaming directly from the underlying
    'Producer' because any unused input is saved for later, as the following
    example illustrates:

> import Control.Monad.IO.Class (liftIO)
> import Control.Monad.Trans.State.Strict
> import Pipes
> import Pipes.Parse
> import qualified Pipes.Prelude as P
>
> parser :: (Show a) => StateT (Producer a IO r) IO ()
> parser = do
>     run $ input >-> P.take 2 >-> P.show >-> hoist liftIO P.stdout
>
>     liftIO $ putStrLn "Intermission"
>
>     run $ input >-> P.take 2 >-> P.show >-> hoist liftIO P.stdout

    The second pipeline resumes where the first pipeline left off:

>>> evalStateT parser (each [1..])
1
2
Intermission
3
4

    You can see more examples of how to use these parsing utilities by studying
    the source code for the above splitters.
-}

-- | Stream from the underlying 'Producer'
input :: (Monad m) => Producer' a (StateT (Producer a m r) m) ()
input = loop
  where
    loop = do
        ma <- lift draw
        case ma of
            Nothing -> return ()
            Just a  -> do
                yield a
                loop
{-# INLINABLE input #-}

{-| A variation on 'Pipes.Prelude.takeWhile' from @Pipes.Prelude@ that 'return's
    the first element that does not match
-}

takeWhile'
    :: (Monad m) => (a -> Bool) -> Pipe a a m a
takeWhile' predicate = loop
  where
    loop = do
        a <- await
        if (predicate a)
            then do
                yield a
                loop
            else return a

{-| A variation on 'Pipes.Prelude.takeWhile' from @Pipes.Prelude@ that 'unDraw's
    the first element that does not match
-}
takeWhile
    :: (Monad m) => (a -> Bool) -> Pipe a a (StateT (Producer a m r) m) ()
takeWhile predicate = takeWhile' predicate >>= lift . unDraw
{-# INLINABLE takeWhile #-}

{- $reexports
    @Control.Monad.Trans.Free@ re-exports 'FreeF', 'FreeT', and 'runFreeT'.

    @Control.Monad.Trans.State.STrict@ re-exports 'StateT', 'runStateT',
    'evalStateT', and 'execStateT'.
-}
