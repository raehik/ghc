{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.GHC.ExactPrint.Transform
--
-- This module is currently under heavy development, and no promises are made
-- about API stability. Use with care.
--
-- We welcome any feedback / contributions on this, as it is the main point of
-- the library.
--
-----------------------------------------------------------------------------
module Transform
        (
        -- * The Transform Monad
          Transform
        , TransformT(..)
        , hoistTransform
        , runTransform
        , runTransformT
        , runTransformFrom
        , runTransformFromT

        -- * Transform monad operations
        , logTr
        , logDataWithAnnsTr
        , getAnnsT, putAnnsT, modifyAnnsT
        , uniqueSrcSpanT

        , cloneT
        , graftT

        , getEntryDPT
        , setEntryDPT
        , transferEntryDPT
        , setPrecedingLinesDeclT
        , setPrecedingLinesT
        , addSimpleAnnT
        , addTrailingCommaT
        , removeTrailingCommaT

        -- ** Managing declarations, in Transform monad
        , HasTransform (..)
        , HasDecls (..)
        , hasDeclsSybTransform
        , hsDeclsGeneric
        , hsDeclsPatBind, hsDeclsPatBindD
        , replaceDeclsPatBind, replaceDeclsPatBindD
        , modifyDeclsT
        , modifyValD
        -- *** Utility, does not manage layout
        , hsDeclsValBinds, replaceDeclsValbinds

        -- ** Managing lists, Transform monad
        , insertAt
        , insertAtStart
        , insertAtEnd
        , insertAfter
        , insertBefore

        -- *** Low level operations used in 'HasDecls'
        , balanceComments
        , balanceTrailingComments
        , moveTrailingComments

        -- ** Managing lists, pure functions
        , captureOrder
        , captureOrderAnnKey

        -- * Operations
        , isUniqueSrcSpan

        -- * Pure functions
        , mergeAnns
        , mergeAnnList
        , setPrecedingLinesDecl
        , setPrecedingLines
        , getEntryDP
        , setEntryDP
        , setEntryDP'
        , transferEntryDP
        , addTrailingComma
        , wrapSig, wrapDecl
        , decl2Sig, decl2Bind
        ) where

import Types
import Utils

import Control.Monad.RWS
import qualified Control.Monad.Fail as Fail

import qualified GHC           as GHC hiding (parseModule)
import qualified GHC.Data.Bag          as GHC
import qualified GHC.Data.FastString   as GHC

-- import qualified Data.Generics as SYB

import Data.Data
import Data.List
import Data.Maybe

import qualified Data.Map as Map

import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Writer

-- import Debug.Trace

------------------------------------------------------------------------------
-- Transformation of source elements

-- | Monad type for updating the AST and managing the annotations at the same
-- time. The W state is used to generate logging information if required.
type Transform = TransformT Identity

-- |Monad transformer version of 'Transform' monad
newtype TransformT m a = TransformT { unTransformT :: RWST () [String] (Anns,Int) m a }
                deriving (Monad,Applicative,Functor
                         ,MonadReader ()
                         ,MonadWriter [String]
                         ,MonadState (Anns,Int)
                         ,MonadTrans
                         )

instance Fail.MonadFail m => Fail.MonadFail (TransformT m) where
    fail msg = TransformT $ RWST $ \_ _ -> Fail.fail msg

-- | Run a transformation in the 'Transform' monad, returning the updated
-- annotations and any logging generated via 'logTr'
runTransform :: Anns -> Transform a -> (a,(Anns,Int),[String])
runTransform ans f = runTransformFrom 0 ans f

runTransformT :: Anns -> TransformT m a -> m (a,(Anns,Int),[String])
runTransformT ans f = runTransformFromT 0 ans f

-- | Run a transformation in the 'Transform' monad, returning the updated
-- annotations and any logging generated via 'logTr', allocating any new
-- SrcSpans from the provided initial value.
runTransformFrom :: Int -> Anns -> Transform a -> (a,(Anns,Int),[String])
runTransformFrom seed ans f = runRWS (unTransformT f) () (ans,seed)

-- |Run a monad transformer stack for the 'TransformT' monad transformer
runTransformFromT :: Int -> Anns -> TransformT m a -> m (a,(Anns,Int),[String])
runTransformFromT seed ans f = runRWST (unTransformT f) () (ans,seed)

-- | Change inner monad of 'TransformT'.
hoistTransform :: (forall x. m x -> n x) -> TransformT m a -> TransformT n a
hoistTransform nt (TransformT m) = TransformT (mapRWST nt m)

-- |Log a string to the output of the Monad
logTr :: (Monad m) => String -> TransformT m ()
logTr str = tell [str]

-- |Log a representation of the given AST with annotations to the output of the
-- Monad
logDataWithAnnsTr :: (Monad m) => (Data a) => String -> a -> TransformT m ()
logDataWithAnnsTr str ast = do
  anns <- getAnnsT
  logTr $ str ++ showAst ast

-- |Access the 'Anns' being modified in this transformation
getAnnsT :: (Monad m) => TransformT m Anns
getAnnsT = gets fst

-- |Replace the 'Anns' after any changes
putAnnsT :: (Monad m) => Anns -> TransformT m ()
putAnnsT ans = do
  (_,col) <- get
  put (ans,col)

-- |Change the stored 'Anns'
modifyAnnsT :: (Monad m) => (Anns -> Anns) -> TransformT m ()
modifyAnnsT f = do
  ans <- getAnnsT
  putAnnsT (f ans)

-- ---------------------------------------------------------------------

-- |Once we have 'Anns', a 'GHC.SrcSpan' is used purely as part of an 'AnnKey'
-- to index into the 'Anns'. If we need to add new elements to the AST, they
-- need their own 'GHC.SrcSpan' for this.
uniqueSrcSpanT :: (Monad m) => TransformT m GHC.SrcSpan
uniqueSrcSpanT = do
  (an,col) <- get
  put (an,col + 1 )
  let pos = GHC.mkSrcLoc (GHC.mkFastString "ghc-exactprint") (-1) col
  return $ GHC.mkSrcSpan pos pos

-- |Test whether a given 'GHC.SrcSpan' was generated by 'uniqueSrcSpanT'
isUniqueSrcSpan :: GHC.SrcSpan -> Bool
isUniqueSrcSpan ss = srcSpanStartLine ss == -1

srcSpanStartLine :: GHC.SrcSpan -> Int
srcSpanStartLine (GHC.RealSrcSpan s _) = GHC.srcSpanStartLine s
srcSpanStartLine _ = 0

-- ---------------------------------------------------------------------
-- |Make a copy of an AST element, replacing the existing SrcSpans with new
-- ones, and duplicating the matching annotations.
cloneT :: (Data a,Monad m) => a -> TransformT m (a, [(GHC.SrcSpan, GHC.SrcSpan)])
cloneT ast = do
  runWriterT $ everywhereM (return `ext2M` replaceLocated) ast
  where
    replaceLocated :: forall loc a m. (Typeable loc,Data a,Monad m)
                    => (GHC.GenLocated loc a) -> WriterT [(GHC.SrcSpan, GHC.SrcSpan)] (TransformT m) (GHC.GenLocated loc a)
    replaceLocated (GHC.L l t) = do
      case cast l :: Maybe GHC.SrcSpan of
        Just ss -> do
          newSpan <- lift uniqueSrcSpanT
          lift $ modifyAnnsT (\anns -> case Map.lookup (mkAnnKey (GHC.L ss t)) anns of
                                  Nothing -> anns
                                  Just an -> Map.insert (mkAnnKey (GHC.L newSpan t)) an anns)
          tell [(ss, newSpan)]
          return $ fromJust . cast  $ GHC.L newSpan t
        Nothing -> return (GHC.L l t)

-- ---------------------------------------------------------------------
-- |Slightly more general form of cloneT
graftT :: (Data a,Monad m) => Anns -> a -> TransformT m a
graftT origAnns = everywhereM (return `ext2M` replaceLocated)
  where
    replaceLocated :: forall loc a m. (Typeable loc, Data a, Monad m)
                    => GHC.GenLocated loc a -> TransformT m (GHC.GenLocated loc a)
    replaceLocated (GHC.L l t) = do
      case cast l :: Maybe GHC.SrcSpan of
        Just ss -> do
          newSpan <- uniqueSrcSpanT
          modifyAnnsT (\anns -> case Map.lookup (mkAnnKey (GHC.L ss t)) origAnns of
                                  Nothing -> anns
                                  Just an -> Map.insert (mkAnnKey (GHC.L newSpan t)) an anns)
          return $ fromJust $ cast $ GHC.L newSpan t
        Nothing -> return (GHC.L l t)

-- ---------------------------------------------------------------------

-- |If a list has been re-ordered or had items added, capture the new order in
-- the appropriate 'annSortKey' attached to the 'Annotation' for the first
-- parameter.
captureOrder :: (Data a) => GHC.LocatedA a -> [GHC.LocatedA b] -> Anns -> Anns
captureOrder parent ls ans = ans
-- captureOrder parent ls ans = captureOrderAnnKey (mkAnnKey parent) ls ans

-- |If a list has been re-ordered or had items added, capture the new order in
-- the appropriate 'annSortKey' item of the supplied 'AnnKey'
captureOrderAnnKey :: AnnKey -> [GHC.LocatedA b] -> Anns -> Anns
captureOrderAnnKey parentKey ls ans = ans
-- captureOrderAnnKey parentKey ls ans = ans'
--   where
--     newList = map (rs . GHC.getLoc) ls
--     reList = Map.adjust (\an -> an {annSortKey = Just newList }) parentKey
--     ans' = reList ans

-- ---------------------------------------------------------------------

-- |Pure function to convert a 'GHC.LHsDecl' to a 'GHC.LHsBind'. This does
-- nothing to any annotations that may be attached to either of the elements.
-- It is used as a utility function in 'replaceDecls'
decl2Bind :: GHC.LHsDecl GHC.GhcPs -> [GHC.LHsBind GHC.GhcPs]
decl2Bind (GHC.L l (GHC.ValD _ s)) = [GHC.L l s]
decl2Bind _                      = []

-- |Pure function to convert a 'GHC.LSig' to a 'GHC.LHsBind'. This does
-- nothing to any annotations that may be attached to either of the elements.
-- It is used as a utility function in 'replaceDecls'
decl2Sig :: GHC.LHsDecl GHC.GhcPs -> [GHC.LSig GHC.GhcPs]
decl2Sig (GHC.L l (GHC.SigD _ s)) = [GHC.L l s]
decl2Sig _                      = []

-- ---------------------------------------------------------------------

-- |Convert a 'GHC.LSig' into a 'GHC.LHsDecl'
wrapSig :: GHC.LSig GHC.GhcPs -> GHC.LHsDecl GHC.GhcPs
wrapSig (GHC.L l s) = GHC.L l (GHC.SigD GHC.NoExtField s)

-- ---------------------------------------------------------------------

-- |Convert a 'GHC.LHsBind' into a 'GHC.LHsDecl'
wrapDecl :: GHC.LHsBind GHC.GhcPs -> GHC.LHsDecl GHC.GhcPs
wrapDecl (GHC.L l s) = GHC.L l (GHC.ValD GHC.NoExtField s)

-- ---------------------------------------------------------------------

-- |Create a simple 'Annotation' without comments, and attach it to the first
-- parameter.
addSimpleAnnT :: (Data a,Monad m)
              => GHC.Located a -> GHC.DeltaPos -> [(KeywordId, GHC.DeltaPos)] -> TransformT m ()
addSimpleAnnT ast dp kds = do
  let ann = annNone { annEntryDelta = dp
                    , annsDP = kds
                    }
  modifyAnnsT (Map.insert (mkAnnKey ast) ann)

-- ---------------------------------------------------------------------

-- |Add a trailing comma annotation, unless there is already one
addTrailingCommaT :: (Data a,Monad m) => GHC.Located a -> TransformT m ()
addTrailingCommaT ast = do
  modifyAnnsT (addTrailingComma ast (GHC.DP (0,0)))

-- ---------------------------------------------------------------------

-- |Remove a trailing comma annotation, if there is one one
removeTrailingCommaT :: (Data a,Monad m) => GHC.Located a -> TransformT m ()
removeTrailingCommaT ast = do
  modifyAnnsT (removeTrailingComma ast)

-- ---------------------------------------------------------------------

-- |'Transform' monad version of 'getEntryDP'
getEntryDPT :: (Data a,Monad m) => GHC.Located a -> TransformT m GHC.DeltaPos
getEntryDPT ast = do
  anns <- getAnnsT
  return (getEntryDP anns ast)

-- ---------------------------------------------------------------------

-- |'Transform' monad version of 'getEntryDP'
setEntryDPT :: (Data a,Monad m) => GHC.LocatedA a -> GHC.DeltaPos -> TransformT m ()
setEntryDPT ast dp = do
  modifyAnnsT (setEntryDP ast dp)

-- ---------------------------------------------------------------------

-- |'Transform' monad version of 'transferEntryDP'
transferEntryDPT :: (Data a,Data b,Monad m) => GHC.LocatedA a -> GHC.LocatedA b -> TransformT m ()
transferEntryDPT a b =
  modifyAnnsT (transferEntryDP a b)

-- ---------------------------------------------------------------------

-- |'Transform' monad version of 'setPrecedingLinesDecl'
setPrecedingLinesDeclT :: (Monad m) => GHC.LHsDecl GHC.GhcPs -> Int -> Int -> TransformT m ()
setPrecedingLinesDeclT ld n c =
  modifyAnnsT (setPrecedingLinesDecl ld n c)

-- ---------------------------------------------------------------------

-- |'Transform' monad version of 'setPrecedingLines'
setPrecedingLinesT ::  (Data a,Monad m) => GHC.LocatedA a -> Int -> Int -> TransformT m ()
setPrecedingLinesT ld n c =
  modifyAnnsT (setPrecedingLines ld n c)

-- ---------------------------------------------------------------------

-- | Left bias pair union
mergeAnns :: Anns -> Anns -> Anns
mergeAnns
  = Map.union

-- |Combine a list of annotations
mergeAnnList :: [Anns] -> Anns
mergeAnnList [] = error "mergeAnnList must have at lease one entry"
mergeAnnList (x:xs) = foldr mergeAnns x xs

-- ---------------------------------------------------------------------

-- |Unwrap a HsDecl and call setPrecedingLines on it
-- ++AZ++ TODO: get rid of this, it is a synonym only
setPrecedingLinesDecl :: GHC.LHsDecl GHC.GhcPs -> Int -> Int -> Anns -> Anns
setPrecedingLinesDecl ld n c ans = setPrecedingLines ld n c ans

-- ---------------------------------------------------------------------

-- | Adjust the entry annotations to provide an `n` line preceding gap
setPrecedingLines :: (Data a) => GHC.LocatedA a -> Int -> Int -> Anns -> Anns
setPrecedingLines ast n c anne = setEntryDP ast (GHC.DP (n,c)) anne

-- ---------------------------------------------------------------------

-- |Return the true entry 'GHC.DeltaPos' from the annotation for a given AST
-- element. This is the 'GHC.DeltaPos' ignoring any comments.
getEntryDP :: (Data a) => Anns -> GHC.Located a -> GHC.DeltaPos
getEntryDP anns ast =
  case Map.lookup (mkAnnKey ast) anns of
    Nothing  -> GHC.DP (0,0)
    Just ann -> annTrueEntryDelta ann

-- ---------------------------------------------------------------------

-- |Set the true entry 'GHC.DeltaPos' from the annotation for a given AST
-- element. This is the 'GHC.DeltaPos' ignoring any comments.
setEntryDP' :: (Data a) => GHC.LocatedA a -> GHC.DeltaPos -> GHC.LocatedA a
setEntryDP' (GHC.L (GHC.SrcSpanAnn GHC.ApiAnnNotUsed l) a) dp
  = (GHC.L (GHC.SrcSpanAnn (GHC.ApiAnn (GHC.Anchor (GHC.realSrcSpan l) (GHC.MovedAnchor dp)) mempty []) l) a)
setEntryDP' (GHC.L (GHC.SrcSpanAnn (GHC.ApiAnn (GHC.Anchor r _) an cs) l) a) dp
  = (GHC.L (GHC.SrcSpanAnn (GHC.ApiAnn (GHC.Anchor r (GHC.MovedAnchor dp)) an cs) l) a)

-- |Set the true entry 'GHC.DeltaPos' from the annotation for a given AST
-- element. This is the 'GHC.DeltaPos' ignoring any comments.
setEntryDP :: (Data a) => GHC.LocatedA a -> GHC.DeltaPos -> Anns -> Anns
setEntryDP ast dp anns = anns
-- setEntryDP ast dp anns =
--   case Map.lookup (mkAnnKey ast) anns of
--     Nothing  -> Map.insert (mkAnnKey ast) (annNone { annEntryDelta = dp}) anns
--     Just ann -> Map.insert (mkAnnKey ast) (ann'    { annEntryDelta = annCommentEntryDelta ann' dp}) anns
--       where
--         ann' = setCommentEntryDP ann dp

-- ---------------------------------------------------------------------

-- |When setting an entryDP, the leading comment needs to be adjusted too
setCommentEntryDP :: Annotation -> GHC.DeltaPos -> Annotation
-- setCommentEntryDP ann dp = error $ "setCommentEntryDP:ann'=" ++ show ann'
setCommentEntryDP ann dp = ann'
  where
    ann' = case (annPriorComments ann) of
      [] -> ann
      [(pc,_)]     -> ann { annPriorComments = [(pc,dp)] }
      ((pc,_):pcs) -> ann { annPriorComments = ((pc,dp):pcs) }

-- ---------------------------------------------------------------------

-- |Take the annEntryDelta associated with the first item and associate it with the second.
-- Also transfer any comments occuring before it.
transferEntryDP :: (Data a, Data b) => GHC.LocatedA a -> GHC.LocatedA b -> Anns -> Anns
transferEntryDP a b anns = anns
-- transferEntryDP a b anns = (const anns2) anns
--   where
--     maybeAnns = do -- Maybe monad
--       anA <- Map.lookup (mkAnnKey a) anns
--       anB <- Map.lookup (mkAnnKey b) anns
--       let anB'  = Ann
--             { annEntryDelta        = GHC.DP (0,0) -- Need to adjust for comments after
--             , annPriorComments     = annPriorComments     anB
--             , annFollowingComments = annFollowingComments anB
--             , annsDP               = annsDP          anB
--             , annSortKey           = annSortKey      anB
--             , annCapturedSpan      = annCapturedSpan anB
--             }
--       return ((Map.insert (mkAnnKey b) anB' anns),annLeadingCommentEntryDelta anA)
--     (anns',dp) = fromMaybe
--                   (error $ "transferEntryDP: lookup failed (a,b)=" ++ show (mkAnnKey a,mkAnnKey b))
--                   maybeAnns
--     anns2 = setEntryDP b dp anns'

-- ---------------------------------------------------------------------

addTrailingComma :: (Data a) => GHC.Located a -> GHC.DeltaPos -> Anns -> Anns
addTrailingComma a dp anns =
  case Map.lookup (mkAnnKey a) anns of
    Nothing -> anns
    Just an ->
      case find isAnnComma (annsDP an) of
        Nothing -> Map.insert (mkAnnKey a) (an { annsDP = annsDP an ++ [(G GHC.AnnComma,dp)]}) anns
        Just _  -> anns
      where
        isAnnComma (G GHC.AnnComma,_) = True
        isAnnComma _                  = False

-- ---------------------------------------------------------------------

removeTrailingComma :: (Data a) => GHC.Located a -> Anns -> Anns
removeTrailingComma a anns =
  case Map.lookup (mkAnnKey a) anns of
    Nothing -> anns
    Just an ->
      case find isAnnComma (annsDP an) of
        Nothing -> anns
        Just _  -> Map.insert (mkAnnKey a) (an { annsDP = filter (not.isAnnComma) (annsDP an) }) anns
      where
        isAnnComma (G GHC.AnnComma,_) = True
        isAnnComma _                  = False

-- ---------------------------------------------------------------------

-- |The relatavise phase puts all comments appearing between the end of one AST
-- item and the beginning of the next as 'annPriorComments' for the second one.
-- This function takes two adjacent AST items and moves any 'annPriorComments'
-- from the second one to the 'annFollowingComments' of the first if they belong
-- to it instead. This is typically required before deleting or duplicating
-- either of the AST elements.
balanceComments :: (Data a,Data b,Monad m) => GHC.LocatedA a -> GHC.LocatedA b -> TransformT m ()
balanceComments first second = do
  -- ++AZ++ : replace the nested casts with appropriate gmapM
  -- logTr $ "balanceComments entered"
  -- logDataWithAnnsTr "first" first
  case cast first :: Maybe (GHC.LHsDecl GHC.GhcPs) of
    Just (GHC.L l (GHC.ValD _ fb@(GHC.FunBind{}))) -> do
      balanceCommentsFB (GHC.L l fb) second
    _ -> case cast first :: Maybe (GHC.LHsBind GHC.GhcPs) of
      Just fb'@(GHC.L _ (GHC.FunBind{})) -> do
        balanceCommentsFB fb' second
      _ -> balanceComments' first second

-- |Prior to moving an AST element, make sure any trailing comments belonging to
-- it are attached to it, and not the following element. Of necessity this is a
-- heuristic process, to be tuned later. Possibly a variant should be provided
-- with a passed-in decision function.
balanceComments' :: (Data a,Data b,Monad m) => GHC.LocatedA a -> GHC.LocatedA b -> TransformT m ()
balanceComments' first second = do
  -- let
  --   k1 = mkAnnKey first
  --   k2 = mkAnnKey second
  --   moveComments p ans = ans'
  --     where
  --       an1 = gfromJust "balanceComments' k1" $ Map.lookup k1 ans
  --       an2 = gfromJust "balanceComments' k2" $ Map.lookup k2 ans
  --       cs1f = annFollowingComments an1
  --       cs2b = annPriorComments an2
  --       (move,stay) = break p cs2b
  --       an1' = an1 { annFollowingComments = cs1f ++ move}
  --       an2' = an2 { annPriorComments = stay}
  --       ans' = Map.insert k1 an1' $ Map.insert k2 an2' ans

  --   simpleBreak (_,GHC.DP (r,_c)) = r > 0

  -- modifyAnnsT (moveComments simpleBreak)
  return ()

-- |Once 'balanceComments' has been called to move trailing comments to a
-- 'GHC.FunBind', these need to be pushed down from the top level to the last
-- 'GHC.Match' if that 'GHC.Match' needs to be manipulated.
balanceCommentsFB :: (Data b,Monad m)
  => GHC.LHsBind GHC.GhcPs -> GHC.LocatedA b -> TransformT m ()
balanceCommentsFB (GHC.L _ (GHC.FunBind _ _ (GHC.MG _ (GHC.L _ matches) _) _)) second = do
  -- logTr $ "balanceCommentsFB entered"
  balanceComments' (last matches) second
balanceCommentsFB f s = balanceComments' f s

-- ---------------------------------------------------------------------


-- |After moving an AST element, make sure any comments that may belong
-- with the following element in fact do. Of necessity this is a heuristic
-- process, to be tuned later. Possibly a variant should be provided with a
-- passed-in decision function.
balanceTrailingComments :: (Monad m) => (Data a,Data b) => GHC.Located a -> GHC.Located b
                        -> TransformT m [(Comment, GHC.DeltaPos)]
balanceTrailingComments first second = do
  let
    k1 = mkAnnKey first
    k2 = mkAnnKey second
    moveComments p ans = (ans',move)
      where
        an1 = gfromJust "balanceTrailingComments k1" $ Map.lookup k1 ans
        an2 = gfromJust "balanceTrailingComments k2" $ Map.lookup k2 ans
        cs1f = annFollowingComments an1
        (move,stay) = break p cs1f
        an1' = an1 { annFollowingComments = stay }
        ans' = Map.insert k1 an1' $ Map.insert k2 an2 ans

    simpleBreak (_,GHC.DP (r,_c)) = r > 0

  ans <- getAnnsT
  let (ans',mov) = moveComments simpleBreak ans
  putAnnsT ans'
  return mov

-- ---------------------------------------------------------------------

-- ++AZ++ TODO: This needs to be renamed/reworked, based on what it actually gets used for
-- |Move any 'annFollowingComments' values from the 'Annotation' associated to
-- the first parameter to that of the second.
moveTrailingComments :: (Data a,Data b)
                     => GHC.Located a -> GHC.Located b -> Transform ()
moveTrailingComments first second = do
  let
    k1 = mkAnnKey first
    k2 = mkAnnKey second
    moveComments ans = ans'
      where
        an1 = gfromJust "moveTrailingComments k1" $ Map.lookup k1 ans
        an2 = gfromJust "moveTrailingComments k2" $ Map.lookup k2 ans
        cs1f = annFollowingComments an1
        cs2f = annFollowingComments an2
        an1' = an1 { annFollowingComments = [] }
        an2' = an2 { annFollowingComments = cs1f ++ cs2f }
        ans' = Map.insert k1 an1' $ Map.insert k2 an2' ans

  modifyAnnsT moveComments

-- ---------------------------------------------------------------------

-- |Insert a declaration into an AST element having sub-declarations
-- (@HasDecls@) according to the given location function.
insertAt :: (HasDecls ast)
              => (GHC.LHsDecl GHC.GhcPs
                  -> [GHC.LHsDecl GHC.GhcPs]
                  -> [GHC.LHsDecl GHC.GhcPs])
              -> ast
              -> GHC.LHsDecl GHC.GhcPs
              -> Transform ast
insertAt f t decl = do
  oldDecls <- hsDecls t
  replaceDecls t (f decl oldDecls)

-- |Insert a declaration at the beginning or end of the subdecls of the given
-- AST item
insertAtStart, insertAtEnd :: (HasDecls ast)
              => ast
              -> GHC.LHsDecl GHC.GhcPs
              -> Transform ast

insertAtStart = insertAt (:)
insertAtEnd   = insertAt (\x xs -> xs ++ [x])

-- |Insert a declaration at a specific location in the subdecls of the given
-- AST item
insertAfter, insertBefore :: (HasDecls (GHC.LocatedA ast))
                          => GHC.LocatedA old
                          -> GHC.LocatedA ast
                          -> GHC.LHsDecl GHC.GhcPs
                          -> Transform (GHC.LocatedA ast)
insertAfter (GHC.getLocA -> k) = insertAt findAfter
  where
    findAfter x xs =
      let (fs, b:bs) = span (\(GHC.L l _) -> GHC.locA l /= k) xs
      in fs ++ (b : x : bs)
insertBefore (GHC.getLocA -> k) = insertAt findBefore
  where
    findBefore x xs =
      let (fs, bs) = span (\(GHC.L l _) -> GHC.locA l /= k) xs
      in fs ++ (x : bs)

-- =====================================================================
-- start of HasDecls instances
-- =====================================================================

-- |Provide a means to get and process the immediate child declartions of a
-- given AST element.
class (Data t) => HasDecls t where
-- ++AZ++: TODO: add tests to confirm that hsDecls followed by replaceDecls is idempotent

    -- | Return the 'GHC.HsDecl's that are directly enclosed in the
    -- given syntax phrase. They are always returned in the wrapped 'GHC.HsDecl'
    -- form, even if orginating in local decls. This is safe, as annotations
    -- never attach to the wrapper, only to the wrapped item.
    hsDecls :: (Monad m) => t -> TransformT m [GHC.LHsDecl GHC.GhcPs]

    -- | Replace the directly enclosed decl list by the given
    --  decl list. Runs in the 'Transform' monad to be able to update list order
    --  annotations, and rebalance comments and other layout changes as needed.
    --
    -- For example, a call on replaceDecls for a wrapped 'GHC.FunBind' having no
    -- where clause will convert
    --
    -- @
    -- -- |This is a function
    -- foo = x -- comment1
    -- @
    -- in to
    --
    -- @
    -- -- |This is a function
    -- foo = x -- comment1
    --   where
    --     nn = 2
    -- @
    replaceDecls :: (Monad m) => t -> [GHC.LHsDecl GHC.GhcPs] -> TransformT m t

-- ---------------------------------------------------------------------

instance HasDecls GHC.ParsedSource where
  hsDecls (GHC.L _ (GHC.HsModule _ _lo _mn _exps _imps decls _ _)) = return decls
  replaceDecls m@(GHC.L l (GHC.HsModule a lo mn exps imps _decls deps haddocks)) decls
    = do
        logTr "replaceDecls LHsModule"
        -- modifyAnnsT (captureOrder m decls)
        return (GHC.L l (GHC.HsModule a lo mn exps imps decls deps haddocks))

-- ---------------------------------------------------------------------

instance HasDecls (GHC.LocatedA (GHC.Match GHC.GhcPs (GHC.LocatedA (GHC.HsExpr GHC.GhcPs)))) where
  hsDecls d@(GHC.L _ (GHC.Match _ _ _ (GHC.GRHSs _ _ lb))) = do
    decls <- hsDeclsValBinds lb
    orderedDecls d decls
  hsDecls (GHC.L _ (GHC.Match _ _ _ (GHC.XGRHSs _))) = return []
  hsDecls (GHC.L _ (GHC.XMatch _))                   = return []

  replaceDecls m@(GHC.L l (GHC.Match xm c p (GHC.GRHSs xr rhs binds))) []
    = do
        logTr "replaceDecls LMatch"
        let
          noWhere (G GHC.AnnWhere,_) = False
          noWhere _                  = True

          removeWhere mkds =
            error "TBD"
            -- case Map.lookup (mkAnnKey m) mkds of
            --   Nothing -> error "wtf"
            --   Just ann -> Map.insert (mkAnnKey m) ann1 mkds
            --     where
            --       ann1 = ann { annsDP = filter noWhere (annsDP ann)
            --                      }
        modifyAnnsT removeWhere

        binds'' <- replaceDeclsValbinds binds []
        -- let binds' = GHC.L (GHC.getLoc binds) binds''
        return (GHC.L l (GHC.Match xm c p (GHC.GRHSs xr rhs binds'')))

  replaceDecls m@(GHC.L l (GHC.Match xm c p (GHC.GRHSs xr rhs binds))) newBinds
    = do
        logTr "replaceDecls LMatch"
        -- Need to throw in a fresh where clause if the binds were empty,
        -- in the annotations.
        case binds of
          GHC.EmptyLocalBinds{} -> do
            let
              addWhere mkds =
                error "TBD"
                -- case Map.lookup (mkAnnKey m) mkds of
                --   Nothing -> error "wtf"
                --   Just ann -> Map.insert (mkAnnKey m) ann1 mkds
                --     where
                --       ann1 = ann { annsDP = annsDP ann ++ [(G GHC.AnnWhere,GHC.DP (1,2))]
                --                  }
            modifyAnnsT addWhere
            modifyAnnsT (setPrecedingLines (ghead "LMatch.replaceDecls" newBinds) 1 4)

            -- only move the comment if the original where clause was empty.
            -- toMove <- balanceTrailingComments m m
            -- insertCommentBefore (mkAnnKey m) toMove (matchApiAnn GHC.AnnWhere)
            return ()
          _ -> return ()

        -- modifyAnnsT (captureOrderAnnKey (mkAnnKey m) newBinds)
        binds'' <- replaceDeclsValbinds binds newBinds
        -- let binds' = GHC.L (GHC.getLoc binds) binds''
        -- logDataWithAnnsTr "Match.replaceDecls:binds'" binds'
        return (GHC.L l (GHC.Match xm c p (GHC.GRHSs xr rhs binds'')))
  replaceDecls (GHC.L _ (GHC.Match _ _ _ (GHC.XGRHSs _))) _ = error "replaceDecls"
  replaceDecls (GHC.L _ (GHC.XMatch _)) _                   = error "replaceDecls"

-- ---------------------------------------------------------------------

instance HasDecls (GHC.LocatedA (GHC.HsExpr GHC.GhcPs)) where
  hsDecls ls@(GHC.L _ (GHC.HsLet _ decls _ex)) = do
    ds <- hsDeclsValBinds decls
    orderedDecls ls ds
  hsDecls _                               = return []

  replaceDecls e@(GHC.L l (GHC.HsLet x decls ex)) newDecls
    = do
        logTr "replaceDecls HsLet"
        modifyAnnsT (captureOrder e newDecls)
        decls'' <- replaceDeclsValbinds decls newDecls
        -- let decls' = GHC.L (GHC.getLoc decls) decls''
        return (GHC.L l (GHC.HsLet x decls'' ex))

  replaceDecls (GHC.L l (GHC.HsPar x e)) newDecls
    = do
        logTr "replaceDecls HsPar"
        e' <- replaceDecls e newDecls
        return (GHC.L l (GHC.HsPar x e'))
  replaceDecls old _new = error $ "replaceDecls (GHC.LHsExpr GHC.GhcPs) undefined for:" ++ showGhc old

-- ---------------------------------------------------------------------

-- | Extract the immediate declarations for a 'GHC.PatBind' wrapped in a 'GHC.ValD'. This
-- cannot be a member of 'HasDecls' because a 'GHC.FunBind' is not idempotent
-- for 'hsDecls' \/ 'replaceDecls'. 'hsDeclsPatBindD' \/ 'replaceDeclsPatBindD' is
-- idempotent.
hsDeclsPatBindD :: (Monad m) => GHC.LHsDecl GHC.GhcPs -> TransformT m [GHC.LHsDecl GHC.GhcPs]
hsDeclsPatBindD (GHC.L l (GHC.ValD _ d)) = hsDeclsPatBind (GHC.L l d)
hsDeclsPatBindD x = error $ "hsDeclsPatBindD called for:" ++ showGhc x

-- | Extract the immediate declarations for a 'GHC.PatBind'. This
-- cannot be a member of 'HasDecls' because a 'GHC.FunBind' is not idempotent
-- for 'hsDecls' \/ 'replaceDecls'. 'hsDeclsPatBind' \/ 'replaceDeclsPatBind' is
-- idempotent.
hsDeclsPatBind :: (Monad m) => GHC.LHsBind GHC.GhcPs -> TransformT m [GHC.LHsDecl GHC.GhcPs]
hsDeclsPatBind d@(GHC.L _ (GHC.PatBind _ _ (GHC.GRHSs _ _grhs lb) _)) = do
  decls <- hsDeclsValBinds lb
  orderedDecls d decls
hsDeclsPatBind x = error $ "hsDeclsPatBind called for:" ++ showGhc x

-- -------------------------------------

-- | Replace the immediate declarations for a 'GHC.PatBind' wrapped in a 'GHC.ValD'. This
-- cannot be a member of 'HasDecls' because a 'GHC.FunBind' is not idempotent
-- for 'hsDecls' \/ 'replaceDecls'. 'hsDeclsPatBindD' \/ 'replaceDeclsPatBindD' is
-- idempotent.
replaceDeclsPatBindD :: (Monad m) => GHC.LHsDecl GHC.GhcPs -> [GHC.LHsDecl GHC.GhcPs]
                     -> TransformT m (GHC.LHsDecl GHC.GhcPs)
replaceDeclsPatBindD (GHC.L l (GHC.ValD x d)) newDecls = do
  (GHC.L _ d') <- replaceDeclsPatBind (GHC.L l d) newDecls
  return (GHC.L l (GHC.ValD x d'))
replaceDeclsPatBindD x _ = error $ "replaceDeclsPatBindD called for:" ++ showGhc x

-- | Replace the immediate declarations for a 'GHC.PatBind'. This
-- cannot be a member of 'HasDecls' because a 'GHC.FunBind' is not idempotent
-- for 'hsDecls' \/ 'replaceDecls'. 'hsDeclsPatBind' \/ 'replaceDeclsPatBind' is
-- idempotent.
replaceDeclsPatBind :: (Monad m) => GHC.LHsBind GHC.GhcPs -> [GHC.LHsDecl GHC.GhcPs]
                    -> TransformT m (GHC.LHsBind GHC.GhcPs)
replaceDeclsPatBind p@(GHC.L l (GHC.PatBind x a (GHC.GRHSs xr rhss binds) b)) newDecls
    = do
        logTr "replaceDecls PatBind"
        -- Need to throw in a fresh where clause if the binds were empty,
        -- in the annotations.
        case binds of
          GHC.EmptyLocalBinds{} -> do
            let
              addWhere mkds =
                error "TBD"
                -- case Map.lookup (mkAnnKey p) mkds of
                --   Nothing -> error "wtf"
                --   Just ann -> Map.insert (mkAnnKey p) ann1 mkds
                --     where
                --       ann1 = ann { annsDP = annsDP ann ++ [(G GHC.AnnWhere,GHC.DP (1,2))]
                --                  }
            modifyAnnsT addWhere
            modifyAnnsT (setPrecedingLines (ghead "LMatch.replaceDecls" newDecls) 1 4)

          _ -> return ()

        -- modifyAnnsT (captureOrderAnnKey (mkAnnKey p) newDecls)
        binds'' <- replaceDeclsValbinds binds newDecls
        -- let binds' = GHC.L (GHC.getLoc binds) binds''
        return (GHC.L l (GHC.PatBind x a (GHC.GRHSs xr rhss binds'') b))
replaceDeclsPatBind x _ = error $ "replaceDeclsPatBind called for:" ++ showGhc x

-- ---------------------------------------------------------------------

instance HasDecls (GHC.LocatedA (GHC.Stmt GHC.GhcPs (GHC.LocatedA (GHC.HsExpr GHC.GhcPs)))) where
  hsDecls ls@(GHC.L _ (GHC.LetStmt _ lb)) = do
    decls <- hsDeclsValBinds lb
    orderedDecls ls decls
  hsDecls (GHC.L _ (GHC.LastStmt _ e _ _))    = hsDecls e
  hsDecls (GHC.L _ (GHC.BindStmt _ _pat e))   = hsDecls e
  hsDecls (GHC.L _ (GHC.BodyStmt _ e _ _))    = hsDecls e
  hsDecls _                                   = return []

  replaceDecls s@(GHC.L l (GHC.LetStmt x lb)) newDecls
    = do
        modifyAnnsT (captureOrder s newDecls)
        lb'' <- replaceDeclsValbinds lb newDecls
        -- let lb' = GHC.L (GHC.getLoc lb) lb''
        return (GHC.L l (GHC.LetStmt x lb''))
  replaceDecls (GHC.L l (GHC.LastStmt x e d se)) newDecls
    = do
        e' <- replaceDecls e newDecls
        return (GHC.L l (GHC.LastStmt x e' d se))
  replaceDecls (GHC.L l (GHC.BindStmt x pat e)) newDecls
    = do
      e' <- replaceDecls e newDecls
      return (GHC.L l (GHC.BindStmt x pat e'))

  replaceDecls (GHC.L l (GHC.BodyStmt x e a b)) newDecls
    = do
      e' <- replaceDecls e newDecls
      return (GHC.L l (GHC.BodyStmt x e' a b))
  replaceDecls x _newDecls = return x

-- =====================================================================
-- end of HasDecls instances
-- =====================================================================

-- ---------------------------------------------------------------------

-- |Do a transformation on an AST fragment by providing a function to process
-- the general case and one specific for a 'GHC.LHsBind'. This is required
-- because a 'GHC.FunBind' may have multiple 'GHC.Match' items, so we cannot
-- gurantee that 'replaceDecls' after 'hsDecls' is idempotent.
hasDeclsSybTransform :: (Data t2,Monad m)
       => (forall t. HasDecls t => t -> m t)
             -- ^Worker function for the general case
       -> (GHC.LHsBind GHC.GhcPs -> m (GHC.LHsBind GHC.GhcPs))
             -- ^Worker function for FunBind/PatBind
       -> t2 -- ^Item to be updated
       -> m t2
hasDeclsSybTransform workerHasDecls workerBind t = trf t
  where
    trf = mkM   parsedSource
         `extM` lmatch
         `extM` lexpr
         `extM` lstmt
         `extM` lhsbind
         `extM` lvald

    parsedSource (p::GHC.ParsedSource) = workerHasDecls p

    lmatch (lm::GHC.LMatch GHC.GhcPs (GHC.LHsExpr GHC.GhcPs))
      = workerHasDecls lm

    lexpr (le::GHC.LHsExpr GHC.GhcPs)
      = workerHasDecls le

    lstmt (d::GHC.LStmt GHC.GhcPs (GHC.LHsExpr GHC.GhcPs))
      = workerHasDecls d

    lhsbind (b@(GHC.L _ GHC.FunBind{}):: GHC.LHsBind GHC.GhcPs)
      = workerBind b
    lhsbind b@(GHC.L _ GHC.PatBind{})
      = workerBind b
    lhsbind x = return x

    lvald (GHC.L l (GHC.ValD x d)) = do
      (GHC.L _ d') <- lhsbind (GHC.L l d)
      return (GHC.L l (GHC.ValD x d'))
    lvald x = return x

-- ---------------------------------------------------------------------

-- |A 'GHC.FunBind' wraps up one or more 'GHC.Match' items. 'hsDecls' cannot
-- return anything for these as there is not meaningful 'replaceDecls' for it.
-- This function provides a version of 'hsDecls' that returns the 'GHC.FunBind'
-- decls too, where they are needed for analysis only.
hsDeclsGeneric :: (Data t,Monad m) => t -> TransformT m [GHC.LHsDecl GHC.GhcPs]
hsDeclsGeneric t = q t
  where
    q = return []
        `mkQ`  parsedSource
        `extQ` lmatch
        `extQ` lexpr
        `extQ` lstmt
        `extQ` lhsbind
        `extQ` lhsbindd
        `extQ` llocalbinds
        `extQ` localbinds

    parsedSource (p::GHC.ParsedSource) = hsDecls p

    lmatch (lm::GHC.LMatch GHC.GhcPs (GHC.LHsExpr GHC.GhcPs)) = hsDecls lm

    lexpr (le::GHC.LHsExpr GHC.GhcPs) = hsDecls le

    lstmt (d::GHC.LStmt GHC.GhcPs (GHC.LHsExpr GHC.GhcPs)) = hsDecls d

    -- ---------------------------------

    lhsbind :: (Monad m) => GHC.LHsBind GHC.GhcPs -> TransformT m [GHC.LHsDecl GHC.GhcPs]
    lhsbind (GHC.L _ (GHC.FunBind _ _ (GHC.MG _ (GHC.L _ matches) _) _)) = do
        dss <- mapM hsDecls matches
        return (concat dss)
    lhsbind p@(GHC.L _ (GHC.PatBind{})) = do
      hsDeclsPatBind p
    lhsbind _ = return []

    -- ---------------------------------

    lhsbindd (GHC.L l (GHC.ValD _ d)) = lhsbind (GHC.L l d)
    lhsbindd _ = return []

    -- ---------------------------------

    llocalbinds :: (Monad m) => GHC.Located (GHC.HsLocalBinds GHC.GhcPs) -> TransformT m [GHC.LHsDecl GHC.GhcPs]
    llocalbinds (GHC.L _ ds) = localbinds ds

    -- ---------------------------------

    localbinds :: (Monad m) => GHC.HsLocalBinds GHC.GhcPs -> TransformT m [GHC.LHsDecl GHC.GhcPs]
    localbinds d = hsDeclsValBinds d

-- ---------------------------------------------------------------------

-- |Look up the annotated order and sort the decls accordingly
orderedDecls :: (Data a,Monad m)
             => GHC.LocatedA a -> [GHC.LHsDecl GHC.GhcPs] -> TransformT m [GHC.LHsDecl GHC.GhcPs]
orderedDecls parent decls = do
  ans <- getAnnsT
  -- case getAnnotationEP parent ans of
  case Nothing of
    Nothing -> error $ "orderedDecls:no annotation for:" ++ showAst parent
    Just ann -> case annSortKey ann of
      Nothing -> do
        return decls
      Just keys -> do
        let ds = map (\s -> (rs $ GHC.getLocA s,s)) decls
            ordered = map snd $ orderByKey ds keys
        return ordered

-- ---------------------------------------------------------------------

-- | Utility function for extracting decls from 'GHC.HsLocalBinds'. Use with
-- care, as this does not necessarily return the declarations in order, the
-- ordering should be done by the calling function from the 'GHC.HsLocalBinds'
-- context in the AST.
hsDeclsValBinds :: (Monad m) => GHC.HsLocalBinds GHC.GhcPs -> TransformT m [GHC.LHsDecl GHC.GhcPs]
hsDeclsValBinds lb = case lb of
    GHC.HsValBinds _ (GHC.ValBinds _ bs sigs) -> do
      let
        bds = map wrapDecl (GHC.bagToList bs)
        sds = map wrapSig sigs
      return (bds ++ sds)
    GHC.HsValBinds _ (GHC.XValBindsLR _) -> error $ "hsDecls.XValBindsLR not valid"
    GHC.HsIPBinds {}       -> return []
    GHC.EmptyLocalBinds {} -> return []
    GHC.XHsLocalBindsLR {} -> return []

-- | Utility function for returning decls to 'GHC.HsLocalBinds'. Use with
-- care, as this does not manage the declaration order, the
-- ordering should be done by the calling function from the 'GHC.HsLocalBinds'
-- context in the AST.
replaceDeclsValbinds :: (Monad m)
                     => GHC.HsLocalBinds GHC.GhcPs -> [GHC.LHsDecl GHC.GhcPs]
                     -> TransformT m (GHC.HsLocalBinds GHC.GhcPs)
replaceDeclsValbinds _ [] = do
  return (GHC.EmptyLocalBinds GHC.NoExtField)
replaceDeclsValbinds (GHC.HsValBinds _ _b) new
    = do
        logTr "replaceDecls HsLocalBinds"
        let decs = GHC.listToBag $ concatMap decl2Bind new
        let sigs = concatMap decl2Sig new
        return (GHC.HsValBinds GHC.noAnn (GHC.ValBinds GHC.NoAnnSortKey decs sigs))
replaceDeclsValbinds (GHC.HsIPBinds {}) _new    = error "undefined replaceDecls HsIPBinds"
replaceDeclsValbinds (GHC.EmptyLocalBinds _) new
    = do
        logTr "replaceDecls HsLocalBinds"
        let newBinds = map decl2Bind new
            newSigs  = map decl2Sig  new
        let decs = GHC.listToBag $ concat newBinds
        let sigs = concat newSigs
        return (GHC.HsValBinds GHC.noAnn (GHC.ValBinds GHC.NoAnnSortKey decs sigs))
replaceDeclsValbinds (GHC.XHsLocalBindsLR _) _ = error "replaceDeclsValbinds. XHsLocalBindsLR"

-- ---------------------------------------------------------------------

type Decl  = GHC.LocatedA (GHC.HsDecl GHC.GhcPs)
type Match = GHC.LocatedA (GHC.Match GHC.GhcPs (GHC.LocatedA (GHC.HsExpr GHC.GhcPs)))

-- |Modify a 'GHC.LHsBind' wrapped in a 'GHC.ValD'. For a 'GHC.PatBind' the
-- declarations are extracted and returned after modification. For a
-- 'GHC.FunBind' the supplied 'GHC.SrcSpan' is used to identify the specific
-- 'GHC.Match' to be transformed, for when there are multiple of them.
modifyValD :: forall m t. (HasTransform m)
                => GHC.SrcSpan
                -> Decl
                -> (Match -> [Decl] -> m ([Decl], Maybe t))
                -> m (Decl,Maybe t)
modifyValD p pb@(GHC.L ss (GHC.ValD _ (GHC.PatBind {} ))) f =
  if (GHC.locA ss) == p
     then do
       ds <- liftT $ hsDeclsPatBindD pb
       (ds',r) <- f (error "modifyValD.PatBind should not touch Match") ds
       pb' <- liftT $ replaceDeclsPatBindD pb ds'
       return (pb',r)
     else return (pb,Nothing)
modifyValD p ast f = do
  (ast',r) <- runStateT (everywhereM (mkM doModLocal) ast) Nothing
  return (ast',r)
  where
    doModLocal :: Match -> StateT (Maybe t) m Match
    doModLocal  (match@(GHC.L ss _) :: Match) = do
         let
         if (GHC.locA ss) == p
           then do
             ds <- lift $ liftT $ hsDecls match
             (ds',r) <- lift $ f match ds
             put r
             match' <- lift $ liftT $ replaceDecls match ds'
             return match'
           else return match

-- ---------------------------------------------------------------------

-- |Used to integrate a @Transform@ into other Monad stacks
class (Monad m) => (HasTransform m) where
  liftT :: Transform a -> m a

instance Monad m => HasTransform (TransformT m) where
  liftT = hoistTransform (return . runIdentity)

-- ---------------------------------------------------------------------

-- | Apply a transformation to the decls contained in @t@
modifyDeclsT :: (HasDecls t,HasTransform m)
             => ([GHC.LHsDecl GHC.GhcPs] -> m [GHC.LHsDecl GHC.GhcPs])
             -> t -> m t
modifyDeclsT action t = do
  decls <- liftT $ hsDecls t
  decls' <- action decls
  liftT $ replaceDecls t decls'

-- ---------------------------------------------------------------------

matchApiAnn :: GHC.AnnKeywordId -> (KeywordId,GHC.DeltaPos) -> Bool
matchApiAnn mkw (kw,_)
  = case kw of
     (G akw) -> mkw == akw
     _       -> False


-- We comments extracted from annPriorComments or annFollowingComments, which
-- need to move to just before the item identified by the predicate, if it
-- fires, else at the end of the annotations.
insertCommentBefore :: (Monad m) => AnnKey -> [(Comment, GHC.DeltaPos)]
                    -> ((KeywordId, GHC.DeltaPos) -> Bool) -> TransformT m ()
insertCommentBefore key toMove p = do
  -- let
  --   doInsert ans =
  --     case Map.lookup key ans of
  --       Nothing -> error $ "insertCommentBefore:no AnnKey for:" ++ showGhc key
  --       Just ann -> Map.insert key ann' ans
  --         where
  --           (before,after) = break p (annsDP ann)
  --           ann' = ann { annsDP = before ++ (map comment2dp toMove) ++ after}

  -- modifyAnnsT doInsert
  return ()

-- ---------------------------------------------------------------------

