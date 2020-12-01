{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
--
-- (c) The University of Glasgow
--

#include "HsVersions.h"

module GHC.Types.Avail (
    Avails,
    AvailInfo(..),
    avail,
    availField,
    availTC,
    availsToNameSet,
    availsToNameSetWithSelectors,
    availsToNameEnv,
    availExportsDecl,
    availName, availChild,
    availNames, availNonFldNames,
    availNamesWithSelectors,
    availFlds,
    availChildren,
    availSubordinateChildren,
    stableAvailCmp,
    plusAvail,
    trimAvail,
    filterAvail,
    filterAvails,
    nubAvails,

    Child(..),
    childName,
    childPrintableName,
    childSrcSpan,
    partitionChildren,
    stableChildCmp,
  ) where

import GHC.Prelude

import GHC.Types.Name
import GHC.Types.Name.Env
import GHC.Types.Name.Set
import GHC.Types.SrcLoc

import GHC.Types.FieldLabel
import GHC.Utils.Binary
import GHC.Data.List.SetOps
import GHC.Utils.Outputable
import GHC.Utils.Panic
import GHC.Utils.Misc

import Data.Data ( Data )
import Data.Either ( partitionEithers )
import Data.List ( find )
import Data.Maybe

-- -----------------------------------------------------------------------------
-- The AvailInfo type

-- | Records what things are \"available\", i.e. in scope
data AvailInfo

  -- | An ordinary identifier in scope, or a field label without a parent type
  -- (see Note [Representing pattern synonym fields in AvailInfo]).
  = Avail Child

  -- | A type or class in scope
  --
  -- The __AvailTC Invariant__: If the type or class is itself to be in scope,
  -- it must be /first/ in this list.  Thus, typically:
  --
  -- > AvailTC Eq [Eq, ==, \/=]
  | AvailTC
       Name         -- ^ The name of the type or class
       [Child]      -- ^ The available pieces of type or class
                    -- (see Note [Representing fields in AvailInfo]).

   deriving ( Eq    -- ^ Used when deciding if the interface has changed
            , Data )

-- | A collection of 'AvailInfo' - several things that are \"available\"
type Avails = [AvailInfo]

{-
Note [Representing fields in AvailInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
See also Note [FieldLabel] in GHC.Types.FieldLabel.

When -XDuplicateRecordFields is disabled (the normal case), a
datatype like

  data T = MkT { foo :: Int }

gives rise to the AvailInfo

  AvailTC T [T, MkT, FieldLabel "foo" False foo]

whereas if -XDuplicateRecordFields is enabled it gives

  AvailTC T [T, MkT, FieldLabel "foo" True $sel:foo:MkT]

since the label does not match the selector name.

The labels in a field list are not necessarily unique:
data families allow the same parent (the family tycon) to have
multiple distinct fields with the same label. For example,

  data family F a
  data instance F Int  = MkFInt { foo :: Int }
  data instance F Bool = MkFBool { foo :: Bool}

gives rise to

  AvailTC F [ F, MkFInt, MkFBool
            , FieldLabel "foo" True $sel:foo:MkFInt
            , FieldLabel "foo" True $sel:foo:MkFBool ]

Moreover, note that the flIsOverloaded flag need not be the same for
all the elements of the list.  In the example above, this occurs if
the two data instances are defined in different modules, one with
`-XDuplicateRecordFields` enabled and one with it disabled.  Thus it
is possible to have

  AvailTC F [ F, MkFInt, MkFBool
            , FieldLabel "foo" True $sel:foo:MkFInt
            , FieldLabel "foo" False foo ]

If the two data instances are defined in different modules, both
without `-XDuplicateRecordFields`, it will be impossible to export
them from the same module (even with `-XDuplicateRecordfields`
enabled), because they would be represented identically.  The
workaround here is to enable `-XDuplicateRecordFields` on the defining
modules.


Note [Representing pattern synonym fields in AvailInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Record pattern synonym fields cannot be represented using AvailTC like fields of
normal record types (see Note [Representing fields in AvailInfo]), because they
do not always have a parent type constructor.  Thus we represent them using the
AvailFL constructor, which carries the underlying FieldLabel.

Thus under -XDuplicateRecordFields -XPatternSynoynms, the declaration

  pattern MkFoo{f} = Bar f

gives rise to the AvailInfo

  Avail (ChildName MkFoo)
  Avail (ChildField (FieldLabel "f" True $sel:f:MkFoo))

However, if `f` is bundled with a type constructor `T` by using `T(MkFoo,f)` in
an export list, then whenever `f` is imported the parent will be `T`,
represented as

  AvailTC T [ ChildName T
            , ChildName MkFoo
            , ChildField (FieldLabel "f" True $sel:f:MkFoo) ]

-}

-- | Compare lexicographically
stableAvailCmp :: AvailInfo -> AvailInfo -> Ordering
stableAvailCmp (Avail c1)     (Avail c2)     = c1 `stableChildCmp` c2
stableAvailCmp (Avail {})     (AvailTC {})   = LT
stableAvailCmp (AvailTC n ns) (AvailTC m ms) = (n `stableNameCmp` m) `thenCmp`
                                               (cmpList stableChildCmp ns ms)
stableAvailCmp (AvailTC {})   (Avail {})     = GT

stableChildCmp :: Child -> Child -> Ordering
stableChildCmp (ChildName  n1) (ChildName  n2) = n1 `stableNameCmp` n2
stableChildCmp (ChildName  {}) (ChildField {}) = LT
stableChildCmp (ChildField f1) (ChildField f2) = flSelector f1 `stableNameCmp` flSelector f2
stableChildCmp (ChildField {}) (ChildName  {}) = GT

avail :: Name -> AvailInfo
avail n = Avail (ChildName n)

availField :: FieldLabel -> AvailInfo
availField fl = Avail (ChildField fl)

availTC :: Name -> [Name] -> [FieldLabel] -> AvailInfo
availTC n ns fls = AvailTC n (map ChildName ns ++ map ChildField fls)


-- -----------------------------------------------------------------------------
-- Operations on AvailInfo

availsToNameSet :: [AvailInfo] -> NameSet
availsToNameSet avails = foldr add emptyNameSet avails
      where add avail set = extendNameSetList set (availNames avail)

availsToNameSetWithSelectors :: [AvailInfo] -> NameSet
availsToNameSetWithSelectors avails = foldr add emptyNameSet avails
      where add avail set = extendNameSetList set (availNamesWithSelectors avail)

availsToNameEnv :: [AvailInfo] -> NameEnv AvailInfo
availsToNameEnv avails = foldr add emptyNameEnv avails
     where add avail env = extendNameEnvList env
                                (zip (availNames avail) (repeat avail))

-- | Does this 'AvailInfo' export the parent decl?  This depends on the
-- invariant that the parent is first if it appears at all.
availExportsDecl :: AvailInfo -> Bool
availExportsDecl (AvailTC ty_name names)
  | n : _ <- names = ChildName ty_name == n
  | otherwise      = False
availExportsDecl _ = True

-- | Just the main name made available, i.e. not the available pieces
-- of type or class brought into scope by the 'AvailInfo'
availName :: AvailInfo -> Name
availName (Avail n)     = childName n
availName (AvailTC n _) = n

availChild :: AvailInfo -> Child
availChild (Avail c) = c
availChild (AvailTC n _) = ChildName n

-- | All names made available by the availability information (excluding overloaded selectors)
availNames :: AvailInfo -> [Name]
availNames (Avail c) = childNonOverloadedNames c
availNames (AvailTC _ cs) = concatMap childNonOverloadedNames cs

childNonOverloadedNames :: Child -> [Name]
childNonOverloadedNames (ChildName n) = [n]
childNonOverloadedNames (ChildField fl) = [ flSelector fl | not (flIsOverloaded fl) ]

-- | All names made available by the availability information (including overloaded selectors)
availNamesWithSelectors :: AvailInfo -> [Name]
availNamesWithSelectors (Avail c) = [childName c]
availNamesWithSelectors (AvailTC _ cs) = map childName cs

-- | Names for non-fields made available by the availability information
availNonFldNames :: AvailInfo -> [Name]
availNonFldNames (Avail (ChildName n))   = [n]
availNonFldNames (Avail (ChildField {})) = []
availNonFldNames (AvailTC _ ns) = mapMaybe f ns
  where
    f (ChildName n)   = Just n
    f (ChildField {}) = Nothing

-- | Fields made available by the availability information
availFlds :: AvailInfo -> [FieldLabel]
availFlds (Avail c) = maybeToList (childFieldLabel c)
availFlds (AvailTC _ cs) = mapMaybe childFieldLabel cs

-- | Children made available by the availability information.
availChildren :: AvailInfo -> [Child]
availChildren (Avail c)      = [c]
availChildren (AvailTC _ cs) = cs

-- | Children made available by the availability information, other than the
-- main decl itself.
availSubordinateChildren :: AvailInfo -> [Child]
availSubordinateChildren (Avail {}) = []
availSubordinateChildren avail@(AvailTC _ ns)
  | availExportsDecl avail = tail ns
  | otherwise              = ns


-- | Used where we may have an ordinary name or a record field label.
-- See Note [Children] in GHC.Types.Name.Reader.
data Child = ChildName  Name
           | ChildField FieldLabel
           deriving (Data, Eq)

instance Outputable Child where
  ppr (ChildName   n) = ppr n
  ppr (ChildField fl) = ppr fl

instance HasOccName Child where
  occName (ChildName name) = occName name
  occName (ChildField fl)  = occName fl

childName :: Child -> Name
childName (ChildName name) = name
childName (ChildField fl)  = flSelector fl

-- | A Name for the child suitable for output to the user.  For fields, the
-- OccName will be the field label.  See 'fieldLabelPrintableName'.
childPrintableName :: Child -> Name
childPrintableName (ChildName name) = name
childPrintableName (ChildField fl)  = fieldLabelPrintableName fl

childSrcSpan :: Child -> SrcSpan
childSrcSpan (ChildName name) = nameSrcSpan name
childSrcSpan (ChildField fl)  = nameSrcSpan (flSelector fl)

childFieldLabel :: Child -> Maybe FieldLabel
childFieldLabel (ChildName {})  = Nothing
childFieldLabel (ChildField fl) = Just fl

partitionChildren :: [Child] -> ([Name], [FieldLabel])
partitionChildren = partitionEithers . map to_either
  where
    to_either (ChildName   n) = Left n
    to_either (ChildField fl) = Right fl


-- -----------------------------------------------------------------------------
-- Utility

plusAvail :: AvailInfo -> AvailInfo -> AvailInfo
plusAvail a1 a2
  | debugIsOn && availName a1 /= availName a2
  = pprPanic "GHC.Rename.Env.plusAvail names differ" (hsep [ppr a1,ppr a2])
plusAvail a1@(Avail {})         (Avail {})        = a1
plusAvail (AvailTC _ [])     a2@(AvailTC {})   = a2
plusAvail a1@(AvailTC {})       (AvailTC _ []) = a1
plusAvail (AvailTC n1 (s1:ss1)) (AvailTC n2 (s2:ss2))
  = case (ChildName n1==s1, ChildName n2==s2) of  -- Maintain invariant the parent is first
       (True,True)   -> AvailTC n1 (s1 : (ss1 `unionLists` ss2))
       (True,False)  -> AvailTC n1 (s1 : (ss1 `unionLists` (s2:ss2)))
       (False,True)  -> AvailTC n1 (s2 : ((s1:ss1) `unionLists` ss2))
       (False,False) -> AvailTC n1 ((s1:ss1) `unionLists` (s2:ss2))
plusAvail a1 a2 = pprPanic "GHC.Rename.Env.plusAvail" (hsep [ppr a1,ppr a2])

-- | trims an 'AvailInfo' to keep only a single name
trimAvail :: AvailInfo -> Name -> AvailInfo
trimAvail avail@(Avail {})         _ = avail
trimAvail avail@(AvailTC n ns) m = case find ((== m) . childName) ns of
    Just c  -> AvailTC n [c]
    Nothing -> pprPanic "trimAvail" (hsep [ppr avail, ppr m])

-- | filters 'AvailInfo's by the given predicate
filterAvails  :: (Name -> Bool) -> [AvailInfo] -> [AvailInfo]
filterAvails keep avails = foldr (filterAvail keep) [] avails

-- | filters an 'AvailInfo' by the given predicate
filterAvail :: (Name -> Bool) -> AvailInfo -> [AvailInfo] -> [AvailInfo]
filterAvail keep ie rest =
  case ie of
    Avail c | keep (childName c) -> ie : rest
            | otherwise -> rest
    AvailTC tc cs ->
        let cs' = filter (keep . childName) cs
        in if null cs' then rest else AvailTC tc cs' : rest


-- | Combines 'AvailInfo's from the same family
-- 'avails' may have several items with the same availName
-- E.g  import Ix( Ix(..), index )
-- will give Ix(Ix,index,range) and Ix(index)
-- We want to combine these; addAvail does that
nubAvails :: [AvailInfo] -> [AvailInfo]
nubAvails avails = nameEnvElts (foldl' add emptyNameEnv avails)
  where
    add env avail = extendNameEnv_C plusAvail env (availName avail) avail

-- -----------------------------------------------------------------------------
-- Printing

instance Outputable AvailInfo where
   ppr = pprAvail

pprAvail :: AvailInfo -> SDoc
pprAvail (Avail n)
  = ppr n
pprAvail (AvailTC n ns)
  = ppr n <> braces (fsep (punctuate comma (map ppr ns)))

instance Binary AvailInfo where
    put_ bh (Avail aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (AvailTC ab ac) = do
            putByte bh 1
            put_ bh ab
            put_ bh ac
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (Avail aa)
              _ -> do ab <- get bh
                      ac <- get bh
                      return (AvailTC ab ac)

instance Binary Child where
    put_ bh (ChildName aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (ChildField ab) = do
            putByte bh 1
            put_ bh ab
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (ChildName aa)
              _ -> do ab <- get bh
                      return (ChildField ab)
