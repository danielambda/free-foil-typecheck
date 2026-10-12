module FreeFoilTypecheck.SystemF.TypecheckGen
  ( Context'
  , AlphaEquiv(..)
  , TypingSig(..), toAST
  , defaultCheckSig
  , TypedPattern(..)
  , bidirectionalCheck
  , bidirectionalInfer
  , Scoped(..)
  , mapBinder
  , TypeError(..)
  , TypedNameBinders(..)
  , TypedAST(..)
  , ScopedTypedAST
  , typeOf
  , CheckInfer(..)
  , ScopedCheckInfer
  , ScopedCheckInfer'(..)
  , shouldBe
  ) where

import Control.Monad (unless)
import Control.Monad.Foil hiding (AlphaEquiv)
import Control.Monad.Free.Foil qualified as FreeFoil (alphaEquiv)
import Control.Monad.Foil.Relative
import Control.Monad.Free.Foil hiding (alphaEquiv)
import Data.Bitraversable (Bitraversable)
import Data.Kind (Type)
import Data.ZipMatchK (ZipMatchK)
import Data.Bifunctor (bimap, Bifunctor)

-- | Main typing signature class
class
  (forall n. Show (TypeError (ty n)), AlphaEquiv ty) =>
  TypingSig binder ty sig
  where
  checkSig ::
    (Distinct n) =>
    Context' ty n ->
    sig (ScopedCheckInfer binder sig ty n) (CheckInfer binder sig ty n) ->
    ty n ->
    Either String (TypedAST binder sig ty n)
  checkSig = defaultCheckSig

  inferSig ::
    (Distinct n) =>
    Context' ty n ->
    sig (ScopedCheckInfer binder sig ty n) (CheckInfer binder sig ty n) ->
    Either String (TypedAST binder sig ty n)

defaultCheckSig ::
  (TypingSig binder ty sig, Distinct n) =>
  Context' ty n ->
  sig (ScopedCheckInfer binder sig ty n) (CheckInfer binder sig ty n) ->
  ty n ->
  Either String (TypedAST binder sig ty n)
defaultCheckSig ctx node expectedType = do
  typedNode <- inferSig ctx node
  unless (alphaEquiv (nameMapToScope ctx) (typeOf typedNode) expectedType) do
    Left (show (TypeErrorUnexpectedType (typeOf typedNode) expectedType))
  pure typedNode

bidirectionalInfer ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  Either String (TypedAST binder sig ty n)
bidirectionalInfer scope t = infer $ bidirectionalCheckInfer scope t

bidirectionalCheck ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    AlphaEquiv ty,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  ty n -> Either String (TypedAST binder sig ty n)
bidirectionalCheck scope t = check $ bidirectionalCheckInfer scope t

bidirectionalCheckInfer ::
  forall ty binder sig n.
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  AST binder sig n ->
  CheckInfer binder sig ty n
bidirectionalCheckInfer scope = \case
  Var n ->
    let inferredType = lookupName n scope
    in CheckInfer
      { infer = pure $ TypedVar n inferredType
      , check = \expectedType -> do
          unless (alphaEquiv (nameMapToScope scope) inferredType expectedType) do
            Left (show (TypeErrorUnexpectedType inferredType expectedType))
          pure $ TypedVar n inferredType
      , getTerm = Var n
      }
  Node node ->
    let node' = bimap
          (bidirectionalCheckInferScoped scope . unScopedAST)
          (bidirectionalCheckInfer scope)
          node
    in CheckInfer
        { infer = inferSig scope node'
        , check = checkSig scope node'
        , getTerm = Node node
        }
bidirectionalCheckInferScoped ::
  ( Distinct n,
    Bifunctor sig,
    TypingSig binder ty sig,
    UnifiablePattern binder,
    SinkableK binder,
    Sinkable ty,
    TypedPattern ty binder
  ) =>
  Context' ty n ->
  Scoped binder (AST binder sig) n ->
  ScopedCheckInfer binder sig ty n
bidirectionalCheckInferScoped scope (Scoped binder body) =
  case (assertExt binder, assertDistinct binder) of
    (Ext, Distinct) -> \mbinderType -> ScopedCheckInfer
      { scopedInfer = do
          ty <- extractTypeFromBinder scope binder mbinderType
          let scope' = sink <$> addNameBinder (extractExactlyOneBinder binder ty) ty scope
          Scoped binder <$> bidirectionalInfer scope' body
      , scopedCheck = \(Scoped binder' expectedType) -> do
          ty <- extractTypeFromBinder scope binder mbinderType
          case unifyPatterns binder binder' of
            SameNameBinders _binders -> do
              let scope' =
                    sink <$> addNameBinder (extractExactlyOneBinder binder ty) ty scope
              let ci = bidirectionalCheckInfer scope' body
              b' <- check ci expectedType
              pure $ Scoped binder b'
            RenameLeftNameBinder _binders renameL ->
              case (assertExt binder', assertDistinct binder') of
                (Ext, Distinct) -> do
                  let scope' = sink <$> addNameBinder (extractExactlyOneBinder binder' ty) ty scope
                  let body' = liftRM (nameMapToScope scope') (fromNameBinderRenaming renameL) body
                  b' <- bidirectionalCheck scope' body' expectedType
                  pure $ Scoped binder' b'
            -- FIXME: RenameRightNameBinder, RenameBothNameBinders
            _ -> Left "non-unifiable patterns"
      }

--------------------------------------------------------------------------------

-- * Core Types

--------------------------------------------------------------------------------

-- | Typing context mapping names to types
type Context' ty n = NameMap n (ty n)

unScopedAST :: ScopedAST binder sig n -> Scoped binder (AST binder sig) n
unScopedAST (ScopedAST binder body) = Scoped binder body

-- | Scoped value with a binder
data Scoped binder (t :: S -> Type) (n :: S) where
  Scoped :: binder n l -> t l -> Scoped binder t n

mapBinder :: (forall x y. binder0 x y -> binder1 x y) -> Scoped binder0 t n -> Scoped binder1 t n
mapBinder f (Scoped bindernl tl) = Scoped (f bindernl) tl

-- | Type errors
data TypeError ty
  = TypeErrorUnexpectedType ty ty
  | TypeErrorUnexpectedDependentType
  deriving (Show)

data TypedAST binder sig ty n where
  TypedVar :: Name n -> ty n -> TypedAST binder sig ty n
  TypedNode ::
    sig (ScopedTypedAST binder sig ty n) (TypedAST binder sig ty n) ->
    ty n ->
    TypedAST binder sig ty n

type ScopedTypedAST binder sig ty n = Scoped binder (TypedAST binder sig ty) n

typeOf :: TypedAST binder sig ty n -> ty n
typeOf (TypedVar _ ty) = ty
typeOf (TypedNode _ ty) = ty

toAST :: (Bifunctor sig) => TypedAST binder sig ty n -> AST binder sig n
toAST (TypedVar n _) = Var n
toAST (TypedNode n _) = Node (bimap toScopedAST toAST n)

toScopedAST :: (Bifunctor sig) => Scoped binder (TypedAST binder sig ty) n -> ScopedAST binder sig n
toScopedAST (Scoped binder typedAST) = ScopedAST binder (toAST typedAST)

data CheckInfer binder sig ty n = CheckInfer
  { check :: ty n -> Either String (TypedAST binder sig ty n)
  , infer :: Either String (TypedAST binder sig ty n)
  , getTerm :: AST binder sig n
  }

-- | Bidirectional check/infer for a scoped subterm.
--
-- The annotation (a 'Maybe' type for the bound variable) is supplied by the
-- parent typing rule. The resulting check/infer actions return the typed body
-- wrapped back in its binder, so the parent rule can recover both.
data ScopedCheckInfer' binder sig ty n = ScopedCheckInfer
  { scopedCheck ::
      Scoped binder ty n ->
      Either String (Scoped binder (TypedAST binder sig ty) n)
  , scopedInfer :: Either String (Scoped binder (TypedAST binder sig ty) n)
  }

type ScopedCheckInfer binder sig ty n = Maybe (ty n) -> ScopedCheckInfer' binder sig ty n

-- | Typed name binders data structure
data TypedNameBinders ty n l where
  TypedNameBindersEmpty :: TypedNameBinders ty n n
  TypedNameBindersCons ::
    NameBinder n i -> ty n -> TypedNameBinders ty i l -> TypedNameBinders ty n l

--------------------------------------------------------------------------------

-- * Required Type Classes

--------------------------------------------------------------------------------

-- | Alpha equivalence class
class AlphaEquiv t where
  alphaEquiv :: (Distinct n) => Scope n -> t n -> t n -> Bool

-- | Default instance for Free Foil ASTs
instance
  (Bitraversable sig, ZipMatchK sig, UnifiablePattern binder, SinkableK binder) =>
  AlphaEquiv (AST binder sig)
  where
  alphaEquiv = FreeFoil.alphaEquiv

-- | Class for typed patterns
class TypedPattern ty pat where
  extractPatternType :: pat n l -> Maybe (ty n)
  extractTypedBinders :: pat n l -> ty n -> TypedNameBinders ty n l

--------------------------------------------------------------------------------

-- * Generic Utilities

--------------------------------------------------------------------------------

-- | Extract type from a binder
extractTypeFromBinder ::
  (TypedPattern ty binder, AlphaEquiv ty, Distinct n) =>
  Context' ty n ->
  binder n l ->
  Maybe (ty n) ->
  Either String (ty n)
extractTypeFromBinder _scope binder Nothing =
  maybe (Left "cannot infer without type annotation for pattern") Right $
    extractPatternType binder
extractTypeFromBinder scope binder (Just ty) =
  case extractPatternType binder of
    Nothing -> Right ty
    Just binderTy ->
      if alphaEquiv (nameMapToScope scope) binderTy ty
        then Right ty
        else Left "type mismatch"

--------------------------------------------------------------------------------

-- * Main Bidirectional Type Checking API

--------------------------------------------------------------------------------

extractExactlyOneBinder :: TypedPattern ty pat => pat n l -> ty n -> NameBinder n l
extractExactlyOneBinder binder ty =
  case extractTypedBinders binder ty of
    TypedNameBindersCons extractedBinder _ty TypedNameBindersEmpty -> extractedBinder
    _ -> error "Expected exactly one binder"

shouldBe ::
  (AlphaEquiv ty, Distinct n, Show (ty n)) =>
  (Context' ty n, ty n) ->
  ty n ->
  Either String ()
shouldBe (scope, actualType) expectedType =
  unless (alphaEquiv (nameMapToScope scope) actualType expectedType) do
    Left $ unlines
      [ "expected type"
      , "  " ++ show expectedType
      , "but got type"
      , "  " ++ show actualType
      , "when typechecking expression"
      ]
