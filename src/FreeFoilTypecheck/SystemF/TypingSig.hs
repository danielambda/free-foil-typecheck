{-# OPTIONS_GHC -fno-warn-orphans #-}

module FreeFoilTypecheck.SystemF.TypingSig where

import Control.Monad.Foil hiding (AlphaEquiv)
import Control.Monad.Free.Foil
import FreeFoilTypecheck.SystemF.Syntax
import FreeFoilTypecheck.SystemF.TypecheckGen

deriving instance Show (TermSig (ScopedTypedAST (FoilPattern Term) TermSig Term n) (TypedAST (FoilPattern Term) TermSig Term n))
deriving instance Show (FoilPattern Term n l)
deriving instance Show (TypedAST (FoilPattern Term) TermSig Term n)
deriving instance Show (ScopedTypedAST (FoilPattern Term) TermSig Term n)

--------------------------------------------------------------------------------

-- * TypingSig Instance for System F

--------------------------------------------------------------------------------

instance
  (forall n. Show (TypeError (Term n))) =>
  TypingSig (FoilPattern Term) Term TermSig
  where
  --------------------------------------------------------------------------------
  -- Type Checking Rules
  --------------------------------------------------------------------------------

  checkSig scope = \case
    -- Type abstraction: Γ ⊢ ΛX.t ⇐ ∀X.T
    ETAbsSig body -> \case
      Term (TForAll x bodyType) -> do
        sc <- scopedCheck (body (Just (Term TType))) (Scoped x (Term bodyType))
        pure $ TypedNode (ETAbsSig sc) (Term (TForAll x bodyType))
      _ -> Left "unexpected type abstraction"
    -- Type application
    ETAppSig e t -> \expectedType -> do
      tt <- check t (Term TType)
      et <- infer e
      case typeOf et of
        Term (TForAll (FoilPatternVar x) bodyType) -> do
          let subst = addSubst identitySubst x (toAST tt)
          let actualType = substitute (nameMapToScope scope) subst bodyType
          (scope, Term actualType) `shouldBe` expectedType
          pure $ TypedNode (ETAppSig et tt) (Term actualType)
        _ -> Left "expected a type abstraction"

    -- Lambda abstraction: Γ ⊢ λx:A. t ⇐ A → B
    EAbsSig body -> \case
      Term (TArrow x expectedBodyType) -> do
        Scoped c b <- scopedInfer (body (Just (Term x)))
        case assertDistinct c of
          Distinct -> do
            b' <- unsinkType scope (typeOf b)
            (scope, b') `shouldBe` Term expectedBodyType
            pure $ TypedNode (EAbsSig (Scoped c b)) (Term (TArrow x expectedBodyType))
      t -> Left $ "unexpected abstraction" <> show t
    -- Let binding
    ELetSig e body -> \expectedType -> do
      et <- infer e
      let a = typeOf et
      let scopedExpectedType = withFresh (nameMapToScope scope) \binder ->
            Scoped (FoilPatternVar binder) (sink expectedType)
      Scoped c b <- scopedCheck (body (Just a)) scopedExpectedType
      pure $ TypedNode (ELetSig et (Scoped c b)) expectedType

    -- Default case
    sig -> defaultCheckSig scope sig

  --------------------------------------------------------------------------------
  -- Type Inference Rules
  --------------------------------------------------------------------------------

  inferSig scope = \case
    -- Literals
    ETrueSig -> pure $ TypedNode ETrueSig (Term TBool)
    EFalseSig -> pure $ TypedNode EFalseSig (Term TBool)
    ENatSig n -> pure $ TypedNode (ENatSig n) (Term TNat)
    -- Arithmetic operations
    EAddSig l r -> do
      lt <- check l (Term TNat)
      rt <- check r (Term TNat)
      pure $ TypedNode (EAddSig lt rt) (Term TNat)
    ESubSig l r -> do
      lt <- check l (Term TNat)
      rt <- check r (Term TNat)
      pure $ TypedNode (ESubSig lt rt) (Term TNat)

    -- Conditionals
    EIfSig cond thenBranch elseBranch -> do
      ct <- check cond (Term TBool)
      tt <- infer thenBranch
      let thenType = typeOf tt
      et <- check elseBranch thenType
      pure $ TypedNode (EIfSig ct tt et) thenType

    -- Zero test
    EIsZeroSig e -> do
      et <- check e (Term TNat)
      pure $ TypedNode (EIsZeroSig et) (Term TBool)

    -- Type annotation
    -- t : T
    -- T : Type
    ETypedSig e t -> do
      tt <- check t (Term TType)
      let t' = Term $ toAST tt
      et <- check e t'
      pure $ TypedNode (ETypedSig et tt) t'

    -- Let binding: Γ ⊢ let x = t₁ in t₂ ⇒ T₂
    ELetSig e body -> do
      et <- infer e
      let a = typeOf et
      Scoped c bt <- scopedInfer (body (Just a))
      case assertDistinct c of
        Distinct -> do
          bty <- unsinkType scope (typeOf bt)
          pure $ TypedNode (ELetSig et (Scoped c bt)) bty

    -- For loop
    EForSig e1 e2 body -> do
      e1t <- check e1 (Term TNat)
      e2t <- check e2 (Term TNat)
      Scoped c bt <- scopedInfer (body (Just (Term TNat)))
      case assertDistinct c of
        Distinct -> do
          bty <- unsinkType scope (typeOf bt)
          pure $ TypedNode (EForSig e1t e2t (Scoped c bt)) bty

    -- Function application: Γ ⊢ t₁ t₂ ⇒ B
    EAppSig t1 t2 ->
      infer t1 >>= \tf -> case typeOf tf of
        Term (TArrow a b) -> do
          t2t <- check t2 (Term a)
          pure $ TypedNode (EAppSig tf t2t) (Term b)
        _ -> Left "not a function"

    -- Lambda abstraction (with annotation)
    EAbsSig body -> do
      Scoped binder bbody <- scopedInfer (body Nothing)
      case binder of
        FoilPatternAsc x (Term argType) ->
          case assertDistinct x of
            Distinct -> do
              Term bodyType' <- unsinkType scope (typeOf bbody)
              pure $ TypedNode (EAbsSig (Scoped (FoilPatternAsc x (Term argType)) bbody)) (Term (TArrow argType bodyType'))
        _ -> Left "cannot infer type of unannotated lambda"

    -- Type application
    ETAppSig body arg -> do
      at <- check arg (Term TType)
      let argType = toAST at
      bt <- infer body
      case typeOf bt of
        Term (TForAll (FoilPatternVar x) bodyType') -> do
          let subst = addSubst identitySubst x argType
          let actualType = substitute (nameMapToScope scope) subst bodyType'
          pure $ TypedNode (ETAppSig bt at) (Term actualType)
        _ -> Left "expected a polymorphic type"

    -- Type abstraction
    -- ΛX.λx.x  :  forall X. X -> X
    -- body = λx.x : X -> X
    ETAbsSig body -> do
      Scoped binder bbody <- scopedInfer (body (Just (Term TType)))
      case assertDistinct binder of
        Distinct ->
          let Term bodyType = typeOf bbody
          in pure $ TypedNode (ETAbsSig (Scoped binder bbody)) (Term (TForAll binder bodyType))

    -- Type constructors
    TBoolSig -> pure $ TypedNode TBoolSig (Term TType)
    TNatSig -> pure $ TypedNode TNatSig (Term TType)
    TUVarSig v -> pure $ TypedNode (TUVarSig v) (Term TType)
    TTypeSig -> pure $ TypedNode TTypeSig (Term TType)
    -- Type-level forall
    TForAllSig body -> do -- forall X. T
      Scoped _binder bbody <- scopedInfer (body (Just (Term TType)))
      -- TODO: check that bodyType is just Type
      pure $ TypedNode (TForAllSig (Scoped _binder bbody)) (Term TType)

    -- Arrow type
    TArrowSig l r -> do
      lt <- check l (Term TType)
      rt <- check r (Term TType)
      pure $ TypedNode (TArrowSig lt rt) (Term TType)

type Context n = NameMap n (Term n)

type Context' ty n = NameMap n (ty n)

--------------------------------------------------------------------------------

-- * Utility Functions

--------------------------------------------------------------------------------

-- | Unsink a type from a larger scope to a smaller one
unsinkType :: (Distinct l) => Context n -> Term l -> Either String (Term n)
unsinkType scope type_ = do
  case unsinkAST (nameMapToScope scope) (convertTermToAST type_) of
    Nothing -> Left "dependent types!"
    Just type'' -> return (Term type'')

-- | Convert Term to AST
convertTermToAST :: Term n -> AST (FoilPattern Term) TermSig n
convertTermToAST (Term ast) = ast

--------------------------------------------------------------------------------

-- * Typeclass Instances

--------------------------------------------------------------------------------

instance TypedPattern ty (FoilPattern ty) where
  extractPatternType (FoilPatternVar _) = Nothing
  extractPatternType (FoilPatternAsc _ ty) = Just ty
  extractTypedBinders (FoilPatternVar binder) ty =
    TypedNameBindersCons binder ty TypedNameBindersEmpty
  extractTypedBinders (FoilPatternAsc binder ty) _ =
    TypedNameBindersCons binder ty TypedNameBindersEmpty

deriving newtype instance AlphaEquiv Term
