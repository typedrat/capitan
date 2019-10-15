module Data.Typeclass.Reified.Internal (Reifiable(..), thReifiable) where

import           Control.Monad
import           Data.Char
import           Data.Functor.Foldable
import           Data.Functor.Foldable.TH
import           Data.Foldable
import           Data.Kind
import           Data.Maybe
import           Encoding                   ( zEncodeString )
import           Language.Haskell.TH.Syntax hiding ( Type )
import qualified Language.Haskell.TH.Syntax as TH

import           Data.Capabilities

--

makeBaseFunctor ''TH.Type

--

class Reifiable (c :: k -> Constraint) where
    data family Reified c :: k -> Type
    reifyInstance :: (c a) => Reified c a

--

methodPrefix :: Name -> String
methodPrefix name = toLower n : ns
    where
        (n:ns) = nameBase name

getClassD :: Name -> Q Dec
getClassD name = reify name >>= \case
    ClassI dec@(ClassD _ _ _ _ _) _ -> return dec
    _                               -> fail "Only typeclasses can currently be reified."

mkInstanceHead :: Name -> [TyVarBndr] -> (TH.Type, TH.Type)
mkInstanceHead clsName tvs = (foldl' AppT (ConT clsName) instTvs, finalTv)
    where
        tvbToTy (PlainTV name)       = VarT name
        tvbToTy (KindedTV name kind) = SigT (VarT name) kind
        
        tys = fmap tvbToTy tvs
        instTvs = init tys
        finalTv = last tys

mkDataInst :: Name -> TH.Type -> TH.Type -> [(Name, Name, TH.Type)] -> (Name, Dec)
mkDataInst clsName instHead finalTv fields = (conName, DataInstD [] Nothing instTy Nothing [con] [])
    where
        instTy = AppT (AppT (ConT ''Reified) instHead) finalTv
        conName = mkName $ nameBase clsName ++ "C"
        toVarBangType (_, name, ty) = (name, Bang NoSourceUnpackedness SourceStrict, ty)
        con = RecC conName (fmap toVarBangType fields)

mkDataFields :: Name -> [Dec] -> [(Name, Name, TH.Type)]
mkDataFields clsName decs = mapMaybe go decs
    where
        prefix = methodPrefix clsName

        go (SigD oldName ty) = Just (oldName, mkName $ prefix ++ '_' : name', ty)
            where
                name@(n:_) = nameBase oldName
                name'
                    | isAlpha n = name
                    | otherwise = zEncodeString name
        go _              = Nothing

mkReifyFn :: Name -> [Dec] -> Dec
mkReifyFn conName decs = FunD 'reifyInstance [Clause [] (NormalB dict) []]
    where
        methods = mapMaybe go decs
        dict = foldl' AppE (ConE conName) methods

        go (SigD name _) = Just (VarE name)
        go _             = Nothing

mkReifiableInst :: Name -> [TyVarBndr] -> [Dec] -> Dec
mkReifiableInst clsName tvs decs = InstanceD Nothing [] instTy [dataInst, reifyFn]
    where
        (instHead, finalTv) = mkInstanceHead clsName tvs
        (conName, dataInst) = mkDataInst clsName instHead finalTv dictFields
        dictFields = mkDataFields clsName decs
        reifyFn = mkReifyFn conName decs
        instTy = AppT (ConT ''Reifiable) instHead

--

isLiftableKind :: [TyVarBndr] -> Bool
isLiftableKind [KindedTV _ ty] = cata countArrows ty == 1
    where
        countArrows (ForallTF _ _ n) = n
        countArrows (AppTF l r)      = l + r
        countArrows (SigTF ty sig)   = ty
        countArrows ArrowTF          = 1
        countArrows _                = 0
        
isLiftableKind (x:xs) = isLiftableKind xs
isLiftableKind []     = False

substituteTy :: TH.Type -> TH.Type -> TH.Type -> TH.Type
substituteTy oldTy newTy = cata (update . embed)
    where
        update x
            | x == oldTy = newTy
            | otherwise  = x

mkLiftedFn :: TH.Type -> TH.Type -> (Name, Name, TH.Type) -> Q Dec
mkLiftedFn oldTy newTy (name, field, ty) = do
        capN <- newName "c"
        (pats, bodyArgs) <- topLevel capN ty
        let meth = AppE (VarE field) (AppE (VarE 'getCapability) (VarE capN))
            bodyE = AppE (ConE 'Cap) (LamE [VarP capN] (foldl' AppE meth bodyArgs))
            body = NormalB bodyE 

        return (FunD name [Clause pats body []])
    where
        topLevel :: Name -> TH.Type -> Q ([Pat], [Exp])
        topLevel capN (ForallT _ _ ty) = topLevel capN ty
        topLevel capN (AppT (AppT ArrowT lhs) rhs) = (<>) <$> go capN lhs <*> topLevel capN rhs
        topLevel capN (AppT lhs _) | lhs == oldTy = pure mempty
        topLevel capN ty = error ("Unexpected weird type: " ++ show ty)

        go :: Name -> TH.Type -> Q ([Pat], [Exp])
        go capN ty = case substituteTy oldTy newTy ty of
            AppT lhs _ | lhs == newTy -> do
                varN <- newName "x"
                return ([ConP 'Cap [VarP varN]], [AppE (VarE varN) (VarE capN)])
            AppT (AppT ArrowT _) (AppT con _) | con == newTy -> do
                varN <- newName "g"
                let app = AppE (VarE 'apply) (VarE capN)
                    run = VarE 'runCap
                    fn = VarE varN
                    comp = VarE '(.)
                return ([VarP varN], [InfixE (Just app) comp (Just $ InfixE (Just run) comp (Just fn))])
            AppT (AppT ArrowT _) _ -> do
                varN <- newName "f"
                return ([VarP varN], [VarE varN])
            _ -> do
                varN <- newName "y"
                return ([VarP varN], [VarE varN])

mkLiftInst :: [TH.Type] -> Name -> [TyVarBndr] -> [Dec] -> Q (Maybe Dec)
mkLiftInst ctx clsName tvs decs 
    | isLiftableKind tvs = do
        instDecs <- mapM (mkLiftedFn oldTy capT) fields
        pure (Just (InstanceD Nothing (hasCap:ctx') instTy instDecs))
    | otherwise          = pure Nothing
    where
        (instHead, finalTv) = mkInstanceHead clsName tvs
        fields              = mkDataFields clsName decs

        stripSig (SigT ty _) = ty
        stripSig ty          = ty

        oldTy = stripSig finalTv

        ctx' = substituteTy oldTy capT <$> ctx

        capVarT = VarT $ mkName "caps"
        capT = AppT (ConT ''Cap) capVarT
        hasCap = AppT (AppT (ConT ''HasCapability) (AppT (ConT ''Reified) instHead)) capVarT
        instTy = AppT instHead capT

--

thReifiable :: Name -> Q [Dec]
thReifiable name = do
    ClassD ctx clsName tvs _ decs <- getClassD name

    when (null tvs) .
        fail $ "I don't know how to derive Reifiable for a nullary typeclass: " ++ show clsName

    let reifiableInst = mkReifiableInst clsName tvs decs
    liftInst <- mkLiftInst ctx clsName tvs decs
    
    return (reifiableInst : maybeToList liftInst)
