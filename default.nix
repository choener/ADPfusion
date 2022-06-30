{ mkDerivation, base, bits, containers, deepseq, DPutils, ghc-prim
, lib, mmorph, mtl, OrderedBits, primitive, PrimitiveArray
, QuickCheck, singletons, singletons-base, strict, tasty
, tasty-quickcheck, tasty-th, template-haskell, th-abstraction
, th-orphans, transformers, tuple, vector
}:
mkDerivation {
  pname = "ADPfusion";
  version = "0.6.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base bits containers deepseq DPutils ghc-prim mmorph mtl
    OrderedBits primitive PrimitiveArray QuickCheck singletons
    singletons-base strict template-haskell th-abstraction th-orphans
    transformers tuple vector
  ];
  testHaskellDepends = [
    base bits containers deepseq DPutils ghc-prim mmorph mtl
    OrderedBits primitive PrimitiveArray QuickCheck singletons
    singletons-base strict tasty tasty-quickcheck tasty-th
    template-haskell th-abstraction th-orphans transformers tuple
    vector
  ];
  homepage = "https://github.com/choener/ADPfusion";
  description = "Efficient, high-level dynamic programming";
  license = lib.licenses.bsd3;
}
