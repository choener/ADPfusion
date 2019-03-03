{ mkDerivation, base, bits, containers, deepseq, DPutils, fmlist
, ghc-prim, mmorph, mtl, OrderedBits, primitive, PrimitiveArray
, QuickCheck, singletons, stdenv, strict, tasty, tasty-quickcheck
, tasty-th, template-haskell, th-orphans, transformers, tuple
, vector
}:
mkDerivation {
  pname = "ADPfusion";
  version = "0.6.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base bits containers deepseq DPutils ghc-prim mmorph mtl
    OrderedBits primitive PrimitiveArray QuickCheck singletons strict
    template-haskell th-orphans transformers tuple vector
  ];
  testHaskellDepends = [
    base bits OrderedBits PrimitiveArray QuickCheck strict tasty
    tasty-quickcheck tasty-th vector
  ];
  benchmarkHaskellDepends = [
    base fmlist PrimitiveArray template-haskell vector
  ];
  homepage = "https://github.com/choener/ADPfusion";
  description = "Efficient, high-level dynamic programming";
  license = stdenv.lib.licenses.bsd3;
}
