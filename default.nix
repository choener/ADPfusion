with import <nixpkgs> {};
haskellPackages.extend (haskell.lib.packageSourceOverrides {
  DPutils = ../Lib-DPutils;
  OrderedBits = ../Lib-OrderedBits;
  PrimitiveArray = ../Lib-PrimitiveArray;
#  doctest = "0.12.0";
})

