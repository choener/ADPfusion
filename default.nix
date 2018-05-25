with (import <nixpkgs> {});
with haskell.lib;

rec {
  hsPkgs = haskellPackages.extend (packageSourceOverrides {
    DPutils = ../Lib-DPutils;
    OrderedBits = ../Lib-OrderedBits;
    PrimitiveArray = ../Lib-PrimitiveArray;
    ADPfusion = ./.;
  });
  hsShell = with hsPkgs; shellFor {
    packages = p: [ p.ADPfusion ];
    withHoogle = true;
    buildInputs = [
      cabal-install ghc
      OrderedBits DPutils PrimitiveArray
    ];
  };
}
