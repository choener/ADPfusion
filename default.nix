with (import <nixpkgs> {});
with haskell.lib;

rec {
  hsSrcSet = (lib.foldl' (s: p: s // (import p).hsSrcSet) {} [
    ../Lib-DPutils
    ../Lib-OrderedBits
    ../Lib-PrimitiveArray
  ]) // {ADPfusion = ./.;};
  hsPkgs = haskellPackages.extend (packageSourceOverrides hsSrcSet);
  hsShell = with hsPkgs; shellFor {
    packages = p: [ p.ADPfusion ];
    withHoogle = true;
    buildInputs = [
      cabal-install ghc llvm_39
      DPutils
      OrderedBits
      PrimitiveArray
    ];
  };
}
