{ compilerVersion ? "ghc822" }:

with builtins;
with (import <nixpkgs> {});
with haskell.lib;

rec {
  handle = f: if isFunction f
              then (f { compilerVersion = compilerVersion; }).hsSrcSet
              else f.hsSrcSet;
  hsSrcSet = (lib.foldl' (s: p: s // handle (import p)) {} [
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
