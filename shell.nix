{ pkgs ? import <nixpkgs> {}, compiler ? null }:

# nixos 19-03

with pkgs;

let
  hsp = if compiler==null then haskellPackages else haskell.packages."${compiler}";
  hsPkgs0 = hsp.override {
    overrides = hself: hsuper:
      let compilerspecific = {
            "ghc8102" = { lens = hself.lens_4_19_2;
                          singletons = hself.singletons_2_7;
                        };
          };
      in
      {
        fused-effects = hself.fused-effects_1_1_0_0;
      } // compilerspecific.compiler or {};
  };
  #
  hsPkgs = hsPkgs0.extend (haskell.lib.packageSourceOverrides {
        ADPfusion = ./.;
        #
        PrimitiveArray =  ./deps/PrimitiveArray;
        #
        DPutils =  ./deps/DPutils;
        OrderedBits =  ./deps/OrderedBits;
        #
  }); # extend
  # my own little tool
  cabalghcisrc =
    let local = ~/Documents/University/active/ghcicabal;
    in  if builtins.pathExists local
        then local
        else builtins.fetchGit {
          url = https://github.com/choener/ghcicabal;
          ref = "master";
        };
  cabalghci = hsPkgs.callPackage cabalghcisrc {};
in

hsPkgs.shellFor {
  packages = p: [
    p.ADPfusion
    p.DPutils
    p.OrderedBits
    p.PrimitiveArray
                ];
  withHoogle = true;
  buildInputs = [
    cabal-install
    (if compiler==null then llvm_9 else { "ghc8102" = llvm_9; }.${compiler} or llvm)
    # haskellPackages.ghcid
    # haskellPackages.hpack
    cabalghci
    # hsPkgs.nvim-hs-ghcid
  ];
} # shellFor

