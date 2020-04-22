{ pkgs ? <nixpkgs>, compiler ? null }:

# nixos 19-03

with import pkgs {};

let
  hsp = if compiler == null then haskellPackages else haskell.packages."${compiler}";
  hsPkgs0 = hsp.override {
    overrides = hself: hsuper:
      {
        semirings    = hself.callHackageDirect { pkg = "semirings"  ; ver = "0.5.3" ; sha256 = "0000000000000000000000000000000000000000000000000000"; } {};
      } // (if compiler == null then {} else {
        lens         = hself.callHackageDirect { pkg = "lens"       ; ver = "4.19.2"; sha256 = "0cgkigb7p0igzg9l669xkq787bb1cw32lx03pcgv5ivd6zsx3fpm"; } {};
        singletons   = hself.callHackageDirect { pkg = "singletons" ; ver = "2.7"   ; sha256 = "0ssbswl72fr3wx8br2c4snzi4qnic821wq57s042cjw61kzrrg5b"; } {};
        mkDerivation = if compiler == null then hsuper.mkDerivation else args: hsuper.mkDerivation (args // { doCheck = false; });
      });
  }; # haskellPackages override
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
    (if compiler == "ghc8101" then llvm_9 else llvm)
    # haskellPackages.ghcid
    # haskellPackages.hpack
    cabalghci
    # hsPkgs.nvim-hs-ghcid
    #haskell-ci
  ];
} # shellFor

