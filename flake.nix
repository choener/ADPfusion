{
  description = ''
    ADPfusion allows writing highly efficient, high-level dynamic programming code in Haskell.
  '';

  inputs = {
    # NOTE Only update if we are sure that all packages can build with nixos>20.09.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
    flake-utils.url = "github:numtide/flake-utils";
    ghcicabal = { url = "github:choener/ghcicabal"; inputs.nixpkgs.follows = "nixpkgs"; };
    DPutils-src = {
      url = "github:choener/DPutils";
      flake = false;
    };
    OrderedBits-src = {
      url = "github:choener/OrderedBits";
      flake = false;
    };
    PrimitiveArray-src = {
      url = "github:choener/PrimitiveArray";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, ghcicabal
    , DPutils-src
    , OrderedBits-src
    , PrimitiveArray-src
  }: let
    overlay = final: prev: {
      #haskellPackages = (prev.haskell.packages.ghc8102.override{ overrides= hself: hsuper: let
      haskellPackages = (prev.haskellPackages.override{ overrides= hself: hsuper: let
          checked   = a: hself.callHackageDirect a {};
          unchecked = a: final.haskell.lib.dontCheck (checked a);
          unb       = a: final.haskell.lib.dontCheck (final.haskell.lib.unmarkBroken a);
        in {
        };
      }).extend ( hself: hsuper: {
        ADPfusion = hself.callPackage ./. {};
        #
        DPutils = hself.callPackage DPutils-src {};
        OrderedBits = hself.callPackage OrderedBits-src {};
        PrimitiveArray = hself.callPackage PrimitiveArray-src {};
        #
        #adp = with final.haskell.lib;  (dontCheck (enableCabalFlag hself.ADPfusion "enablenw"));
        adp = with final.haskell.lib.compose; final.lib.pipe hself.ADPfusion [
          dontCheck
          (enableCabalFlag "examplenw")
        ];
      });
    };
  in
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs { inherit system; overlays = [ ghcicabal.overlay self.overlay ]; };
      sharedBuildInputs = with pkgs; [ llvm_9 ];
    in {
      # update dependencies via mr, develop the package, push changes, and update the flake
      # dependencies if major changes were made or before releasing
      devShell = pkgs.haskellPackages.shellFor {
        packages = p: [
          p.ADPfusion
          #
          p.DPutils
          p.OrderedBits
          p.PrimitiveArray
        ];
        withHoogle = true;
        buildInputs = with pkgs; [
          cabal-install
          pkgs.ghcicabal # be explicit to get the final package
          haskellPackages.haskell-language-server
          haskellPackages.hls-tactics-plugin
          nodejs # required for lsp
        ] ++ sharedBuildInputs;
      }; # devShell

      apps = let
        C = pkgs.stdenv.mkDerivation {
          name = "C";
          src = [ ./C/nw.c ];
          buildInputs = [];
          unpackPhase = ":";
          buildPhase = ''
            ${pkgs.gcc}/bin/gcc -O3 -o C $src
          '';
          installPhase = ''
            mkdir -p $out/bin
            cp C $out/bin
          '';
        };
      in {
        C = { type = "app"; program = "${C}/bin/C"; };
        NW = { type = "app"; program = "${pkgs.haskellPackages.adp}/bin/NeedlemanWunsch"; };
      };
    }) // { inherit overlay; };
}

