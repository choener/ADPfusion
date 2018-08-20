{ pkgs ? <nixpkgs> }:
with (import pkgs {});
with haskell.lib;
with builtins;

let
  # check directories below this one
  parentContent = readDir ./..;
  # extract sibling folders that contain a default.nix file
  parentDirs = filter (d: pathExists (./.. + ("/" + d + "/default.nix"))) (attrNames parentContent);
  # construct set of names / source directories for override
  hsSrcSet = listToAttrs (map (d: {name = "${d}"; value = ./.. + ("/" + d);}) parentDirs);
  # extend the set of packages with source overrides
  hsPkgs = haskellPackages.extend (packageSourceOverrides hsSrcSet);
  # name of this module
  this = baseNameOf ./.;
  traceds = x: y: builtins.trace (builtins.deepSeq x x) y;
in

{
  hsShell = with hsPkgs; shellFor {
    packages = p: let v = p.vector;
                  in  [ p."${this}" ]; # traceds (p."${this}".buildInputs) [ ];
    withHoogle = true;
    buildInputs = [
      cabal-install
    ];
  };
  # nix-build -A hsBuild
  # this shall build and put into ./result
  # the result is a typical ./bin/; ./lib/ etc.
  hsBuild = with hsPkgs; callCabal2nix "${this}" ./. {};
}
