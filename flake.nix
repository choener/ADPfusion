{
  description = ''
    Generic Haskell development flake
    This flake pins "nixpkgs" but not much more.
    Afterwards, the "real" nix shell with ghc 8.10.2 is called within a zsh shell.
  '';

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-20.09";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = nixpkgs.legacyPackages.${system}; in
        {
          devShell = pkgs.mkShell {
            "NIX_PATH" = "nixpkgs=${nixpkgs}";
            #shellHook = ''
            #  nix-shell --argstr compiler ghc8102 --run zsh
            #'';
          };
          # NOTE unfortunately, this requires that all dependencies are known to the flake, which is
          # not working out for this type of development, since I "share" in-progress repositories
          # between multiple projects.
          #devShell = import ./shell.nix { inherit pkgs; };
        }
      );
}

